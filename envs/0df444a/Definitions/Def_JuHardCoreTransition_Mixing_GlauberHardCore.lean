-- Prove2me | Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore
-- name    : JuHardCoreTransition_Mixing_GlauberHardCore
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:34.317285+00:00
-- url     : https://prove2.me/theorems/ae0db605-3e65-4329-b4df-a6e4397ce495
-- title:
--   Hard-core law, single-site Glauber dynamics, $t_{\mathrm{mix}}$, $t_{\mathrm{rel}}$, worst-case mixing, field-dynamics spectral stability
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $\lambda>0$. The **hard-core law** is $\mu_{G,\lambda}(I)=\lambda^{|I|}/Z_G(\lambda)$ on the independent sets $I\in\mathcal I(G)$ (empty set included), $Z_G(\lambda)=\sum_{I\in\mathcal I(G)}\lambda^{|I|}$; $\lambda_c(d)=(d-1)^{d-1}/(d-2)^d$.
--
--   **Glauber dynamics.** Each step picks a vertex uniformly at random; if a neighbour is occupied it is (kept) vacant, otherwise it becomes occupied with probability $\lambda/(1+\lambda)$ and vacant otherwise. One time unit is one single-vertex update. For $0<\eta<1$,
--   $$t_{\mathrm{mix}}(\eta)=\min\Big\{t\ge0:\max_{x}d_{TV}\big(P^t(x,\cdot),\mu_{G,\lambda}\big)\le\eta\Big\},\qquad d_{TV}(\nu,\pi)=\tfrac12\sum_x|\nu(x)-\pi(x)|,$$
--   and $t_{\mathrm{rel}}=1/(1-\theta_2)$ with $\theta_2$ the largest eigenvalue on functions orthogonal to constants (the kernel is reversible and positive semidefinite). $\max_G t^G_{\mathrm{mix}}(1/4)$ ranges over all simple graphs on $n$ labelled vertices with maximum degree exactly $d$.
--
--   **Positive pinnings and Definition 4.1.** A positive pinning fixes an independent set $S$ occupied; the free coordinates are $V\setminus N_G[S]$. $\mu_{G,\lambda}$ satisfies **field-dynamics spectral stability** with rate $\mathcal C:(0,\lambda]\to[0,\infty)$ if for every $0<a\le\lambda$ and every positive pinning of $\mu_{G,a}$ the residual configuration satisfies $\mathrm{Cov}(X)\preceq\mathcal C(a)\operatorname{diag}(p_v)$, $p_v=\mathbb E X_v$, on the free coordinates. The **stability integral** is $I=\int_0^\lambda(\mathcal C(a)-1)/a\,da$. The **occupied-marginal condition** with parameter $b$ asks $\mu_{G,\lambda}(X_v=1\mid X_w=1\ \forall w\in S)\ge b$ for every independent $S$ and $v\notin N_G[S]$; $\mu_{\min}=\min_{J\in\mathcal I(G)}\mu_{G,\lambda}(J)$.
--
--   **Lemma 4.3 / Proposition 4.4 objects.** For $0<a<\lambda_c(d)$, $\theta_d(a)\in(0,1/(d-1))$ solves $a=\theta/(1-\theta)^d$. The rate (4.5) is $\min\{K(1+\sqrt{n/d}),[1-(d-1)\theta_d(a)]^{-1}\}$ for $0<a<\lambda_c$ and $K(1+\sqrt{n/d}+(n/d)(a/\lambda_c-1))$ for $a\ge\lambda_c$. Constants $\delta_{\mathrm{up}}=2^{-18}$, $h_0=2^{-27}$.
--
--   **Formalization Note.** Everything is built from the published `HiddenHardCoreColoring.Mixing` modules at the constant activity `fun _ => λ`: `hcLaw`, the heat-bath kernel `hcP` (no extra laziness), `tmix` (natural-number infimum; it is the minimum because the chain mixes), `gap` ($1-\lambda_2$ with multiplicity) so `trelG = 1/gap`, `muMin`, `lamCrit`. `hcSetLaw` is $\mu_{G,\lambda}$ as a Boolean law (zero off $\mathcal I(G)$). `worstTmix d n λ` is a `Finset.sup` over all `SimpleGraph (Fin n)` with `maxDegree = d` (value $0$ when the class is empty, i.e. $n\le d$, never used). `IsStabilityRate` explicitly requires a nonnegative rate on $(0,\lambda]$ and sums over `freeAfterPin G S` $=V\setminus N_G[S]$. `stabIntegral C λ` is the Lebesgue integral $\int^-_{(0,\lambda]}\mathrm{ofReal}((\mathcal C(a)-1)/a)$ in $[0,\infty]$, equal to the improper integral for the nonnegative integrands used; `thetaD` is the unique root (value $0$ when none exists); `rateProp44 K n d` is (4.5).
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), §1, §2.1, §3.1, Definition 4.1, Lemma 4.2, Lemma 4.3, Proposition 4.4, printed pp.1–19 / PDF pp.2–20

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Chain
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-!
# The hard-core law, its single-site Glauber dynamics, mixing and relaxation times,
# and field-dynamics spectral stability

Ju, Liu and Yin, *Fine-Grained Complexity Across the Computational Phase Transition*,
arXiv:2611.02702, pinned source.pdf dated 2026-11-02 (SHA256 6288a2d2…3678; arXiv version suffix
not supplied): §1 (printed pp.1–3 / PDF pp.2–4), §2.1 (printed pp.8–10 / PDF pp.9–11), §3 and §3.1
(printed pp.16–17 / PDF pp.17–18), §4.1 (printed pp.18–19 / PDF pp.19–20).

All objects are built from the published hard-core and chain vocabulary
(`HiddenHardCoreColoring.Mixing`) at the **constant** activity `λ` at every vertex:
`hcLaw G (fun _ => λ)` is `μ_{G,λ}(I) = λ^{|I|}/Z_G(λ)` on the independent sets `I(G)`,
`hcP G (fun _ => λ)` is the heat-bath Glauber kernel (one uniformly chosen vertex per step, no
extra laziness), `tmix` is the worst-start mixing time and `gap` the spectral gap `1 − θ₂`,
`lamCrit d = (d−1)^{d−1}/(d−2)^d` the uniqueness threshold.

* `hcSetLaw G λ` is `μ_{G,λ}` as a Boolean law on `{0,1}^V` (value `0` off `I(G)`).
* `tmixG`, `trelG` are `t_mix(η)` and `t_rel = 1/gap` of the Glauber dynamics; `worstTmix d n λ` is
  `max_G t_mix^G(1/4)` over all simple graphs on `Fin n` of maximum degree exactly `d`.
* `posPinLaw G a S` is `μ_{G,a}` conditioned on `X_w = 1` for all `w ∈ S` (a positive pinning),
  `freeAfterPin G S = V ∖ N_G[S]` its free coordinates; `IsStabilityRate G λ C` is
  Definition 4.1; `stabIntegral C λ = ∫_0^λ (C(a) − 1)/a da` (Lebesgue integral of the nonnegative
  integrand on `(0, λ]`, in `[0, ∞]`).
* `thetaD d a` is the root `θ_d(a) ∈ (0, 1/(d−1))` of `a = θ/(1 − θ)^d` (Lemma 4.3), and
  `rateProp44 K n d a` the piecewise rate (4.5) of Proposition 4.4.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `δ_up = 2^{−18}` (§2, printed p.7; Theorem 1.3, p.2). -/
noncomputable def deltaUp : ℝ := 1 / 2 ^ 18

/-- `h_0 = 2^{−27}` (Lemma 2.2, p.9). -/
noncomputable def hZero : ℝ := 1 / 2 ^ 27

/-- The independent sets of `G` are the `Finset`s with no edge inside. -/
def IsIndep (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w

/-- The hard-core law `μ_{G,λ}(I) = λ^{|I|}/Z_G(λ)` at constant activity `λ`, as a Boolean law
on `{0,1}^V` (configurations = occupied sets); `0` off the independent sets. Built from the
published `hcLaw`. -/
noncomputable def hcSetLaw (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : Finset V) : ℝ := by
  classical
  exact if h : IsIndep G I then hcLaw G (fun _ => lam) ⟨I, h⟩ else 0

/-- The mixing time `t_mix(η)` of the single-site heat-bath Glauber dynamics for `μ_{G,λ}`
(§3.1, p.17): the least `t` with `max_x d_TV(P^t(x,·), μ) ≤ η`; one step is one single-vertex
update. -/
noncomputable def tmixG (G : SimpleGraph V) [DecidableRel G.Adj] (lam η : ℝ) : ℕ :=
  tmix (hcP G (fun _ => lam)) (hcLaw G (fun _ => lam)) η

/-- The relaxation time `t_rel = 1/gap(P) = 1/(1 − θ₂)` of the Glauber dynamics for `μ_{G,λ}`
(§3.1, p.17). The kernel is reversible and positive semidefinite, so `θ₂` is the largest
eigenvalue on functions orthogonal to constants. -/
noncomputable def trelG (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) : ℝ :=
  1 / gap (hcP G (fun _ => lam))

/-- `max_G t_mix^G(1/4)`, the maximum over **all** simple graphs `G` on the vertex set `Fin n`
with maximum degree exactly `d` (Theorem 1.4, p.3), at fugacity `λ`. -/
noncomputable def worstTmix (d n : ℕ) (lam : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun G : SimpleGraph (Fin n) => G.maxDegree = d).sup
    fun G => tmixG G lam (1 / 4)

/-- The positive pinning that fixes every vertex of `S` occupied and leaves the others free. -/
def posPinning (S : Finset V) : Pinning V := fun v => if v ∈ S then some true else none

/-- `μ_{G,a}` conditioned on `X_w = 1` for every `w ∈ S` (a positive pinning, §4.1, p.18). -/
noncomputable def posPinLaw (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (S : Finset V) :
    Finset V → ℝ :=
  condition (hcSetLaw G a) (posPinning S)

/-- The free coordinates after the positive pinning of `S`: `V ∖ N_G[S]` (§2.1, p.8). -/
noncomputable def freeAfterPin (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ S ∧ ∀ w ∈ S, ¬ G.Adj v w

/-- **Field-dynamics spectral stability** (Definition 4.1, p.18): the rate is nonnegative on
`(0, λ]`, and for every `0 < a ≤ λ` and every
positive pinning of `μ_{G,a}` (an independent set `S` fixed occupied), the residual configuration
satisfies `Cov(X) ⪯ C(a) diag(p_v)`, `p_v = E X_v`, on the free coordinates `V ∖ N_G[S]` (vacuous
for an empty residual). -/
def IsStabilityRate (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (C : ℝ → ℝ) : Prop :=
  (∀ a ∈ Set.Ioc (0 : ℝ) lam, 0 ≤ C a) ∧
  ∀ a : ℝ, 0 < a → a ≤ lam → ∀ S : Finset V, IsIndep G S → ∀ z : V → ℝ,
    (∑ u ∈ freeAfterPin G S, ∑ v ∈ freeAfterPin G S,
        z u * z v * cov (posPinLaw G a S) u v) ≤
      C a * ∑ v ∈ freeAfterPin G S, marg (posPinLaw G a S) v * z v ^ 2

/-- The stability integral `I = ∫_0^λ (C(a) − 1)/a da` (Lemma 4.2, Proposition 4.4), as the
Lebesgue integral over `(0, λ]` of the (nonnegative, for `C ≥ 1`) integrand, valued in `[0, ∞]`;
for a nonnegative integrand it equals the improper integral, and `I < ∞` is `≠ ⊤`. -/
noncomputable def stabIntegral (C : ℝ → ℝ) (lam : ℝ) : ENNReal :=
  ∫⁻ a in Set.Ioc 0 lam, ENNReal.ofReal ((C a - 1) / a)

/-- `θ_d(a)`, the unique `θ ∈ (0, 1/(d−1))` with `a = θ/(1 − θ)^d` (Lemma 4.3, p.19); its
existence and uniqueness for `0 < a < λ_c(d)` are part of Lemma 4.3. Value `0` where no unique root
exists. -/
noncomputable def thetaD (d : ℕ) (a : ℝ) : ℝ := by
  classical
  exact if h : ∃! θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (1 / ((d : ℝ) - 1)) ∧ a = θ / (1 - θ) ^ d
    then h.exists.choose else 0

/-- The piecewise rate (4.5) of Proposition 4.4 (p.19), with absolute constant `K`:
`min{K(1 + √(n/d)), [1 − (d−1)θ_d(a)]^{−1}}` for `0 < a < λ_c`, and
`K(1 + √(n/d) + (n/d)(a/λ_c − 1))` for `a ≥ λ_c`. -/
noncomputable def rateProp44 (K : ℝ) (n d : ℕ) (a : ℝ) : ℝ :=
  if a < lamCrit d then
    min (K * (1 + Real.sqrt ((n : ℝ) / d))) (1 / (1 - ((d : ℝ) - 1) * thetaD d a))
  else K * (1 + Real.sqrt ((n : ℝ) / d) + ((n : ℝ) / d) * (a / lamCrit d - 1))

/-- `μ_min = min_{J ∈ I(G)} μ_{G,λ}(J)` (Lemma 4.2, p.18), via the published `muMin`. -/
noncomputable def muMinG (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) : ℝ :=
  muMin (hcLaw G (fun _ => lam))

/-- The occupied-marginal lower-bound condition under positive pinning with parameter `b`
(Lemma 4.2, p.18): `μ_{G,λ}(X_v = 1 | X_w = 1 ∀ w ∈ S) ≥ b` for every independent `S` and every
`v ∉ N_G[S]`. -/
def OccupiedMarginalLB (G : SimpleGraph V) [DecidableRel G.Adj] (lam b : ℝ) : Prop :=
  ∀ S : Finset V, IsIndep G S → ∀ v, v ∉ S → (∀ w ∈ S, ¬ G.Adj v w) →
    b ≤ marg (posPinLaw G lam S) v

end JuHardCoreTransition.Mixing


