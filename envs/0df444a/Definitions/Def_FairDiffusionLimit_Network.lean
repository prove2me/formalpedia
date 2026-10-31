-- Prove2me | Definitions.Def_FairDiffusionLimit_Network
-- name    : FairDiffusionLimit_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:37.051654+00:00
-- url     : https://prove2.me/theorems/6d625569-23bc-4074-8e8e-e7c9da542b4c
-- title:
--   The sequence of resource-sharing networks: $A$, $c$, $\beta$, PF allocation $\Lambda(n)$, $B$, $G$, $\mathcal W$, $H$, $\Upsilon$ and the standing assumptions (10)–(15)
-- statement:
--   This module sets up the sequence of resource-sharing networks of Ye and Yao (§2, pp. 8–13).
--
--   There are $L$ links and $R$ routes (job classes). $A=[a_{\ell r}]$ is a nonnegative $L\times R$ matrix of full row rank $L$, $c=(c_\ell)$ are the link capacities and $\beta_r>0$ the proportional-fair weights. In state $n$ (number of jobs per class) the capacity allocation $\Lambda(n)$ maximizes
--   $$\sum_{r}\beta_r n_r\log\gamma_r\quad\text{over}\quad \Gamma=\{\gamma: A\gamma\le c,\ \gamma\ge 0\},$$
--   with $\Lambda_r(n)=0$ when $n_r=0$ (the published PF allocation `psi`, with $\log 0=-\infty$).
--
--   Network $k$ has arrival rates $\lambda^k_r$ and mean work requirements $\nu^k_r$, with limits $\lambda_r,\nu_r>0$ and $k(\lambda^k_r\nu^k_r-\lambda_r\nu_r)\to\theta_r$ (10). All networks are driven by the same primitives (12): $u^k_r(i)=(\lambda^1_r/\lambda^k_r)u^1_r(i)$ and $v^k_r(i)=(\nu^k_r/\nu^1_r)v^1_r(i)$ for $i\ge 2$, where the $u^1_r(i)$, $v^1_r(i)$ are independent with laws $F^a_r$, $F^s_r$ on $[0,\infty)$, means $1/\lambda^1_r$ and $\nu^1_r$, and finite $p$-th moments, $p>2$ (13). The standing assumptions also contain (14) and (15).
--
--   The module defines $\rho_r=\lambda_r\nu_r$, $\rho^k_r=\lambda^k_r\nu^k_r$, $B=\operatorname{diag}(\rho_r\nu_r/\beta_r)$, $G=A^T(ABA^T)^{-1}$ (18), the fixed-point state space $\mathcal W=\{BA^T\pi:\pi\ge0\}$ (16), the condition (17) on $H$ ($ABH=0$, $H^TBH=I$), the covariance $\Upsilon=\operatorname{diag}(\sigma_r^2)$ of (33), the heavy-traffic condition $A\rho=c$ (11) and the usual traffic condition $A\theta<0$ (66). The norm $|x|=\sum_i|x_i|$ is the $\ell^1$ norm.
--
--   **Formalization Note** Networks are indexed by $k\in\mathbb N$, with a dummy network $0$ of which only $\lambda^0,\nu^0>0$ is asked. Every route is required to use some link ($a_{\ell r}>0$ for some $\ell$); otherwise (3) has no solution. Condition (15) is stated with a measurable density $p$ and the law of the sum of $j-1$ i.i.d. copies.
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), §2, pp.8–13: (1)–(3), (10)–(18), (33), p.19 (66)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization

open MeasureTheory Filter Topology Matrix

namespace FairDiffusionLimit

/-- The `ℓ¹` norm `|x| = ∑ᵢ |xᵢ|` of a real vector (Ye–Yao, SSRN 2579541 (2015), used throughout;
p. 43: "the absolute value of the sum of w's components", which is `∑ᵢ |xᵢ|` on the nonnegative
vectors where it is applied).

**Formalization Note.** Mathlib's default norm on `ι → ℝ` is the sup norm; every `|·|` of the paper
is this `ℓ¹` norm instead. -/
noncomputable def l1 {ι : Type} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, |x i|

/-- A state `x = (w, u, v)` of the Markov process `Ξ = (W, U, V)` (p. 10): the workload vector `w`,
the residual interarrival times `u` and the residual work requirements `v`, each in `ℝ^R`. The
paper's state space is `𝒳 = ℝ₊^{3R}`. -/
abbrev State (R : ℕ) : Type := (Fin R → ℝ) × (Fin R → ℝ) × (Fin R → ℝ)

/-- The norm `|x| = |w| + |u| + |v|` of a state `x = (w, u, v) ∈ ℝ^{3R}` (the `ℓ¹` norm on
`ℝ^{3R}`). -/
noncomputable def stNorm {R : ℕ} (x : State R) : ℝ := l1 x.1 + l1 x.2.1 + l1 x.2.2

/-- **The sequence of resource-sharing networks** of Ye–Yao, *Diffusion limit of fair resource
control — stationarity and interchange of limits*, SSRN 2579541 (2015), §2, pp. 8–11.

* `A` is the `L × R` link–route matrix `[a_ℓr]`, `c` the link capacities, `β` the PF weights (p. 8–9);
  they are shared by every network of the sequence.
* `Fa r`, `Fs r` are the laws of the base primitives `u¹_r(2)` and `v¹_r(2)` (the interarrival
  time and work requirement of network 1). Network `k` is driven by the same primitives, rescaled as
  in (12): `u^k_r(i) = (λ¹_r/λ^k_r) u¹_r(i)` and `v^k_r(i) = (ν^k_r/ν¹_r) v¹_r(i)`, `i ≥ 2`.
* `lam k r = λ^k_r`, `nu k r = ν^k_r` are the arrival rate and mean work of class `r` in network `k`;
  `lamLim r = λ_r`, `nuLim r = ν_r` are their limits in (10), and `θ` is the limit of
  `k(ρ^k − ρ)` in (10).
* `p > 2` is the moment exponent of (13).

**Formalization Note.** Networks are indexed by `k : ℕ`; the paper's networks are `k = 1, 2, …`.
Index `0` is a dummy network: it enters no statement except through limits `k → ∞` or quantifiers
`k ≥ k₀`, and the standing assumptions only ask `λ⁰, ν⁰ > 0` of it (any paper sequence extends by
`λ⁰ = λ¹`, `ν⁰ = ν¹`). -/
structure NetSeq (L R : ℕ) where
  /-- The link–route matrix `A = [a_ℓr]`. -/
  A : Matrix (Fin L) (Fin R) ℝ
  /-- The link capacities `c_ℓ`. -/
  c : Fin L → ℝ
  /-- The proportional-fair weights `β_r`. -/
  β : Fin R → ℝ
  /-- The law of `u¹_r(2)`. -/
  Fa : Fin R → Measure ℝ
  /-- The law of `v¹_r(2)`. -/
  Fs : Fin R → Measure ℝ
  /-- `λ^k_r`. -/
  lam : ℕ → Fin R → ℝ
  /-- `ν^k_r`. -/
  nu : ℕ → Fin R → ℝ
  /-- `λ_r = lim_k λ^k_r`. -/
  lamLim : Fin R → ℝ
  /-- `ν_r = lim_k ν^k_r`. -/
  nuLim : Fin R → ℝ
  /-- `θ_r = lim_k k(ρ^k_r − ρ_r)`. -/
  θ : Fin R → ℝ
  /-- The moment exponent `p > 2` of (13). -/
  p : ℝ

namespace NetSeq

variable {L R : ℕ} (S : NetSeq L R)

/-- The set of feasible allocations `Γ = {γ : Aγ ≤ c, γ ≥ 0}`, (2), p. 9. -/
def Gamma : Set (Fin R → ℝ) := {γ | S.A *ᵥ γ ≤ S.c ∧ 0 ≤ γ}

/-- The proportional-fair allocation `Λ(n)`, (3), p. 9: a maximizer of `∑_r β_r n_r log γ_r` over `Γ`,
with `Λ_r(n) = 0` when `n_r = 0`. It is the published `ProcessingNetworks.ProportionalFairness.psi`
with weights `z_r = β_r n_r`; its objective is `EReal`-valued with `log 0 = −∞`, and coordinates with
`z_r = 0` are set to `0`. The argument `n` is a real vector (job counts, or fluid-scaled counts). -/
noncomputable def Lam (n : Fin R → ℝ) : Fin R → ℝ :=
  ProcessingNetworks.ProportionalFairness.psi S.Gamma (fun r => S.β r * n r)

/-- The limiting traffic intensity `ρ_r = λ_r ν_r`, (1) with the limits of (10), p. 10. -/
def rho : Fin R → ℝ := fun r => S.lamLim r * S.nuLim r

/-- The traffic intensity `ρ^k_r = λ^k_r ν^k_r` of network `k`. -/
def rhoK (k : ℕ) : Fin R → ℝ := fun r => S.lam k r * S.nu k r

/-- `b_r = ρ_r ν_r / β_r`, p. 11. -/
noncomputable def bvec : Fin R → ℝ := fun r => S.rho r * S.nuLim r / S.β r

/-- `B = diag(b_r)`, p. 11. -/
noncomputable def B : Matrix (Fin R) (Fin R) ℝ := Matrix.diagonal S.bvec

/-- `G = Aᵀ(ABAᵀ)⁻¹`, (18), p. 12. (`ABAᵀ` is invertible under the standing assumptions: `A` has
full row rank and `B` is a positive diagonal matrix.) -/
noncomputable def G : Matrix (Fin R) (Fin L) ℝ := S.Aᵀ * (S.A * S.B * S.Aᵀ)⁻¹

/-- The fixed-point state space `𝒲 = {w = BAᵀπ : π ≥ 0}`, (16), p. 11. -/
def Wcone : Set (Fin R → ℝ) := {w | ∃ π : Fin L → ℝ, 0 ≤ π ∧ w = S.B *ᵥ (S.Aᵀ *ᵥ π)}

/-- `H` is an `R × (R − L)` matrix with `ABH = 0` and `HᵀBH = I`, (17), p. 11. Such an `H` is not
unique; every statement takes it as a parameter satisfying (17). -/
def IsH (H : Matrix (Fin R) (Fin (R - L)) ℝ) : Prop :=
  S.A * S.B * H = 0 ∧ Hᵀ * S.B * H = 1

/-- The law of `u^k_r(2) = (λ¹_r/λ^k_r) u¹_r(2)`, (12). -/
noncomputable def lawU (k : ℕ) (r : Fin R) : Measure ℝ :=
  (S.Fa r).map (fun x => S.lam 1 r / S.lam k r * x)

/-- The law of `v^k_r(2) = (ν^k_r/ν¹_r) v¹_r(2)`, (12). -/
noncomputable def lawV (k : ℕ) (r : Fin R) : Measure ℝ :=
  (S.Fs r).map (fun x => S.nu k r / S.nu 1 r * x)

/-- The joint law of the base primitive sequences `(u¹_r(i))_{r, i ≥ 2}` and `(v¹_r(i))_{r, i ≥ 2}`:
all independent, `u¹_r(i) ∼ F^a_r`, `v¹_r(i) ∼ F^s_r`. The index `(r, i)` of the product stands for
`(r, i + 2)`. -/
noncomputable def primLaw : Measure ((Fin R × ℕ → ℝ) × (Fin R × ℕ → ℝ)) :=
  (Measure.infinitePi fun q : Fin R × ℕ => S.Fa q.1).prod
    (Measure.infinitePi fun q : Fin R × ℕ => S.Fs q.1)

/-- `σ²_{a,r} = lim_k (σ^k_{a,r})²`, (10): the variance of `u^k_r(2) = (λ¹_r/λ^k_r)u¹_r(2)` is
`(λ¹_r/λ^k_r)² Var u¹_r(2)`, whose limit is `(λ¹_r/λ_r)² Var u¹_r(2)`. -/
noncomputable def sigmaA2 (r : Fin R) : ℝ :=
  (S.lam 1 r / S.lamLim r) ^ 2 * ∫ x, (x - 1 / S.lam 1 r) ^ 2 ∂(S.Fa r)

/-- `σ²_{s,r} = lim_k (σ^k_{s,r})² = (ν_r/ν¹_r)² Var v¹_r(2)`, (10) with (12). -/
noncomputable def sigmaS2 (r : Fin R) : ℝ :=
  (S.nuLim r / S.nu 1 r) ^ 2 * ∫ x, (x - S.nu 1 r) ^ 2 ∂(S.Fs r)

/-- The covariance matrix `Υ = diag(σ²_r)` of the free Brownian motion, (33), p. 13, with
`σ²_r = ν_r²(λ_r³σ²_{a,r} + ρ_r ν_r⁻³ σ²_{s,r})`. -/
noncomputable def Upsilon : Matrix (Fin R) (Fin R) ℝ :=
  Matrix.diagonal fun r =>
    S.nuLim r ^ 2 * (S.lamLim r ^ 3 * S.sigmaA2 r + S.rho r * (S.nuLim r)⁻¹ ^ 3 * S.sigmaS2 r)

/-- **The standing assumptions** of §2 (pp. 8–11) on the network sequence.

1. `A ≥ 0` has full row rank `L` (p. 8), and every route uses some link.
2. `β_r > 0` (p. 9).
3. `F^a_r`, `F^s_r` are probability laws on `[0, ∞)` with finite `p`-th moments, `p > 2`, (13); their
   means are `1/λ¹_r` and `ν¹_r` (so that, by (12), `u^k_r(i)` and `v^k_r(i)` have means `1/λ^k_r` and
   `ν^k_r`, p. 8).
4. `λ^k_r, ν^k_r > 0` and `λ_r, ν_r > 0` (p. 8).
5. The limits (10): `λ^k_r → λ_r`, `ν^k_r → ν_r`, `k(λ^k_rν^k_r − λ_rν_r) → θ_r`. (The convergence
   of `σ^k_{a,r}, σ^k_{s,r}` in (10) holds automatically under (12).)
6. (14): for every `k ≥ 1`, `r` and `a > 0`, `P{u^k_r(2) ≥ a} > 0`.
7. (15): for every `k ≥ 1` and `r` there are an integer `j ≥ 2` and a nonnegative measurable function
   `p(x)` with `∫₀^∞ p(s) ds > 0` such that `P{a ≤ ∑_{i=2}^j u^k_r(i) ≤ b} ≥ ∫_a^b p(x) dx` for all
   `0 ≤ a < b`.

**Formalization Note.** "Every route uses some link" (`∀ r, ∃ ℓ, a_ℓr > 0`) is not printed; without
it the PF problem (3) has no solution (the feasible set is unbounded in `γ_r` and the objective
unbounded), so the paper's `Λ(n)` would not exist. The sum `∑_{i=2}^j u^k_r(i)` of `j − 1` i.i.d.
copies is the image of the product law under the sum of the first `j − 1` coordinates. Positivity of
`λ^k, ν^k` is also asked of the dummy network `k = 0` (see `NetSeq`). -/
structure Standing : Prop where
  A_nonneg : ∀ ℓ r, 0 ≤ S.A ℓ r
  A_rank : S.A.rank = L
  A_col : ∀ r, ∃ ℓ, 0 < S.A ℓ r
  β_pos : ∀ r, 0 < S.β r
  Fa_prob : ∀ r, IsProbabilityMeasure (S.Fa r)
  Fs_prob : ∀ r, IsProbabilityMeasure (S.Fs r)
  Fa_nonneg : ∀ r, S.Fa r (Set.Iio 0) = 0
  Fs_nonneg : ∀ r, S.Fs r (Set.Iio 0) = 0
  p_gt : 2 < S.p
  Fa_moment : ∀ r, ∫⁻ x, ENNReal.ofReal (|x| ^ S.p) ∂(S.Fa r) < ⊤
  Fs_moment : ∀ r, ∫⁻ x, ENNReal.ofReal (|x| ^ S.p) ∂(S.Fs r) < ⊤
  Fa_mean : ∀ r, ∫ x, x ∂(S.Fa r) = 1 / S.lam 1 r
  Fs_mean : ∀ r, ∫ x, x ∂(S.Fs r) = S.nu 1 r
  lam_pos : ∀ k r, 0 < S.lam k r
  nu_pos : ∀ k r, 0 < S.nu k r
  lamLim_pos : ∀ r, 0 < S.lamLim r
  nuLim_pos : ∀ r, 0 < S.nuLim r
  lam_lim : ∀ r, Tendsto (fun k => S.lam k r) atTop (𝓝 (S.lamLim r))
  nu_lim : ∀ r, Tendsto (fun k => S.nu k r) atTop (𝓝 (S.nuLim r))
  theta_lim : ∀ r, Tendsto (fun k : ℕ => (k : ℝ) * (S.rhoK k r - S.rho r)) atTop (𝓝 (S.θ r))
  unbounded : ∀ k, 1 ≤ k → ∀ r, ∀ a : ℝ, 0 < a → 0 < S.lawU k r (Set.Ici a)
  spread : ∀ k, 1 ≤ k → ∀ r, ∃ j : ℕ, 2 ≤ j ∧ ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    0 < ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (f x) ∧
    ∀ a b : ℝ, 0 ≤ a → a < b →
      ∫⁻ x in Set.Icc a b, ENNReal.ofReal (f x) ≤
        ((Measure.infinitePi fun _ : ℕ => S.lawU k r).map
          (fun y => ∑ i ∈ Finset.range (j - 1), y i)) (Set.Icc a b)

/-- The **heavy-traffic condition** (11), p. 10: every link is a bottleneck, `A_ℓ ρ = c_ℓ` for all
`ℓ`. -/
def HeavyTraffic : Prop := S.A *ᵥ S.rho = S.c

/-- The **usual traffic condition** `Aθ < 0` (componentwise), (66), p. 19. -/
def UsualTraffic : Prop := ∀ ℓ, (S.A *ᵥ S.θ) ℓ < 0

end NetSeq

end FairDiffusionLimit


