-- Prove2me | Definitions.Def_TimeInconsLQ_Sufficient_Adjoint
-- name    : TimeInconsLQ_Sufficient_Adjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:40.842812+00:00
-- url     : https://prove2.me/theorems/68303e1c-2a42-456c-89fe-df97c4c082a2
-- title:
--   §3 — the adjoint flows (3.1)–(3.2), Λ(s;t) and H(s;t), condition (3.4), and the perturbation equations of the proof of Proposition 3.1
-- statement:
--   This file defines the objects of §3 of Hu, Jin and Zhou, built on the model of `TimeInconsLQ.Sufficient.Model` (data $A,B,C^j,D^j,Q,R,G,h,\mu_1,\mu_2$, Brownian motion $W$, filtration $(\mathcal F_t)$, horizon $T$).
--
--   **BSDEs on $[t,T]$.** For $t\in[0,T]$, a terminal value $\xi$ and a driver $F$, a pair $(p,k)=(p,k^1,\dots,k^d)$ **solves the BSDE on $[t,T]$**
--
--   $$-dp(s)=F(s,p(s),k(s))\,ds-\sum_{j=1}^dk^j(s)\,dW^j_s,\qquad p(T)=\xi,$$
--
--   if $p$ and every $k^j$ are progressively measurable (after setting them to $0$ before $t$), $\mathbb E\int_t^T|p|^2ds<\infty$, $\mathbb E\int_t^T|k^j|^2ds<\infty$, and for every $r\in[t,T]$, almost surely, $p(r)=\xi+\int_r^TF(s,p(s),k(s))\,ds-\sum_j\int_r^Tk^j\,dW^j$.
--
--   **First adjoint flow** (3.1). Given a state process $X^*$, for each $t\in[0,T)$ the pair $(p(\cdot;t),k(\cdot;t))$ solves
--
--   $$dp(s;t)=-\Big[A_s'p(s;t)+\sum_{j=1}^d(C^j_s)'k^j(s;t)+Q_sX^*_s\Big]ds+\sum_{j=1}^dk^j(s;t)\,dW^j_s,\quad s\in[t,T],\qquad p(T;t)=GX^*_T-h\,\mathbb E_t[X^*_T]-\mu_1X^*_t-\mu_2.$$
--
--   **Second adjoint flow** (3.2). For each $t$, $(P(\cdot;t),K(\cdot;t))$ takes values in the symmetric matrices on $[t,T]$ and solves
--
--   $$dP(s;t)=-\Big\{A_s'P+PA_s+\sum_{j=1}^d\big[(C^j_s)'PC^j_s+(C^j_s)'K^j+K^jC^j_s\big]+Q_s\Big\}ds+\sum_{j=1}^dK^j(s;t)\,dW^j_s,\quad P(T;t)=G.$$
--
--   **The processes $\Lambda$ and $H$.** For a control $u^*$,
--
--   $$\Lambda(s;t)=B_sp(s;t)+\sum_{j=1}^d(D^j_s)'k^j(s;t)+R_su^*_s\in\mathbb R^l,\qquad H(s;t)=R_s+\sum_{j=1}^d(D^j_s)'P(s;t)D^j_s\in\mathbb R^{l\times l}.$$
--
--   **Condition (3.4).** A family $\Lambda(s;t)$ satisfies (3.4) if for every $t\in[0,T)$:
--
--   1. $\mathbb E_t\int_t^T|\Lambda(s;t)|\,ds<+\infty$ a.s.;
--   2. $\lim_{s\downarrow t}\mathbb E_t[\Lambda(s;t)]=0$ a.s.
--
--   **Perturbation equations** (proof of Proposition 3.1). For $t$, $\varepsilon>0$ and $v$, $Y$ and $Z$ solve, on $[t,T]$ with $Y_t=Z_t=0$,
--
--   $$dY_s=A_sY_s\,ds+\sum_{j=1}^d\big[C^j_sY_s+D^j_sv\mathbf 1_{s\in[t,t+\varepsilon)}\big]dW^j_s,\qquad dZ_s=\big[A_sZ_s+B_s'v\mathbf 1_{s\in[t,t+\varepsilon)}\big]ds+\sum_{j=1}^dC^j_sZ_s\,dW^j_s.$$
--
--   These are the objects of the sufficient condition (Theorem 3.2) and its proof.
--
--   **Formalization Note.** The flows are curried, one BSDE on $[t,T]$ per $t$, in the sign convention of `Peng1990_SMP_Stochastic`'s `SolvesBSDE` ($p(r)=\xi+\int_r^TF-\sum_j(J^j(T)-J^j(r))$, with $J^j$ an Itô integral process of $\mathbf 1_{s\ge t}k^j$). Requiring a solution on all of $[0,T]$ would be a stronger hypothesis, so the BSDE lives on $[t,T]$. The matrix equation (3.2) is read entrywise through `matEntries`/`entriesMat`; symmetry of $P,K^j$ on $[t,T]$ (the paper's $\mathbb S^n$) is part of the definition. Condition (3.4)(1) is a conditional expectation of a nonnegative, possibly non-integrable variable; it is encoded exactly as the existence of $\mathcal F_t$-sets $\Omega_m\uparrow$ of full union with $\mathbb E[\mathbf 1_{\Omega_m}\int_t^T|\Lambda|]<\infty$. Condition (3.4)(2) concerns uncountably many conditional expectations, so it is stated version-robustly: there is a $\mathcal B\otimes\mathcal F_t$-measurable process $\hat\Lambda$ that, for almost every $s\in(t,T]$, is a version of $\mathbb E_t[\Lambda(s;t)]$, and almost surely $\hat\Lambda_s\to0$ as $s\downarrow t$; since $\Lambda(\cdot;t)$ is itself only defined up to $ds\otimes d\mathbb P$-null sets, "for almost every $s$" is the meaningful reading. The perturbation equations are written as SDEs from time $0$ with initial value $0$ and coefficients multiplied by $\mathbf 1_{s\ge t}$, so their solutions vanish on $[0,t]$. `supSq` computes $\sup_{s\in[t,T]}|Y_s|^2$ over the rational times of $[t,T]$: it equals the supremum over $[t,T]$ for the continuous version and does not depend on the version chosen.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, pp. 4–6, (3.1), (3.2), Proposition 3.1 (Λ, H), proof of Proposition 3.1 (Y, Z), (3.4)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ}

/-- `(p, k)` solves the backward SDE `−dp(s) = F(s, p(s), k(s)) ds − Σⱼ kʲ(s) dWʲ(s)`,
`p(T) = ξ`, on the interval `[t, T]`: `p` and every `kʲ` (set to `0` before `t`) are progressively
measurable with `E ∫ₜᵀ |p|² ds < ∞`, `E ∫ₜᵀ |kʲ|² ds < ∞`, and for every `r ∈ [t, T]`, almost surely,
`p(r) = ξ + ∫ᵣᵀ F(s, p(s), k(s)) ds − Σⱼ ∫ᵣᵀ kʲ dWʲ`, where `∫ᵣᵀ kʲ dWʲ = Jʲ(T) − Jʲ(r)` for Itô
integral processes `Jʲ` of `1_{s ≥ t} kʲ(s)` against `Wʲ`. -/
def SolvesBSDEOn {ι : Type*} [Fintype ι] (M : Data Ω n l d) (t : ℝ≥0) (ξ : Ω → ι → ℝ)
    (F : ℝ≥0 → Ω → (ι → ℝ) → (Fin d → ι → ℝ) → (ι → ℝ))
    (p : ℝ≥0 → Ω → ι → ℝ) (k : Fin d → ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsStronglyProgressive (filt M) (fun s ω => if t ≤ s then p s ω else 0) ∧
    (∀ j, IsStronglyProgressive (filt M) (fun s ω => if t ≤ s then k j s ω else 0)) ∧
    ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖p s.toNNReal ω‖ₑ ^ 2 ∂volume ∂M.P < ⊤ ∧
    (∀ j, ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖k j s.toNNReal ω‖ₑ ^ 2 ∂volume ∂M.P < ⊤) ∧
    ∃ J : ι → Fin d → ℝ≥0 → Ω → ℝ,
      (∀ i j, Peng1990.SMP.IsItoIntegral (filt M) M.P M.T (fun s ω => M.W s ω j)
        (fun s ω => if t ≤ s then k j s ω i else 0) (J i j)) ∧
      ∀ r : ℝ≥0, t ≤ r → r ≤ M.T → ∀ᵐ ω ∂M.P,
        IntegrableOn
          (fun s : ℝ => F s.toNNReal ω (p s.toNNReal ω) (fun j => k j s.toNNReal ω))
          (Set.Icc (r : ℝ) M.T) ∧
        ∀ i, p r ω i = ξ ω i
          + (∫ s in Set.Icc (r : ℝ) M.T,
              F s.toNNReal ω (p s.toNNReal ω) (fun j => k j s.toNNReal ω)) i
          - ∑ j, (J i j M.T ω - J i j r ω)

/-- The first adjoint equation (3.1) at time `t`, along the state `X` of the control:
`dp(s;t) = −[Aₛᵀ p(s;t) + Σⱼ (Cʲₛ)ᵀ kʲ(s;t) + Qₛ Xₛ] ds + Σⱼ kʲ(s;t) dWʲₛ`, `s ∈ [t, T]`,
`p(T;t) = G X_T − h E_t[X_T] − μ₁ X_t − μ₂`. -/
def FirstAdjoint (M : Data Ω n l d) (X : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesBSDEOn M t
    (fun ω => M.G *ᵥ X M.T ω - M.h *ᵥ condVec M t (X M.T) ω - M.μ₁ *ᵥ X t ω - M.μ₂)
    (fun s ω y z => (M.A s)ᵀ *ᵥ y + ∑ j, (M.C j s ω)ᵀ *ᵥ z j + M.Q s ω *ᵥ X s ω)
    p k

/-- The second adjoint equation (3.2) at time `t`, read entrywise:
`dP(s;t) = −{Aₛᵀ P + P Aₛ + Σⱼ [(Cʲₛ)ᵀ P Cʲₛ + (Cʲₛ)ᵀ Kʲ + Kʲ Cʲₛ] + Qₛ} ds + Σⱼ Kʲ(s;t) dWʲₛ`,
`s ∈ [t, T]`, `P(T;t) = G`; `P(s;t)` and `Kʲ(s;t)` take values in the symmetric matrices for
`s ∈ [t, T]`. -/
def SecondAdjoint (M : Data Ω n l d) (t : ℝ≥0)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (K : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ ω, (Pm s ω).IsSymm) ∧
    (∀ j, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ ω, (K j s ω).IsSymm) ∧
    SolvesBSDEOn M t (fun _ => Peng1990.SMP.matEntries M.G)
      (fun s ω z w => Peng1990.SMP.matEntries
        ((M.A s)ᵀ * Peng1990.SMP.entriesMat z + Peng1990.SMP.entriesMat z * M.A s
          + ∑ j, ((M.C j s ω)ᵀ * Peng1990.SMP.entriesMat z * M.C j s ω
            + (M.C j s ω)ᵀ * Peng1990.SMP.entriesMat (w j)
            + Peng1990.SMP.entriesMat (w j) * M.C j s ω)
          + M.Q s ω))
      (fun s ω => Peng1990.SMP.matEntries (Pm s ω))
      (fun j s ω => Peng1990.SMP.matEntries (K j s ω))

/-- `Λ(s;t) = Bₛ p(s;t) + Σⱼ (Dʲₛ)ᵀ kʲ(s;t) + Rₛ uₛ` (Proposition 3.1), for one member `(p, k)`
of the first adjoint flow. -/
def Lam (M : Data Ω n l d) (u : ℝ≥0 → Ω → Fin l → ℝ) (p : ℝ≥0 → Ω → Fin n → ℝ)
    (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) (ω : Ω) : Fin l → ℝ :=
  M.B s ω *ᵥ p s ω + ∑ j, (M.D j s ω)ᵀ *ᵥ k j s ω + M.R s ω *ᵥ u s ω

/-- `H(s;t) = Rₛ + Σⱼ (Dʲₛ)ᵀ P(s;t) Dʲₛ` (Proposition 3.1), for one member `P` of the second
adjoint flow. -/
def Hmat (M : Data Ω n l d) (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) (ω : Ω) :
    Matrix (Fin l) (Fin l) ℝ :=
  M.R s ω + ∑ j, (M.D j s ω)ᵀ * Pm s ω * M.D j s ω

/-- Condition (3.4) for a family `Λ(s;t)` (`Lam t s ω`): for every `t ∈ [0, T)`,
(a) `E_t ∫ₜᵀ |Λ(s;t)| ds < +∞` a.s. — there are `𝓕ₜ`-measurable sets `Ωₘ ↑` of full union with
`E[1_{Ωₘ} ∫ₜᵀ |Λ(s;t)| ds] < ∞`; and
(b) `lim_{s↓t} E_t[Λ(s;t)] = 0` a.s. — some `𝔅 ⊗ 𝓕ₜ`-measurable process `Λ̂` is, for almost every
`s ∈ (t, T]`, a version of `E_t[Λ(s;t)]`, and almost surely `Λ̂ₛ → 0` as `s ↓ t`. -/
def Cond34 (M : Data Ω n l d) (Lam : ℝ≥0 → ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  ∀ t : ℝ≥0, t < M.T →
    (∃ Ωm : ℕ → Set Ω, (∀ m, MeasurableSet[filt M t] (Ωm m)) ∧ Monotone Ωm ∧
        M.P (⋃ m, Ωm m)ᶜ = 0 ∧
        ∀ m, ∫⁻ ω in Ωm m, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖Lam t s.toNNReal ω‖ₑ ∂volume ∂M.P < ⊤) ∧
    (∃ Lhat : ℝ → Ω → Fin l → ℝ,
        Measurable[MeasurableSpace.comap Prod.fst (borel ℝ) ⊔
          MeasurableSpace.comap Prod.snd (filt M t)] (fun q : ℝ × Ω => Lhat q.1 q.2) ∧
        (∀ᵐ s ∂(volume.restrict (Set.Ioc (t : ℝ) M.T)), ∀ i,
          (fun ω => Lhat s ω i) =ᵐ[M.P]
            condExp (filt M t) M.P (fun ω => Lam t s.toNNReal ω i)) ∧
        ∀ᵐ ω ∂M.P, Tendsto (fun s => Lhat s ω) (𝓝[>] (t : ℝ)) (𝓝 0))

/-- The first-order perturbation `Y = Y^{t,ε,v}` of the proof of Proposition 3.1, as an SDE on
`[0, T]` that vanishes on `[0, t]`: `dYₛ = Aₛ Yₛ ds + Σⱼ [Cʲₛ Yₛ + Dʲₛ v 1_{s∈[t,t+ε)}] dWʲₛ` for
`s ∈ [t, T]`, `Y_t = 0`. -/
def IsPertY (M : Data Ω n l d) (t : ℝ≥0) (ε : ℝ) (v : Ω → Fin l → ℝ)
    (Y : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  Peng1990.SMP.SolvesSDE (filt M) M.P M.T M.W 0
    (fun s _ y => if t ≤ s then M.A s *ᵥ y else 0)
    (fun j s ω y => if t ≤ s then
        M.C j s ω *ᵥ y + (if (s : ℝ) < (t : ℝ) + ε then M.D j s ω *ᵥ v ω else 0) else 0) Y

/-- The second-order perturbation `Z = Z^{t,ε,v}` of the proof of Proposition 3.1, as an SDE on
`[0, T]` that vanishes on `[0, t]`: `dZₛ = [Aₛ Zₛ + Bₛᵀ v 1_{s∈[t,t+ε)}] ds + Σⱼ Cʲₛ Zₛ dWʲₛ` for
`s ∈ [t, T]`, `Z_t = 0`. -/
def IsPertZ (M : Data Ω n l d) (t : ℝ≥0) (ε : ℝ) (v : Ω → Fin l → ℝ)
    (Z : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  Peng1990.SMP.SolvesSDE (filt M) M.P M.T M.W 0
    (fun s ω z => if t ≤ s then
        M.A s *ᵥ z + (if (s : ℝ) < (t : ℝ) + ε then (M.B s ω)ᵀ *ᵥ v ω else 0) else 0)
    (fun j s ω z => if t ≤ s then M.C j s ω *ᵥ z else 0) Z

/-- `sup_{s ∈ [t, T]} |Yₛ|²`, computed over the rational times of `[t, T]` (in `[0, ∞]`); for a
process with continuous paths on `[t, T]` (`t < T`) it is the supremum over all of `[t, T]`, and it
does not depend on the choice of version of `Y`. -/
noncomputable def supSq {ι : Type*} [Fintype ι] (T t : ℝ≥0) (Y : ℝ≥0 → Ω → ι → ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : (t : ℝ) ≤ q ∧ (q : ℝ) ≤ T), ‖Y (q : ℝ).toNNReal ω‖ₑ ^ 2

end TimeInconsLQ.Sufficient


