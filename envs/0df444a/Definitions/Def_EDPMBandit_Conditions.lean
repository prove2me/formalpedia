-- Prove2me | Definitions.Def_EDPMBandit_Conditions
-- name    : EDPMBandit_Conditions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:14.674186+00:00
-- url     : https://prove2.me/theorems/5d0967a4-e3f2-4ee9-845a-0569c3310711
-- title:
--   Stability (Definition 1), smoothness with $M_0=\infty$ (Definition 2) and linear gap (Definition 3)
-- statement:
--   Let $U:L\to\mathbb R$ be an EDPM on the seminormed space $(L,\|\cdot\|)$ and $D^\Delta$ the mixtures of the arm distributions.
--
--   1. **Stability** (Definition 1) with parameters $\upsilon,b>0$, $q\ge1$: (Requirement 1) $|U(F)-U(G)|\le b(\|F-G\|+\|F-G\|^q)$ for all $F\in D^\Delta$, $G\in L$; (Requirement 2) for every arm $i$, $t\ge1$ and $x>0$,
--   $$
--   \mathbb P\big(\|\hat F^{(i)}_t-F^{(i)}\|\ge x\big)\le 2\exp(-\upsilon t x^2).
--   $$
--   2. **Smoothness with $M_0=\infty$** (Definition 2) with parameter $\beta\ge0$: for every $F\in D^\Delta$ there is a bounded linear functional $\partial U(F)$ on $L$ with
--   $$
--   |U(G)-U(F)-\partial U(F)\cdot(G-F)|\le\tfrac12\beta\|G-F\|^2\qquad\text{for all }G\in L.
--   $$
--   3. **Linear gap** (Definition 3) with parameter $\eta>0$: $U(F)\le U(F^{(i^*)})-\frac1\eta\|F-F^{(i^*)}\|$ for all $F\in D^\Delta$.
--
--   These are the hypotheses of the paper's regret bounds; the parameters $\upsilon,b,q,\beta,\eta$ appear in the bounds.
--
--   **Formalization Note** The parameters are explicit arguments of `StabilityReq1`, `StabilityReq2`, `IsStable`, `IsSmoothInf` and `HasLinearGap` rather than existentially quantified, because the bounds are stated in terms of them. `IsDifferentialAt S N U β F dU` says that `dU` is a bounded linear functional ($|dU\,h|\le C\|h\|$ for some $C$) satisfying the quadratic bound at $F$; the bound determines it uniquely, and with $M_0=\infty$ it implies differentiability. $\|\cdot\|^q$ is `Real.rpow`.
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.7 Definition 1; p.9 Definition 2 (with M₀ = ∞); p.10 Definition 3

import Mathlib
import Definitions.Def_EDPMBandit_Model

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

variable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]

/-- Requirement 1 of Definition 1 (Stable EDPM), arXiv:1806.01380v3, p.7, with parameters
`b > 0`, `q ≥ 1`: "U admits ω(x) = b(x + x^q) as a local modulus of continuity for all
F ∈ D^Δ, i.e., |U(F) − U(G)| ≤ ω(‖F − G‖), ∀F ∈ D^Δ, G ∈ L_{‖·‖}".

**Formalization Note.** The parameters are arguments, not existentially quantified, because the
bounds of the paper are stated in terms of them. `x^q` is `Real.rpow` (`q` real). -/
def StabilityReq1 (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ)
    (M : BanditModel K Ω 𝒱) (b q : ℝ) : Prop :=
  0 < b ∧ 1 ≤ q ∧
    ∀ F ∈ mixtures S M, ∀ G : S.L, |U F - U G| ≤ b * (N (F - G) + N (F - G) ^ q)

/-- Requirement 2 of Definition 1 (Stable EDPM), arXiv:1806.01380v3, p.7, with parameter
`υ > 0`: "for all i ∈ K, t ≥ 1, P(‖F̂^{(i)}_t − F^{(i)}‖ ≥ x) ≤ 2 exp(−υ t x²), ∀x > 0".

**Formalization Note.** `υ > 0` is part of Definition 1 ("there exist υ, b > 0, q ≥ 1"). The
probability is the measure `M.P` of the event (an outer measure if the event is not
measurable), compared in `ℝ≥0∞`. -/
def StabilityReq2 (S : DistSpace) (N : Seminorm ℝ S.L) (M : BanditModel K Ω 𝒱) (υ : ℝ) :
    Prop :=
  0 < υ ∧
    ∀ (i : Fin K) (t : ℕ), 1 ≤ t → ∀ x : ℝ, 0 < x →
      M.P {ω | x ≤ N (empArm S M i t ω - armDist S M i)} ≤
        ENNReal.ofReal (2 * Real.exp (-(υ * t * x ^ 2)))

/-- Definition 1 (Stable EDPM), arXiv:1806.01380v3, p.7: `U` is stable with respect to the
seminorm `‖·‖` with parameters `υ, b > 0`, `q ≥ 1` (both requirements). -/
def IsStable (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱)
    (υ b q : ℝ) : Prop :=
  StabilityReq1 S N U M b q ∧ StabilityReq2 S N M υ

/-- The differential of Definition 2 (Smooth EDPM), arXiv:1806.01380v3, p.9, at one point `F`,
in the case `M₀ = ∞`: `dU` is a bounded linear functional on `L_{‖·‖}` ("∂U(F) ∈ 𝓛(L_{‖·‖}, ℝ)")
with `|U(G) − U(F) − ∂U(F)·(G − F)| ≤ ½ β ‖G − F‖²` for every `G ∈ L`.

**Formalization Note.** Bounded means `|dU h| ≤ C ‖h‖` for some constant `C`. The quadratic
bound forces `dU` to be the (Fréchet) differential of `U` at `F`, and determines it uniquely. -/
def IsDifferentialAt (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (β : ℝ) (F : S.L)
    (dU : S.L →ₗ[ℝ] ℝ) : Prop :=
  (∃ C : ℝ, ∀ h : S.L, |dU h| ≤ C * N h) ∧
    ∀ G : S.L, |U G - U F - dU (G - F)| ≤ 1 / 2 * β * N (G - F) ^ 2

/-- Definition 2 (Smooth EDPM) with `M₀ = ∞`, arXiv:1806.01380v3, p.9: "U is smooth if it is
differentiable on D^Δ, and there exist β ≥ 0, M₀ > 0 such that for any F ∈ D^Δ, G ∈ L_{‖·‖}
satisfying ‖G − F‖ ≤ M₀ we have that |U(G) − U(F) − ∂U(F)·(G − F)| ≤ ½β‖G − F‖²", with
`M₀ = ∞` (no restriction on `G`), as in Theorems 3 and 4.

**Formalization Note.** `β` is an argument (it appears in the bounds). The differential at
each `F ∈ D^Δ` is an existentially given bounded linear functional satisfying the quadratic
bound (`IsDifferentialAt`); with `M₀ = ∞` that bound implies differentiability. -/
def IsSmoothInf (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱)
    (β : ℝ) : Prop :=
  0 ≤ β ∧ ∀ F ∈ mixtures S M, ∃ dU : S.L →ₗ[ℝ] ℝ, IsDifferentialAt S N U β F dU

/-- Definition 3 (Linear gap), arXiv:1806.01380v3, p.10: "U has a linear gap if there exists
η > 0 such that U(F) ≤ U(F^{(i*)}) − (1/η)‖F − F^{(i*)}‖, ∀F ∈ D^Δ". `η` is an argument. -/
def HasLinearGap (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱)
    (istar : Fin K) (η : ℝ) : Prop :=
  0 < η ∧ ∀ F ∈ mixtures S M,
    U F ≤ U (armDist S M istar) - 1 / η * N (F - armDist S M istar)

end EDPMBandit


