-- Prove2me | Definitions.Def_LearnStability_ConvexSCO_Problem
-- name    : LearnStability_ConvexSCO_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:14:28.753385+00:00
-- url     : https://prove2.me/theorems/72f1f145-f6e7-4d81-a2a4-e03da9960f42
-- title:
--   Stochastic convex optimization in a Hilbert space; empirical and Tikhonov-regularized minimizers
-- statement:
--   A **stochastic convex optimization problem** (§4.1) consists of a closed, convex, bounded, nonempty set $\mathcal H$ in a real Hilbert space $E$ and an objective $f(h;z)$ which, for every instance $z$, is convex and $L$-Lipschitz in $h\in\mathcal H$:
--   $$|f(h;z)-f(h';z)|\le L\,\|h-h'\|\qquad(h,h'\in\mathcal H,\ z\in Z),$$
--   with each $f(h;\cdot)$ measurable and, as throughout the paper (p. 2637), $|f(h;z)|\le C$ on $\mathcal H\times Z$.
--
--   For such a problem the file defines:
--
--   1. the optimal risk over the constraint set, $F^*=\inf_{h\in\mathcal H}F(h)$;
--   2. the regularized empirical objective of Eq. (5), $F_S(h)+\frac\lambda2\|h\|^2$;
--   3. a *selection of empirical minimizers*: a map $S\mapsto\hat h_S\in\mathcal H$ with $F_S(\hat h_S)\le F_S(h)$ for all $h\in\mathcal H$;
--   4. a *selection of regularized minimizers* $S\mapsto\hat h_\lambda\in\mathcal H$ minimizing $F_S(h)+\frac\lambda2\|h\|^2$ over $\mathcal H$;
--   5. measurability of a selection: $(S,z)\mapsto f(\hat h_S;z)$ is jointly measurable.
--
--   These are the objects of Theorems 2 and 3, where Tikhonov regularization makes the empirical minimizer stable.
--
--   **Formalization Note** The paper calls the loss bound $B$; here it is $C$, because Theorem 3 uses $B$ for the norm bound $\|h\|\le B$. Stating results for any bound $C$ is equivalent to using $\sup_{h,z}|f(h;z)|$. Minimizers are modelled as selections so that statements hold for "the" minimizer (unique by strong convexity whenever it exists). Measurability of the selection is the series' standing convention, not in the paper.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2642 (§4.1, definition of a stochastic convex optimization problem), p. 2637 (standing bound |f| ≤ B), p. 2644, Eq. (5) and Theorems 2–3

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting

open MeasureTheory

namespace LearnStability.ConvexSCO

variable {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A *stochastic convex optimization problem* (§4.1, p. 2642, together with the standing
bound of §2, p. 2637): a constraint set `Hset` in a real inner product space `E` that is
nonempty, closed, convex and bounded, and an objective `f : E → Z → ℝ` that, for every
instance `z`, is convex and `L`-Lipschitz in `h` on `Hset`, with each `f(h; ·)` measurable
and `|f(h; z)| ≤ C` on `Hset × Z`. Only the values of `f` on `Hset` matter. -/
structure IsStochasticConvexProblem (Hset : Set E) (f : E → Z → ℝ) (L C : ℝ) : Prop where
  nonempty : Hset.Nonempty
  convex : Convex ℝ Hset
  closed : IsClosed Hset
  bounded : Bornology.IsBounded Hset
  measurable : ∀ h ∈ Hset, Measurable (f h)
  loss_bounded : ∀ h ∈ Hset, ∀ z, |f h z| ≤ C
  convexOn : ∀ z, ConvexOn ℝ Hset (fun h => f h z)
  lipschitz_nonneg : 0 ≤ L
  lipschitz : ∀ z, ∀ h ∈ Hset, ∀ h' ∈ Hset, |f h z - f h' z| ≤ L * ‖h - h'‖

/-- The optimal risk over the constraint set, `F* = inf_{h ∈ H} F(h)` (p. 2642). -/
noncomputable def optRiskOn (Hset : Set E) (f : E → Z → ℝ) (D : Measure Z) : ℝ :=
  ⨅ h : Hset, risk f D (h : E)

/-- The regularized empirical objective of Eq. (5), p. 2644:
`F_S(h) + (λ/2)‖h‖²`. -/
noncomputable def regObjective (f : E → Z → ℝ) (lam : ℝ) {m : ℕ} (S : Fin m → Z) (h : E) : ℝ :=
  empRisk f S h + lam / 2 * ‖h‖ ^ 2

/-- `hhat` selects, for every sample `S` of size `m`, an empirical minimizer `ĥ_S` over
`Hset`: `ĥ_S ∈ Hset` and `F_S(ĥ_S) ≤ F_S(h)` for all `h ∈ Hset` (Theorem 2, p. 2644). -/
def IsEmpMinimizerOn (Hset : Set E) (f : E → Z → ℝ) {m : ℕ} (hhat : (Fin m → Z) → E) : Prop :=
  ∀ S, hhat S ∈ Hset ∧ ∀ h ∈ Hset, empRisk f S (hhat S) ≤ empRisk f S h

/-- `hhat` selects, for every sample `S` of size `m`, a minimizer `ĥ_λ` of the regularized
objective (5) over `Hset` (Theorem 3, p. 2644). -/
def IsRegMinimizerOn (Hset : Set E) (f : E → Z → ℝ) (lam : ℝ) {m : ℕ}
    (hhat : (Fin m → Z) → E) : Prop :=
  ∀ S, hhat S ∈ Hset ∧ ∀ h ∈ Hset, regObjective f lam S (hhat S) ≤ regObjective f lam S h

/-- The selection is measurable in the series' sense: `(S, z) ↦ f(ĥ_S; z)` is jointly
measurable (standing measurability convention; not in the paper). -/
def IsMeasurableSelection (f : E → Z → ℝ) {m : ℕ} (hhat : (Fin m → Z) → E) : Prop :=
  Measurable (fun p : (Fin m → Z) × Z => f (hhat p.1) p.2)

end LearnStability.ConvexSCO


