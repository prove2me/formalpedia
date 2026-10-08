-- Prove2me | Definitions.Def_CvitanicKaratzas92_Existence_Utility
-- name    : CvitanicKaratzas92_Existence_Utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:46.118849+00:00
-- url     : https://prove2.me/theorems/6d0b55b9-47eb-4a7f-9b0b-6a403798c47a
-- title:
--   Sections 5–6 and 12 — utilities, marginal inverses, conjugates, and growth conditions
-- statement:
--   A utility function $U$ is strictly increasing, strictly concave, continuously differentiable on $(0,\infty)$, and has marginal utility tending to $+\infty$ at zero and to zero at infinity. Its inverse marginal $I$ and convex conjugate $\widetilde U$ are
--
--   $$I(y)=(U')^{-1}(y),\qquad \widetilde U(y)=\sup_{x>0}\{U(x)-xy\},\quad y>0.$$
--
--   The definition records the right limit $U(0+)$ as an extended real, condition (5.8) on $xU'(x)$, common constants in (8.25), the lower bounds in (12.3), and $U_2(\infty)=\infty$ in (12.11). The terminal utility $U_2$ and each running utility $U_1(t,\cdot)$ satisfy the same basic utility conditions.
--
--   **Formalization Note** The extended conjugate is a genuine extended-real supremum at zero; this matters in the dual extension. The inverse marginal is used on positive arguments, where the utility conditions make the defining infimum the unique inverse of $U'$.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 772–773, 779, 791, 793, (5.1)–(5.9), (8.25), (12.3), (12.11); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Market
import Definitions.Def_CvitanicKaratzas92_Optimality_Utility

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- The transform of (5.2), finite for y > 0 under the utility assumptions. -/
noncomputable def conj (U : ℝ → ℝ) (y : ℝ) : ℝ :=
  ⨆ x : {x : ℝ // 0 < x}, U x.val - x.val * y

/-- The extended transform, including its genuine value at zero. This avoids
the real supremum's default value on an unbounded range. -/
noncomputable def conjExt (U : ℝ → ℝ) (y : ℝ) : EReal :=
  ⨆ x : {x : ℝ // 0 < x}, ((U x.val - x.val * y : ℝ) : EReal)

/-- The right limit U(0+) supplies utility at zero consumption or wealth. -/
noncomputable def uExt (U : ℝ → ℝ) (x : ℝ) : EReal :=
  if 0 < x then (U x : EReal) else
    ⨅ z : {z : ℝ // 0 < z}, (U z.val : EReal)

def UtilityStanding (T : ℝ≥0) (U1 : ℝ≥0 → ℝ → ℝ)
    (U2 : ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ≥0 × ℝ => U1 p.1 p.2)
    (Set.Icc 0 T ×ˢ Set.Ioi 0) ∧
  (∀ t ≤ T, CvitanicKaratzas92.Optimality.IsUtility (U1 t)) ∧ CvitanicKaratzas92.Optimality.IsUtility U2

/-- The relative-risk-aversion condition (5.8), imposed on both utilities. -/
def Cond58 (T : ℝ≥0) (U1 : ℝ≥0 → ℝ → ℝ)
    (U2 : ℝ → ℝ) : Prop :=
  MonotoneOn (fun c => c * deriv U2 c) (Set.Ioi 0) ∧
  ∀ t ≤ T, MonotoneOn (fun c => c * deriv (U1 t) c) (Set.Ioi 0)

/-- The two lower bounds in (12.3). -/
def Cond123 (T : ℝ≥0) (U1 : ℝ≥0 → ℝ → ℝ)
    (U2 : ℝ → ℝ) : Prop :=
  (⊥ : EReal) < ⨅ t : {t : ℝ≥0 // t ≤ T}, uExt (U1 t.val) 0 ∧
  (⊥ : EReal) < uExt U2 0

/-- U₂(∞)=∞ in (12.11). -/
def Cond1211 (U2 : ℝ → ℝ) : Prop := Tendsto U2 atTop atTop

/-- Extended expectation of a real random variable. Its negative part is
required finite wherever it is used for the primal and dual objectives. -/
noncomputable def expectEReal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : EReal :=
  ((∫⁻ a, ENNReal.ofReal (f a) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ a, ENNReal.ofReal (-f a) ∂μ : ℝ≥0∞) : EReal)

end CvitanicKaratzas92.Existence


