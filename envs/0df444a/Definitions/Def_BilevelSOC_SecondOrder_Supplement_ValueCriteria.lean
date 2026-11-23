-- Prove2me | Definitions.Def_BilevelSOC_SecondOrder_Supplement_ValueCriteria
-- name    : BilevelSOC_SecondOrder_Supplement_ValueCriteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:39:49.935041+00:00
-- url     : https://prove2.me/theorems/fcb28149-e35d-48ed-9968-4632d8c6b674
-- title:
--   §2.3 and §4.1 — subdifferentials, the Dini system and the full covector union Q
-- statement:
--   For a real function $h$ on Euclidean space, its convex subdifferential consists of continuous covectors $\xi$ with $h(a)\ge h(x)+\xi(a-x)$ for all $a$; its Clarke subdifferential is the published support-inequality construction in `FirstOrder`. They are distinct notions.
--
--   The value-function system is all four lines of (4.1), using the upper Dini derivative of the published extended-real value function. With a locally equal real representative $\varphi$, the set in (4.2) is
--
--   $$Q=\{DF(z)\}\cup\{DG_i(z):i\in\bar I^G\}\cup\{Df(z)-\xi\circ\pi_x:\xi\in\partial^c\varphi(x)\}\cup\{Dg_i(z):i\in\bar I^g\}.$$
--
--   The covector $\xi\circ\pi_x$ is the paper's vector $(\xi,0)$ under the Euclidean dual identification. The union is built from the actual bilevel data and actual Clarke subdifferential; no arbitrary set is postulated. These definitions expose the systems used by Theorems 4.2 and 4.7 without adding solution regularity assumptions.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 3–4, 6–10, 12–17, §2.3 and §4.1

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
variable {n m p q : ℕ}
/-- Convex subdifferential, included to distinguish it from Clarke's construction (§2.3). -/
def convexSubdiff (h : E n → ℝ) (x : E n) : Set (E n →L[ℝ] ℝ) :=
  {ξ | ∀ a, h x + ξ (a - x) ≤ h a}
noncomputable def valueSystem (D : Data n m p q) (z d : E n × Y m) : Prop :=
  fderiv ℝ D.F z d ≤ 0 ∧
  (∀ i ∈ actG D z, fderiv ℝ (D.G i) z d ≤ 0) ∧
  (fderiv ℝ D.f z d : EReal) - upperDini (valueFn D) z.1 d.1 ≤ 0 ∧
  ∀ i ∈ actg D z, fderiv ℝ (D.g i) z d ≤ 0
/-- Riesz identification of Q (4.2), using continuous covectors. -/
noncomputable def Q42 (D : Data n m p q) (z : E n × Y m) (φ : E n → ℝ) :
    Set ((E n × Y m) →L[ℝ] ℝ) :=
  {fderiv ℝ D.F z} ∪ {a | ∃ i ∈ actG D z, a = fderiv ℝ (D.G i) z} ∪
  {a | ∃ ξ ∈ clarkeSubdiff φ z.1,
    a = fderiv ℝ D.f z - ξ.comp (ContinuousLinearMap.fst ℝ (E n) (Y m))} ∪
  {a | ∃ i ∈ actg D z, a = fderiv ℝ (D.g i) z}
end BilevelSOC.SecondOrder.Supplement


