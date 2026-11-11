-- Prove2me | Definitions.Def_CellProbeTree_Matching_ConvexDistance
-- name    : CellProbeTree_Matching_ConvexDistance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:34:41.573813+00:00
-- url     : https://prove2.me/theorems/736d3c20-0618-4821-a724-145878d4cb73
-- title:
--   Talagrand's convex distance $d_T(y, A)$ in sup–inf form
-- statement:
--   Let $\Omega = \prod_{c \in I} \Omega_c$ be a product over a finite index set $I$, and let $A \subseteq \Omega$ be nonempty. For $y \in \Omega$, **Talagrand's convex distance** is
--   $$d_T(y, A) = \sup_{\substack{\alpha_c \ge 0 \\ \sum_c \alpha_c^2 \le 1}} \; \inf_{z \in A} \; \sum_{c \in I} \alpha_c \, \mathbf 1[y_c \ne z_c].$$
--   The weights $\alpha$ may be chosen depending on $y$ but must then work against every $z \in A$. In the paper a coordinate is a whole memory word: $\Omega = (\{0,1\}^w)^s$.
--
--   **Formalization Note.** Real `⨆`/`⨅`: for nonempty $A$ the infimum is over a nonempty set bounded below by $0$, and the supremum over a nonempty set ($\alpha = 0$) bounded above by $|I|$, so both are the true values. For $A = \emptyset$ the Lean value is a junk $0$; statements assume $A \neq \emptyset$.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 12, §3.2, equation (9)

import Mathlib

/-!
# Talagrand's convex distance in the sup–inf form

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, §3.2, p. 12, equation (9).

For a point `y` of a finite product `∀ c, Ω c` and a set `A` of such points,
`d_T(y, A) = sup_{α ≥ 0, Σ α_c² ≤ 1} inf_{z ∈ A} Σ_c α_c 1[y_c ≠ z_c]`.

**Formalization Note.** The supremum and infimum are real `⨆`/`⨅`. For nonempty `A` the inner
infimum is over a nonempty set bounded below by `0`, and the outer supremum is over a nonempty set
(`α = 0`) bounded above by `card ι`, so both are the true sup and inf. For `A = ∅` the value is a
junk `0`; Theorem 3.2 assumes `A` nonempty.
-/

namespace CellProbeTree.Matching

open Classical in
/-- Talagrand's convex distance `d_T(y, A)` of (9). -/
noncomputable def convexDistance {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    (y : ∀ c, Ω c) (A : Set (∀ c, Ω c)) : ℝ :=
  ⨆ α : {α : ι → ℝ // (∀ c, 0 ≤ α c) ∧ ∑ c, α c ^ 2 ≤ 1},
    ⨅ z : A, ∑ c, (if y c ≠ (z : ∀ c, Ω c) c then α.1 c else 0)

end CellProbeTree.Matching


