-- Prove2me | Definitions.Def_TIESched_convL
-- name    : TIESched_convL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:26.178063+00:00
-- url     : https://prove2.me/theorems/1ce20fa3-8566-42bb-b47f-f5e2531ca6e2
-- title:
--   Zero extension and the left convolution $(f*_L\kappa)(p)=I_D(s\mapsto f(s)\kappa(p-s))$
-- statement:
--   For a job set $J$ and $D=m|J|$, a report matrix is identified with a vector of $\mathbb R^D$ by ordering coordinates by machine index and then by increasing job label. The **zero extension** of a function on nonnegative reports keeps its values on $[0,\infty)^D$ and is $0$ whenever some coordinate is negative. For a family of functionals $I_D$, a locally bounded $f$ and a smooth compactly supported kernel $\kappa$, the **left convolution** (10) is
--   $$(f*_L\kappa)(p)=I_D\big(s\mapsto f(s)\,\kappa(p-s)\big).$$
--
--   It defines the left-smoothed utility interactions of §5.4 without any measurability assumption.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §5.4, Step 1, p.29; App. A.1, p.40; display (10), p.40

import Mathlib

set_option autoImplicit false

namespace TIESched

/-- The report matrix in `ℝ^{m×J}` with coordinate vector `s ∈ ℝ^D`, `D = m|J|`, the coordinates
being ordered "by machine index and then by increasing job label" (arXiv:2611.05142, App. A.1,
p.40): coordinate `(i, j)` is entry number `i·|J| + rank_J(j)`. -/
def ofCoords {m : ℕ} (J : Finset ℕ) (s : Fin (m * J.card) → ℝ) : Fin m → J → ℝ :=
  fun i j => s (finProdFinEquiv (i, (J.orderIsoOfFin rfl).symm j))

open Classical in
/-- **Zero extension** of a function on nonnegative reports to all of `ℝ^{m×J}` (arXiv:2611.05142,
§5.4, Step 1, p.29): keep the values on `[0, ∞)^D` and set the function to zero whenever any
coordinate is negative. -/
noncomputable def zeroExt {m : ℕ} {J : Finset ℕ} (f : (Fin m → J → ℝ) → ℝ) (p : Fin m → J → ℝ) :
    ℝ :=
  if ∀ i j, 0 ≤ p i j then f p else 0

/-- **Left convolution through `I_D`**, display (10) (arXiv:2611.05142, App. A.2, p.40):
`(f ∗_L κ)(p) = I_D(s ↦ f(s) κ(p − s))`, with `D = m|J|` and report matrices identified with
`ℝ^D` in the coordinate order of Lemma A.1 (`ofCoords`).

**Formalization Note.** `I` is any family of functionals `I_D`; the statements that use `convL`
assume `IsCompatibleIntegration I`. No Lebesgue integral of a mechanism-derived function is taken. -/
noncomputable def convL {m : ℕ} (I : (D : ℕ) → ((Fin D → ℝ) → ℝ) → ℝ) (J : Finset ℕ)
    (f κ : (Fin m → J → ℝ) → ℝ) (p : Fin m → J → ℝ) : ℝ :=
  I (m * J.card) (fun s => f (ofCoords J s) * κ (p - ofCoords J s))

end TIESched


