-- Prove2me | Definitions.Def_DualRCD_DualSpace
-- name    : DualRCD_DualSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:29.908954+00:00
-- url     : https://prove2.me/theorems/213f9905-8016-4a15-8126-6dae5dbaee6a
-- title:
--   The dual space $\mathbb R^{mn}$ of block vectors
-- statement:
--   The dual variable of the problem is a block vector $y=(y_1;\dots;y_m)$ with $y_i\in\mathbb R^n$, an element of $\mathbb R^{mn}$ equipped with the Euclidean norm
--   $$
--   \|y\|^2=\sum_{i=1}^m\|y_i\|^2 .
--   $$
--   All distances to the dual optimal set are measured in this norm.
--
--   **Formalization Note.** The space is `PiLp 2` over the blocks. The plain Pi type would carry the sup norm and change every constant.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §2–§3, pp.4–7

import Mathlib

namespace DualRCD

/-- The dual space `ℝ^{mn}` of block vectors `y = (y₁; …; y_m)`, `yᵢ ∈ ℝⁿ`
(Necoara & Fercoq, arXiv:1911.06014v1, §2–§3, pp.4–7).

**Formalization Note.** `PiLp 2` carries the Euclidean norm `‖y‖² = Σᵢ ‖yᵢ‖²` of `ℝ^{mn}`. The plain
Pi type would carry the sup norm and change `dist(·, Y*)` and every constant. -/
abbrev DualSpace (n m : ℕ) : Type := PiLp 2 (fun _ : Fin m => EuclideanSpace ℝ (Fin n))

end DualRCD


