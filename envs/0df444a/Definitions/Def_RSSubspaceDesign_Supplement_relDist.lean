-- Prove2me | Definitions.Def_RSSubspaceDesign_Supplement_relDist
-- name    : RSSubspaceDesign_Supplement_relDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:34:08.754993+00:00
-- url     : https://prove2.me/theorems/18d5b3e1-9780-488a-8581-e3511579f7ff
-- title:
--   Relative Hamming distance $\Delta(x,y)$
-- statement:
--   For words $x, y \in \Sigma^n$ over an alphabet $\Sigma$, the **relative Hamming distance** is the fraction of coordinates in which they differ:
--
--   $$
--   \Delta(x,y) = \frac{|\{i \in [n] : x_i \neq y_i\}|}{n}.
--   $$
--
--   It is the distance in which all list-decoding, list-recovery and curve-decoding radii of the paper are measured.
--
--   **Formalization Note** Coordinates are indexed by `Fin n` (0-based) and the value is a real number. At $n = 0$ Lean's division returns $0$; every statement of the mission that uses $\Delta$ has $n \ge 1$.
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Section 2, p.10

import Mathlib

namespace RSSubspaceDesign

namespace Supplement

open Classical in
/-- **Relative Hamming distance.** Alrabiah–Goyal–Guruswami, *Explicit Reed-Solomon Subspace
Designs: Optimal List and Line Decoding*, arXiv:2610.36215 (held version, sha256 cf26424b…f36206),
Section 2, p.10: for `x, y ∈ Σⁿ`, `Δ(x, y) = |{i ∈ [n] | xᵢ ≠ yᵢ}| / n`.

**Formalization Note.** Coordinates are `Fin n` (0-based). The value is real. At `n = 0` Lean's
division gives `Δ = 0`; every statement of this mission that uses `Δ` has `n ≥ 1`. -/
noncomputable def relDist {Sig : Type*} {n : ℕ} (x y : Fin n → Sig) : ℝ :=
  ((Finset.univ.filter fun i => x i ≠ y i).card : ℝ) / n

end Supplement

end RSSubspaceDesign


