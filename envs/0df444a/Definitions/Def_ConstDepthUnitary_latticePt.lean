-- Prove2me | Definitions.Def_ConstDepthUnitary_latticePt
-- name    : ConstDepthUnitary_latticePt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:21.494516+00:00
-- url     : https://prove2.me/theorems/001afd68-53ed-4cf7-8172-863798189b84
-- title:
--   Lattice points in $\mathbb R^N$
-- statement:
--   An integer vector $w\in\mathbb Z^N$ as a point of $\mathbb R^N$, and the point $(w+\frac12\mathbf 1)\Delta$ of the rescaled half-integer lattice used in Eq. (19).
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.2 and Eq. (19), p.17

import Mathlib

namespace ConstDepthUnitary

/-- The integer point `w ∈ ℤ^N` as a point of `ℝ^N`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.2, p.17. -/
noncomputable def latticePt {N : ℕ} (w : Fin N → ℤ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun j => (w j : ℝ)

/-- The point `(w + ½·1) Δ` of the rescaled half-integer lattice, Eq. (19), p.17. -/
noncomputable def halfLatticePt {N : ℕ} (Δ : ℝ) (w : Fin N → ℤ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun j => ((w j : ℝ) + 1 / 2) * Δ

end ConstDepthUnitary


