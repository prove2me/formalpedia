-- Prove2me | Definitions.Def_QuasiStrictNE_Proj
-- name    : QuasiStrictNE_Proj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:11.166008+00:00
-- url     : https://prove2.me/theorems/2758cc00-719d-4cd7-8be6-5079f73ed27f
-- title:
--   Euclidean projection $\Pi_k$ onto $\Delta_k$
-- statement:
--   The projection $\Pi_k:\mathbb R^k\to\Delta_k$ maps $z$ to the vector with coordinates
--   $$
--   \Pi_k(z)_i=\max\{z_i-t_k(z),0\},\qquad i\in[k].
--   $$
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 1, p.9; §4, p.13

import Mathlib
import Definitions.Def_QuasiStrictNE_tk

namespace QuasiStrictNE

/-- **The Euclidean projection `Πk` onto the simplex** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 1, p.9: "and for each i ∈ [k],
zi ↦ max{zi − tk(z), 0}"; §4, p.13: "Denote the EY modification by Πk").

`Proj k z` is the vector with coordinates `max (zᵢ − tk(z)) 0`.

**Formalization Note** Indices are 0-based (`Fin k`). That `Proj k` maps into `Δk` and is the map
of Lemma 1 is the theorem `lemma_1`. -/
noncomputable def Proj (k : ℕ) (z : Fin k → ℝ) : Fin k → ℝ :=
  fun i => max (z i - tk k z) 0

end QuasiStrictNE


