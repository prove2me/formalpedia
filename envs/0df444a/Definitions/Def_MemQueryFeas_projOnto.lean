-- Prove2me | Definitions.Def_MemQueryFeas_projOnto
-- name    : MemQueryFeas_projOnto
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:22.497417+00:00
-- url     : https://prove2.me/theorems/5f0f966b-c566-4fa1-820b-b835feef8b4f
-- title:
--   Orthogonal projection $P_K$ onto a subspace
-- statement:
--   For a linear subspace $K\subseteq\mathbb R^d$, $P_K$ denotes the orthogonal projection onto $K$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8); Game 1, p.12

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **The orthogonal projection `P_K` onto a subspace `K`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): "we
denote by `P_E` the orthogonal projection onto `E`"; also `Proj_K` in Game 1, p.12.

**Formalization Note.** Mathlib's `Submodule.starProjection` (every subspace of `ℝ^d` is complete,
so the projection exists). -/
noncomputable def projOnto {d : ℕ} (K : Submodule ℝ (Vec d)) : Op d :=
  K.starProjection

end MemQueryFeas


