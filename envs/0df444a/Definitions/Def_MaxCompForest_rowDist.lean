-- Prove2me | Definitions.Def_MaxCompForest_rowDist
-- name    : MaxCompForest_rowDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:08.789897+00:00
-- url     : https://prove2.me/theorems/880d5350-8069-4baf-be6b-7b0d62929727
-- title:
--   Euclidean distance between two rows
-- statement:
--   For a family $x=(x_v)_{v\in V}$ in $\mathbb R^d$, the pseudometric $\rho(u,v)=\|x_u-x_v\|$. The rows are an indexed family, so coincident rows retain distinct indices and have distance zero.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1 p.7, Lemma 2.3 p.9

import Mathlib

namespace MaxCompForest

variable {V : Type*} {d : ℕ}

/-- **The row distance** `ρ(u,v) = ‖x_u − x_v‖` of an indexed family of vectors. Coincident rows keep
distinct indices.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1 p.7, Lemma 2.3 p.9. -/
noncomputable def rowDist (x : V → EuclideanSpace ℝ (Fin d)) (u v : V) : ℝ := ‖x u - x v‖

end MaxCompForest


