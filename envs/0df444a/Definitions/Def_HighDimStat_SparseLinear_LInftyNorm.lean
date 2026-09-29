-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_LInftyNorm
-- name    : HighDimStat_SparseLinear_LInftyNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:34.822687+00:00
-- url     : https://prove2.me/theorems/f05225ec-816f-4088-a0e6-3619edbf0eaf
-- title:
--   The l-infinity norm of a vector in R^d
-- statement:
--   This is the **`ℓ∞`-norm** of a vector, used in Theorem 7.13 to state the regularization
--   condition `λₙ ≥ 2‖Xᵀw/n‖∞` that the Lagrangian Lasso's tuning parameter must satisfy.
--
--   For $v = (v_1, \dots, v_d) \in \mathbb R^d$,
--
--   $$
--   \|v\|_\infty \;:=\; \max_{j=1,\dots,d} |v_j|.
--   $$
--
--   **Formalization Note** Realized as `⨆ j, |v j|`, the real supremum over the finite index
--   type `Fin d`. For $d>0$ this is exactly the maximum; for $d=0$ it is Mathlib's junk value
--   `0` for the supremum of the empty set, which is harmless since no vector of that type
--   exists to be measured either.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 210 (PDF p. 230), Theorem 7.13

import Mathlib

namespace HighDimStat.SparseLinear

/-- The `ℓ∞`-norm of a vector `v ∈ ℝ^d`, `‖v‖∞ := maxⱼ |vⱼ|`, as used in the regularization
condition `λₙ ≥ 2‖Xᵀw/n‖∞` of Wainwright, *High-Dimensional Statistics* (2019), Theorem 7.13.
Realized as `⨆ j, |v j|` over the finite index type `Fin d`; for `d = 0` this is Mathlib's junk
value `0` for the supremum of the empty set (harmless: no vector exists at `d = 0` either). -/
noncomputable def linfNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ⨆ j, |v j|

end HighDimStat.SparseLinear


