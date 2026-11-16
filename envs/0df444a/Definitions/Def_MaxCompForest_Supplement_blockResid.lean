-- Prove2me | Definitions.Def_MaxCompForest_Supplement_blockResid
-- name    : MaxCompForest_Supplement_blockResid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:02.129307+00:00
-- url     : https://prove2.me/theorems/4229054c-76f2-482a-a3e5-b1e0ec25abf2
-- title:
--   Block residual matrix $S_Q=D(I-P_Q)$
-- statement:
--   For a partition $Q$ of $V$ and masses $D=\mathrm{diag}(d_v)$, the **block residual** is
--
--   $$S_Q=D\,(I-P_Q),$$
--
--   where $P_Q$ is degree-weighted block averaging. For every signal $f$, $f^{\top}S_Qf$ is the squared $D$-error of replacing $f$ by its block means; $S_Q$ is symmetric positive semidefinite.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (5.1), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MaxCompForest_Supplement_blockAvgMat
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The block residual matrix** `S_Q = D(I − P_Q)`; `fᵀ S_Q f` is the squared `D`-error of replacing `f` by its
degree-weighted block means.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (5.1), p.28. -/
noncomputable def blockResid (W : V → ℝ) (Q : Finpartition (Finset.univ : Finset V)) : Matrix V V ℝ :=
  Matrix.diagonal W * (1 - blockAvgMat W Q)

end MaxCompForest.Supplement


