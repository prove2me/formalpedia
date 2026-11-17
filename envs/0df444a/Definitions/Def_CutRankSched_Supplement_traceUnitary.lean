-- Prove2me | Definitions.Def_CutRankSched_Supplement_traceUnitary
-- name    : CutRankSched_Supplement_traceUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:40:10.807568+00:00
-- url     : https://prove2.me/theorems/7fa3c897-0bdf-4747-8b94-9d3ffcfd219d
-- title:
--   The product $R_{\epsilon_n}(P(p_n))\cdots R_{\epsilon_1}(P(p_1))$ of a trace
-- statement:
--   For a trace of signed Pauli labels $(\epsilon_1,p_1),\dots,(\epsilon_n,p_n)$, its unitary is the product of signed rotations in the order of (4),
--   $$
--   R_{\epsilon_n}(P(p_n))\cdots R_{\epsilon_1}(P(p_1)),
--   $$
--   the first rotation of the trace acting first. The empty trace has unitary $\mathbf 1$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 4.1, Eq. (4), p.6

import Mathlib
import Definitions.Def_CutRankSched_Supplement_pauliOp
import Definitions.Def_CutRankSched_Supplement_rot

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The product of the signed Pauli rotations of a trace `(ε₁, p₁), …, (ε_n, p_n)` in the order of
(4) (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §4.1, Eq. (4), p.6): `R_{ε_n}(P(p_n)) ⋯ R_{ε_1}(P(p_1))`; the first rotation of the list
acts first. -/
noncomputable def traceUnitary {m : ℕ} (tr : List (Bool × Pauli m)) : Op m :=
  tr.foldl (fun U e => rot e.1 (pauliOp e.2) * U) 1

end Supplement

end CutRankSched


