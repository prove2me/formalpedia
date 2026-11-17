-- Prove2me | Definitions.Def_CutRankSched_Supplement_circuitUnitary
-- name    : CutRankSched_Supplement_circuitUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:39:32.768069+00:00
-- url     : https://prove2.me/theorems/fe1cbe6c-92bf-4b3e-ad0e-ae494e028e03
-- title:
--   The unitary of a gate list (gates act right to left)
-- statement:
--   A circuit is a finite list of gates $g_1,\dots,g_k$, applied in this order. Following the convention that circuit gates act from right to left, its unitary is
--   $$
--   U = U(g_k)\cdots U(g_2)\,U(g_1).
--   $$
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 4.1, p.6

import Mathlib
import Definitions.Def_CutRankSched_Supplement_Gate_unitary

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The unitary of a circuit given as a list of gates (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §4.1, p.6: "circuit gates act from
right to left"): the **first** gate of the list acts first, so `[g₁, …, g_k]` has unitary
`U(g_k) ⋯ U(g₁)`. -/
noncomputable def circuitUnitary {m : ℕ} (c : List (Gate m)) : Op m :=
  c.foldl (fun U g => g.unitary * U) 1

end Supplement

end CutRankSched


