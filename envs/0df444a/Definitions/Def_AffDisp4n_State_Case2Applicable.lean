-- Prove2me | Definitions.Def_AffDisp4n_State_Case2Applicable
-- name    : AffDisp4n_State_Case2Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:30.965463+00:00
-- url     : https://prove2.me/theorems/7147c527-78cc-4e62-9c15-1d1bd7a92e75
-- title:
--   Case 2 applies
-- statement:
--   **Case 2 applies** if two partners have the same child: there is a pair $\{p, r\} \in P$ and an equation that mentions both $p$ and $r$, or a gate that reads both.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.22

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **Case 2 applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1 "Case 2: two partners have the same child", p.22): some pair
`{p, r} ∈ P` has a common child, an equation that mentions both or a gate that reads both. -/
def State.Case2Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ p r : Fin σ.m, s(p, r) ∈ σ.P ∧
    ((∃ i : Fin σ.r, σ.N i p ≠ 0 ∧ σ.N i r ≠ 0) ∨
      ∃ g : Fin σ.circ.size, σ.circ.Reads g (.inl p) ∧ σ.circ.Reads g (.inl r))

end AffDisp4n


