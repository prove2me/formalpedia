-- Prove2me | Definitions.Def_AffDisp4n_State_D3Applicable
-- name    : AffDisp4n_State_D3Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:49.263816+00:00
-- url     : https://prove2.me/theorems/a3aaf278-1935-43d7-b8c5-f38cfa787680
-- title:
--   Deletion (D3) applies
-- statement:
--   **Deletion (D3) applies** to a state if some equation of the affine system has at most two nonconstant terms, i.e. its row of $(A \mid N)$ has at most two nonzero entries.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, p.20

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **(D3) applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1 "D3: deleting an equation with at most two nonconstant terms", p.20):
some equation of the affine system has at most two nonconstant terms, i.e. its row of `(A | N)` has
at most two nonzero entries. -/
def State.D3Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ i : Fin σ.r, Nat.card {k : Fin σ.r // σ.A i k ≠ 0} + Nat.card {y : Fin σ.m // σ.N i y ≠ 0} ≤ 2

end AffDisp4n


