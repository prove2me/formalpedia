-- Prove2me | Definitions.Def_ULHC_Touch
-- name    : ULHC_Touch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:57:19.999193+00:00
-- url     : https://prove2.me/theorems/b2eeb907-0903-45b0-a54d-b9ed381cc813
-- title:
--   Touch
-- statement:
--   Definitions and structural lemmas for Touch, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean

import Definitions.Def_ULHC_Near
set_option autoImplicit true
namespace ULHC
open Finset
section frames
variable (d : Pt) (s : Side)
end frames
def SigFrom (F : Finset Edge) (z : Pt) (tf : Side) (m i0 : ℕ) : Prop :=
  ∀ i, i0 ≤ i → i < m →
    (lat1 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧ (lat2 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧
      (back (cellJ z tf i) tf ∈ F ↔ i % 2 = 0) ∧
      (front (cellJ z tf i) tf ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m))
section touch
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
end touch
end ULHC


