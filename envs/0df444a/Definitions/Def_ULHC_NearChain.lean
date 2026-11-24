-- Prove2me | Definitions.Def_ULHC_NearChain
-- name    : ULHC_NearChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:58:52.94663+00:00
-- url     : https://prove2.me/theorems/9a46fdce-8c4d-4d2a-9194-580457e5ccde
-- title:
--   Near Chain
-- statement:
--   Definitions and structural lemmas for Near Chain, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean

import Definitions.Def_ULHC_NearGeo
set_option autoImplicit true
namespace ULHC
open Finset
section chain
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
end chain
section suffix
def suf (z : StripSpec) (i : ℕ) : StripSpec := ⟨cellJ z.c z.s i, z.s, z.n - i⟩
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}
end suffix
end ULHC


