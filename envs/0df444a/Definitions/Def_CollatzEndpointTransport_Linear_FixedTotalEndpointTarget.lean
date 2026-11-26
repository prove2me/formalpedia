-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
-- name    : CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:58:24.083562+00:00
-- url     : https://prove2.me/theorems/819965e0-46e5-5941-ad0e-7d82909a3d90
-- title:
--   Fixed Total Endpoint Target
-- statement:
--   Definitions and structural lemmas for Fixed Total Endpoint Target, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointTarget.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def actualLevelBadEndpointSet
    (S : Set ℕ) (M s : ℕ) : Finset ℕ := by
  classical
  exact (actualLevelEndpointSet M s).filter fun y => y ∉ S
def actualLevelBadMass
    (S : Set ℕ) (M s : ℕ) : ℕ := by
  classical
  exact ∑ y ∈ actualLevelEndpointSet M s,
    if y ∉ S then actualLevelFiberCard M s y else 0
def sourceLevelBadSet
    (S : Set ℕ) (M s : ℕ) : Finset (SourceCode M) := by
  classical
  exact (sourceOddLevel M s).filter fun x => sourceEndpoint x ∉ S
end
end FixedTotal
end CollatzEndpointTransport


