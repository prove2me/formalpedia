-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
-- name    : GroundTheory_PAdicHodge_AInfTopology
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:11.072475+00:00
-- url     : https://prove2.me/theorems/0b79412b-2f45-4482-a95f-b6303dc67a77
-- title:
--   AInf Topology
-- statement:
--   Definitions and structural lemmas for AInf Topology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open WittVector Filter Topology
namespace GroundTheory.PAdicHodge
section Coordinates
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
end Coordinates
namespace AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
variable (K p) in

@[instance_reducible]
def pAdicTopology : TopologicalSpace (AInf K p) :=
  (Ideal.span {(p : AInf K p)}).adicTopology
@[instance_reducible]
def teichmullerAdicTopology (ϖ : 𝒪♭) : TopologicalSpace (AInf K p) :=
  (Ideal.span {teichmuller p ϖ}).adicTopology
variable (K p) in

@[instance_reducible]
def weakTopology : TopologicalSpace (AInf K p) :=
  TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
end AInf
end GroundTheory.PAdicHodge


