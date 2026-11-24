-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_AInfXi
-- name    : GroundTheory_PAdicHodge_AInfXi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:21.672978+00:00
-- url     : https://prove2.me/theorems/63d7c359-ebf0-40b2-b22d-e8f4425ba5f5
-- title:
--   AInf Xi
-- statement:
--   Definitions and structural lemmas for AInf Xi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean

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
open WittVector
namespace GroundTheory.PAdicHodge
section RootsOfUnity
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
end RootsOfUnity
namespace AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
def mu (ε : 𝒪♭) : AInf K p := teichmuller p ε - 1
def xi (ε : 𝒪♭) : AInf K p := ∑ i ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ^ i
end AInf
end GroundTheory.PAdicHodge


