-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
-- name    : GroundTheory_PAdicHodge_FontaineLemmaAInf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:51.783689+00:00
-- url     : https://prove2.me/theorems/b09e42b3-8bdb-48a0-8211-4213f290b48a
-- title:
--   Fontaine Lemma AInf
-- statement:
--   Definitions and structural lemmas for Fontaine Lemma AInf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
namespace AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
variable (K p) in

noncomputable def kerThetaFrob : Ideal (AInf K p) :=
  ⨅ n : ℕ, RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ ^ n : AInf K p ≃+* AInf K p) : AInf K p →+* AInf K p))
end AInf
end GroundTheory.PAdicHodge


