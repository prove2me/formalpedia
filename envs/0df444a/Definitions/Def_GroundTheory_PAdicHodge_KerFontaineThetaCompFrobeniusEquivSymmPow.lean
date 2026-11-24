-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
-- name    : GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:51.244793+00:00
-- url     : https://prove2.me/theorems/7ccf2ab8-bea2-4752-9571-c9bce5b209b6
-- title:
--   Ker Fontaine Theta Comp Frobenius Equiv Symm Pow
-- statement:
--   Definitions and structural lemmas for Ker Fontaine Theta Comp Frobenius Equiv Symm Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_wittVector_preTilt

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
namespace GroundTheory.PAdicHodge
open WittVector
section WittGeneral
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
def WittVector.teichmullerSeries (a : ℕ → R) : WittVector p R :=
  WittVector.mk p fun n => a n ^ p ^ n
variable [PerfectRing R p]
end WittGeneral
section Frobenius
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
end Frobenius
abbrev AInf (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] :=
  WittVector p (PreTilt (normInteger K) p)
namespace AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
variable (K p) in

instance isDomain : IsDomain (AInf K p) :=
  IsPerfectoidField.isDomain_wittVector_preTilt K p
end AInf
end GroundTheory.PAdicHodge


