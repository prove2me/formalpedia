-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:32.683046+00:00
-- url     : https://prove2.me/theorems/5b76bad2-31aa-4d06-b7b9-bb2d4947cda5
-- title:
--   Relabel Transport
-- statement:
--   Definitions and structural lemmas for Relabel Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
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
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
section Blocks
end Blocks
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
def vars : (Σ k, ι k) ≃ (Σ k', ι' k') :=
  Equiv.sigmaCongr e h
variable (F) in

def ringEquiv : MRingOver F ι ≃+* MRingOver F ι' :=
  (renameEquiv F (vars e h)).toRingEquiv
def pullFamily (I : IFamily F ι) : IFamily F ι' :=
  fun W n L => I (W.comap (ringEquiv F e h)) n fun j => L j ∘ e
def pushFamily (I' : IFamily F ι') : IFamily F ι :=
  fun W n L => I' (W.map (ringEquiv F e h)) n fun j => L j ∘ e.symm
end GroundTheory.Heights₂.Heights.Targets.Relabel


