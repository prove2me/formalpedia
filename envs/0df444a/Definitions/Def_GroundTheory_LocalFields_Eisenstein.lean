-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Eisenstein
-- name    : GroundTheory_LocalFields_Eisenstein
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:28.643107+00:00
-- url     : https://prove2.me/theorems/50550f43-7141-43a7-9afb-172da91b27c0
-- title:
--   Eisenstein
-- statement:
--   Definitions and structural lemmas for Eisenstein, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
section DVR
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
end DVR
section Local
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end Local
section DVR2
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
end DVR2
section Forward
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end Forward
section TotallyRamified
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end TotallyRamified
section Eisenstein
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
theorem isUnit_leadingCoeff_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : IsUnit f.leadingCoeff :=
  IsLocalRing.notMem_maximalIdeal.mp hf.leading
variable [Field L] [Algebra K L]
theorem isIntegral_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    IsIntegral 𝒪[K] α := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_of_isEisensteinAt hf
  refine ⟨C (↑u⁻¹ : 𝒪[K]) * f, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp), ?_⟩
  rw [← aeval_def, map_mul, hα, mul_zero]
end Eisenstein
section Root
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}
theorem mem_integer_of_isEisensteinAt (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    {α : L} (hα : aeval α f = 0) : α ∈ 𝒪[L] :=
  (isIntegral_iff K L α).mp (isIntegral_of_isEisensteinAt hf hα)
variable (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hn hα
section Generated
variable (hgen : K⟮α⟯ = ⊤)
include hgen
end Generated
end Root
section AdjoinRoot
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]} (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hα
include hn
end AdjoinRoot
section Converse
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ
end Converse
end GroundTheory.LocalField


