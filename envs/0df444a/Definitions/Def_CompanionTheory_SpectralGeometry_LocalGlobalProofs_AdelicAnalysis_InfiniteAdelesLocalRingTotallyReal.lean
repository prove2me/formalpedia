-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:10.911157+00:00
-- url     : https://prove2.me/theorems/b9f54030-edc9-4456-8bc9-0b247d7bae9a
-- title:
--   Infinite Adeles Local Ring Totally Real
-- statement:
--   Definitions and structural lemmas for Infinite Adeles Local Ring Totally Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.LocInf
def posU (ι : Type) : Subgroup (ι → ℝ)ˣ where
  carrier := {u | ∀ i, 0 < (u : ι → ℝ) i}
  mul_mem' := fun {a b} ha hb i => by
    simpa using mul_pos (ha i) (hb i)
  one_mem' := fun i => by simp
  inv_mem' := by
    intro u hu i
    have h1 : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i * (u : ι → ℝ) i = 1 := by
      have := congrFun (u.inv_mul) i
      simpa using this
    exact (pos_iff_pos_of_mul_pos (h1 ▸ one_pos)).2 (hu i)
variable (F : Type) [Field F] [NumberField F]
def eInf (h : IsTotallyReal F) : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)
omit [NumberField F] in
theorem continuous_eInf (h : IsTotallyReal F) : Continuous (eInf F h) := by
  show Continuous (fun (x : ∀ w : InfinitePlace F, w.Completion) (w : InfinitePlace F) =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w) (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).continuous.comp (continuous_apply w)
omit [NumberField F] in
theorem continuous_eInf_symm (h : IsTotallyReal F) : Continuous (eInf F h).symm := by
  show Continuous (fun (x : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)).symm (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).symm.continuous.comp (continuous_apply w)
def hInf (h : IsTotallyReal F) : Ainf F ≃ₜ (InfinitePlace F → ℝ) where
  toEquiv := (eInf F h).toEquiv
  continuous_toFun := continuous_eInf F h
  continuous_invFun := continuous_eInf_symm F h
def uInf (h : IsTotallyReal F) : (Ainf F)ˣ ≃ₜ (InfinitePlace F → ℝ)ˣ where
  toEquiv := (Units.mapEquiv (eInf F h).toMulEquiv).toEquiv
  continuous_toFun := Continuous.units_map _ (continuous_eInf F h)
  continuous_invFun := Continuous.units_map _ (continuous_eInf_symm F h)
end GlobalTheory.CompanionTheory.SW.LocInf


