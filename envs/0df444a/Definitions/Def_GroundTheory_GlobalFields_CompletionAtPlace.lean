-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
-- name    : GroundTheory_GlobalFields_CompletionAtPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:26.614813+00:00
-- url     : https://prove2.me/theorems/f180bfc4-39a4-4073-8ef1-3b7fda10224d
-- title:
--   Completion At Place
-- statement:
--   Definitions and structural lemmas for Completion At Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_LocalFields_Interface
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
namespace GroundTheory.Global
section Map
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
def adicCompletionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)
theorem continuous_adicCompletionMap : Continuous (adicCompletionMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)
theorem adicCompletionMap_algebraMap (x : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom _
    (uniformContinuous_algebraMap_liesOver K L v w).continuous
    ((algebraMap K (WithVal (v.valuation K)) x : WithVal (v.valuation K)) :
      UniformSpace.Completion (WithVal (v.valuation K))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl
end Map
namespace AdicLiesOver
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionMap v w).toAlgebra
theorem algebraMap_eq : algebraMap (v.adicCompletion K) (w.adicCompletion L) =
    adicCompletionMap v w :=
  rfl
scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_eq, adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L]
scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  continuousSMul_of_algebraMap _ _ (continuous_adicCompletionMap v w)
end AdicLiesOver
section Extension
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
theorem valued_algebraMap_adicCompletion' [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he]
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy : Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) ≠ 0 := by
    simpa using hx
  have h1 := Valued.locally_const hx'
  have h2 := (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).continuousAt.preimage_mem_nhds
    (Valued.locally_const hy)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' v]
  exact (valuation_liesOver L v w k).symm
instance valuativeExtension_adicCompletion [w.asIdeal.LiesOver v.asIdeal] :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle a b := by
    have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
    rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)),
      valued_algebraMap_adicCompletion', valued_algebraMap_adicCompletion']
    exact pow_le_pow_iff_left₀ zero_le zero_le he
end Extension
section Check
open AdicLiesOver
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
example : ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) := inferInstance
example : Module.Finite (v.adicCompletion K) (w.adicCompletion L) := inferInstance
end Check
end GroundTheory.Global


