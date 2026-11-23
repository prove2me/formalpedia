-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:16.796265+00:00
-- url     : https://prove2.me/theorems/3d9bc233-34b3-4bc1-9286-d49c7363ce48
-- title:
--   Continuous Completion Map
-- statement:
--   Definitions and structural lemmas for Continuous Completion Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/ContinuousCompletionMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField
noncomputable section
namespace SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) in

abbrev PlacesOver (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}
instance (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) : w.1.asIdeal.LiesOver v.asIdeal :=
  w.2
variable (L) in

def placesOverEquiv (v : HeightOneSpectrum (𝓞 K)) :
    PlacesOver L v ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun P := ⟨⟨P.1, P.2.1, (have := P.2.2; Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1)⟩, P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance (v : HeightOneSpectrum (𝓞 K)) : Fintype (PlacesOver L v) :=
  Fintype.ofEquiv _ (placesOverEquiv L v).symm
section Map
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom
theorem continuous_completionMap : Continuous (completionMap v w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)
theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map _
      ((algebraMap K (WithVal (v.valuation K)) x : WithVal _) :
        UniformSpace.Completion (WithVal (v.valuation K))) =
    ((algebraMap K (WithVal (w.valuation L)) x : WithVal _) :
        UniformSpace.Completion (WithVal (w.valuation L)))
  rw [UniformSpace.Completion.map_coe
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w)]
  rfl
scoped instance algebraCompletion : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra
scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ (completionMap_algebraMap v w x).symm
scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := ((continuous_completionMap v w).comp continuous_fst).mul continuous_snd
end Map
end SemiLocal
end
end GroundTheory.Global


