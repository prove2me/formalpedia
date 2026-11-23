-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
-- name    : Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:56.722369+00:00
-- url     : https://prove2.me/theorems/c5785da8-6f90-45fd-9bcf-5116d5590bc1
-- title:
--   Deg One Iff Surjective
-- statement:
--   Definitions and structural lemmas for Deg One Iff Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeSplit
open NumberField IsDedekindDomain HeckeValGen
variable (L : Type) [Field L] [NumberField L]
def IsHeckeChar (χ : Ideles L →* ℂˣ) : Prop := Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1
def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
def infPart : Ideles L →* (InfiniteAdeleRing L)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
def finPart (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => (x.2 : FiniteAdeleRing (𝓞 L) L) v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
variable {L}
def TrivAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, χ (localIdele L v x) = 1
def UnrAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, Valued.v (x : v.adicCompletion L) = 1 → χ (localIdele L v x) = 1
def DegOne (F : Type) [Field F] [NumberField F] [Algebra F L] (w : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ y : 𝓞 L, ∃ u : 𝓞 F, y - algebraMap (𝓞 F) (𝓞 L) u ∈ w.asIdeal
variable (L)
variable {L}
end GlobalTheory.HeckeSplit


