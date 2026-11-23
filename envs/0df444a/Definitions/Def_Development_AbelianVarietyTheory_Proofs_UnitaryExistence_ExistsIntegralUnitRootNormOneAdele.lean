-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:24.775478+00:00
-- url     : https://prove2.me/theorems/9bcda0f8-ad04-4727-9070-2bfdfbac7919
-- title:
--   Exists Integral Unit Root Norm One Adele
-- statement:
--   Definitions and structural lemmas for Exists Integral Unit Root Norm One Adele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_galoisAut_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
namespace GlobalTheory.AdLat.UnitRoot
section quad
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end quad
section inst
variable (F : Type) [Field F] [NumberField F]
abbrev IntAd : Type := ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F
noncomputable def incl : IntAd F →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := ⟨fun v => a v, Filter.Eventually.of_forall fun v => (a v).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
noncomputable def primeAt (v : HeightOneSpectrum (𝓞 F)) : Ideal (IntAd F) :=
  (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).comap
    (Pi.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) v)
variable (E : Type) [Field E] [NumberField E] [Algebra F E]
noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' hx hy := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩) hx hy
open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
variable (F : Type) [Field F] [NumberField F] in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.UnitRoot.mem_hatRing (z : _root_.GlobalTheory.AdLat.RA F E) :
    z ∈ _root_.GlobalTheory.AdLat.UnitRoot.hatRing F E ↔
      z ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := Iff.rfl
variable {F E}
open NumberField IsDedekindDomain in
open scoped TensorProduct Topology Matrix in
variable (F : Type) [Field F] [NumberField F] in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in
variable {F E} in
theorem _root_.GlobalTheory.AdLat.UnitRoot.conj_mem (c : E ≃ₐ[F] E) :
    ∀ x ∈ Set.range (algebraMap (𝓞 E) E), c x ∈ Set.range (algebraMap (𝓞 E) E) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨c (a : E), a.2.map c.toAlgHom.toRingHom.toIntAlgHom⟩, rfl⟩
variable (F E) in

noncomputable def adIn : IntAd F →+* hatRing F E :=
  ((Algebra.TensorProduct.includeLeftRingHom :
    FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict (hatRing F E)
    fun a => (mem_hatRing F E _).2 (tmul_mem_adelicCompletion_of_integral F (a := incl F a) (x := 1)
      (fun v => (a v).2) ⟨1, map_one _⟩)
noncomputable def conjHat (c : E ≃ₐ[F] E) : hatRing F E →+* hatRing F E :=
  ((sg (FiniteAdeleRing (𝓞 F) F) c : RA F E →+* RA F E).comp (hatRing F E).subtype).codRestrict _
    fun z => galoisAut_mem_adelicCompletionOfElementSet F c (conj_mem c) z.2
variable (F E) in

noncomputable def intIn : 𝓞 E →+* hatRing F E :=
  ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E) :
    E →+* RA F E).comp (algebraMap (𝓞 E) E)).codRestrict _
    fun a => one_tmul_mem_adelicCompletionOfElementSet F ⟨a, rfl⟩
end inst
end GlobalTheory.AdLat.UnitRoot
namespace GlobalTheory.AdLat
open UnitRoot
end GlobalTheory.AdLat


