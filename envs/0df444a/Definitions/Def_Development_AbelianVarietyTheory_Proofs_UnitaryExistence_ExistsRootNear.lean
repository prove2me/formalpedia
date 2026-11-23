-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:09.511291+00:00
-- url     : https://prove2.me/theorems/a307b949-2730-496f-941b-eda8cc85b0e7
-- title:
--   Exists Root Near
-- statement:
--   Definitions and structural lemmas for Exists Root Near, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
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
noncomputable section
namespace GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def incl : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := (⟨fun v => (a v : v.adicCompletion F), Filter.Eventually.of_forall fun v => (a v).2⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
omit [NumberField E] in
theorem tmul_mem (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : 𝓞 E) :
    a ⊗ₜ[F] (algebraMap (𝓞 E) E x) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
  AddSubgroup.subset_closure ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
omit [NumberField E] in
theorem mul_mem_hat {a b : RA F E} (ha : a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hb : b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) : a * b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  induction ha, hb using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    obtain ⟨b, hb, _, ⟨t, rfl⟩, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
    exact tmul_mem F E (a * b) (fun v => (v.adicCompletionIntegers F).mul_mem _ _ (ha v) (hb v)) (s * t)
  | zero_left x hx => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | zero_right x hx => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
  | neg_left x y _ _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
  | neg_right x y _ _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h
def intHat : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  neg_mem' := AddSubgroup.neg_mem _
  one_mem' := by
    have := tmul_mem F E 1 (fun v => one_mem _) 1
    rw [map_one] at this
    exact this
  mul_mem' := mul_mem_hat F E
def inclHat : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* intHat F E :=
  ((Algebra.TensorProduct.includeLeftRingHom : FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict
    (intHat F E) (fun a => by
      have := tmul_mem F E (incl F a) (fun v => (a v).2) 1
      rw [map_one] at this
      exact this)
def ratHat : 𝓞 E →+* intHat F E :=
  ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict
    (intHat F E) (fun x => tmul_mem F E 1 (fun v => one_mem _) x)
end GlobalTheory.AdLat.RootNear


