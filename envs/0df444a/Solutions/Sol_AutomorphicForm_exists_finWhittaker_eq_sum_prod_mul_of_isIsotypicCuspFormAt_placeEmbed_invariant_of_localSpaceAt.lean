-- Prove2me | solution 1 for AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4d13c2f4-abb4-5167-ace1-59dd83e48562

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws23Slot

open AdelicDock UnramifiedWhittaker

abbrev G : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev 𝔸f : Type := FiniteAdeleRing (𝓞 ℚ) ℚ
abbrev Gp (p : HeightOneSpectrum (𝓞 ℚ)) : Type := GL (Fin 2) (p.adicCompletion ℚ)

theorem ext_arch_fin {g h : G} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_)
  · exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha
  · exact congrArg (fun u : GL (Fin 2) 𝔸f => (u : Matrix (Fin 2) (Fin 2) 𝔸f)) hf

theorem ext_finComponent {g h : GL (Fin 2) 𝔸f}
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v h) : g = h := by
  refine Units.ext (matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun v => ?_)
  exact congrArg (fun u : Gp v => (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) (hv v)

theorem localAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : G) :
    localAt ℚ p g = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) := rfl

@[scoped simp] theorem glFin_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) :
    glFin (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = localEmbed (𝓞 ℚ) ℚ p x :=
  glFin_finEmbed (𝓞 ℚ) ℚ _

@[scoped simp] theorem glArch_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) :
    glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = 1 :=
  glArch_finEmbed (𝓞 ℚ) ℚ _

@[scoped simp] theorem localAt_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) :
    localAt ℚ p (placeEmbed ℚ p x) = x := by
  rw [localAt_apply, glFin_placeEmbed, finComponent_localEmbed_self]

theorem finComponent_placeEmbed_of_ne (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) {q : HeightOneSpectrum (𝓞 ℚ)}
    (hq : q ≠ p) : finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (placeEmbed ℚ p x)) = 1 := by
  rw [glFin_placeEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem localAt_placeEmbed_of_ne (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) {q : HeightOneSpectrum (𝓞 ℚ)}
    (hq : q ≠ p) : localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  rw [localAt_apply, finComponent_placeEmbed_of_ne p x hq]

theorem placeEmbed_mul_comm_of_localAt_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) (g : G)
    (hg : localAt ℚ p g = 1) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  refine ext_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_placeEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul]
    refine ext_finComponent fun v => ?_
    rw [map_mul, map_mul]
    by_cases hv : v = p
    · subst hv
      rw [← localAt_apply, ← localAt_apply, hg, localAt_placeEmbed, one_mul, mul_one]
    · rw [finComponent_placeEmbed_of_ne p x hv, one_mul, mul_one]

theorem placeEmbed_mul_comm_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hpq : p ≠ q) (x : Gp p) (y : Gp q) :
    placeEmbed ℚ p x * placeEmbed ℚ q y = placeEmbed ℚ q y * placeEmbed ℚ p x :=
  placeEmbed_mul_comm_of_localAt_eq_one p x _ (localAt_placeEmbed_of_ne q y hpq)

theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one (a b : G) (ha : glFin (𝓞 ℚ) ℚ a = 1)
    (hb : glArch (𝓞 ℚ) ℚ b = 1) : a * b = b * a := by
  refine ext_arch_fin ?_ ?_
  · rw [map_mul, map_mul, hb, mul_one, one_mul]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

theorem unipotentGL2_mul_placeEmbed_comm (p : HeightOneSpectrum (𝓞 ℚ)) (t : 𝔸) (ht : localAt ℚ p (unipotentGL2 t) = 1)
    (x : Gp p) : unipotentGL2 t * placeEmbed ℚ p x = placeEmbed ℚ p x * unipotentGL2 t :=
  (placeEmbed_mul_comm_of_localAt_eq_one p x _ ht).symm

open scoped Classical

section Strip

def strip (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : G) : G :=
  g * (T.toList.map fun q => placeEmbed ℚ q (localAt ℚ q g)⁻¹).prod

def IsSupportedOn (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (e : G) : Prop :=
  glArch (𝓞 ℚ) ℚ e = 1 ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ T → localAt ℚ q e = 1

def sliceClass (W : G → ℂ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {F | ∃ e : G, IsSupportedOn T e ∧ F = fun g => W (e * strip T g)}

end Strip

section StripAPI

variable (T : Finset (HeightOneSpectrum (𝓞 ℚ)))

theorem ext_of_glArch_of_localAt {g h : G} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v g = localAt ℚ v h) : g = h :=
  ext_arch_fin ha (ext_finComponent fun v => hv v)

theorem localAt_stripFactor (g : G) (v : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ v ((T.toList.map fun q => placeEmbed ℚ q (localAt ℚ q g)⁻¹).prod) =
      if v ∈ T then (localAt ℚ v g)⁻¹ else 1 := by
  rw [map_list_prod, List.map_map]
  have h := List.prod_map_eq_pow_single v (fun q => localAt ℚ v (placeEmbed ℚ q (localAt ℚ q g)⁻¹))
    (l := T.toList) (fun q hq _ => localAt_placeEmbed_of_ne q _ (Ne.symm hq))
  rw [show ((fun q => localAt ℚ v (placeEmbed ℚ q (localAt ℚ q g)⁻¹)) : HeightOneSpectrum (𝓞 ℚ) → Gp v) =
      (⇑(localAt ℚ v) ∘ fun q => placeEmbed ℚ q (localAt ℚ q g)⁻¹) from rfl] at h
  rw [h]
  try rw [Function.comp_apply]
  rw [localAt_placeEmbed]
  by_cases hv : v ∈ T
  · rw [if_pos hv, List.count_eq_one_of_mem (Finset.nodup_toList T) (Finset.mem_toList.2 hv), pow_one]
  · rw [if_neg hv, List.count_eq_zero_of_not_mem (fun h => hv (Finset.mem_toList.1 h)), pow_zero]

theorem glArch_stripFactor (g : G) :
    glArch (𝓞 ℚ) ℚ ((T.toList.map fun q => placeEmbed ℚ q (localAt ℚ q g)⁻¹).prod) = 1 := by
  rw [map_list_prod, List.map_map]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  exact glArch_placeEmbed q _

theorem glArch_strip (g : G) : glArch (𝓞 ℚ) ℚ (strip T g) = glArch (𝓞 ℚ) ℚ g := by
  rw [strip, map_mul, glArch_stripFactor, mul_one]

theorem localAt_strip_of_mem {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∈ T) (g : G) : localAt ℚ q (strip T g) = 1 := by
  rw [strip, map_mul, localAt_stripFactor, if_pos hq, mul_inv_cancel]

theorem localAt_strip_of_not_mem {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∉ T) (g : G) :
    localAt ℚ q (strip T g) = localAt ℚ q g := by
  rw [strip, map_mul, localAt_stripFactor, if_neg hq, mul_one]

theorem localAt_strip (q : HeightOneSpectrum (𝓞 ℚ)) (g : G) :
    localAt ℚ q (strip T g) = if q ∈ T then 1 else localAt ℚ q g := by
  by_cases hq : q ∈ T
  · rw [if_pos hq, localAt_strip_of_mem T hq]
  · rw [if_neg hq, localAt_strip_of_not_mem T hq]

theorem strip_mul (g h : G) : strip T (g * h) = strip T g * strip T h := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [map_mul, glArch_strip, glArch_strip, glArch_strip, map_mul]
  · rw [map_mul, localAt_strip, localAt_strip, localAt_strip]
    by_cases hv : v ∈ T
    · simp only [if_pos hv, mul_one]
    · simp only [if_neg hv, map_mul]

theorem strip_one : strip T 1 = 1 := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [glArch_strip]
  · rw [localAt_strip]; by_cases hv : v ∈ T <;> simp [hv]

theorem strip_placeEmbed_of_mem {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∈ T) (x : Gp q) : strip T (placeEmbed ℚ q x) = 1 := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [glArch_strip, glArch_placeEmbed, map_one]
  · rw [localAt_strip, map_one]
    by_cases hv : v ∈ T
    · rw [if_pos hv]
    · rw [if_neg hv, localAt_placeEmbed_of_ne q x (by rintro rfl; exact hv hq)]

theorem strip_eq_self_of_forall_localAt_eq_one (g : G) (hg : ∀ q ∈ T, localAt ℚ q g = 1) : strip T g = g := by
  refine ext_of_glArch_of_localAt (glArch_strip T g) fun v => ?_
  rw [localAt_strip]
  by_cases hv : v ∈ T
  · rw [if_pos hv, hg v hv]
  · rw [if_neg hv]

theorem strip_empty (g : G) : strip ∅ g = g :=
  strip_eq_self_of_forall_localAt_eq_one ∅ g fun q hq => absurd hq (Finset.notMem_empty q)

theorem strip_insert {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ T) (g : G) :
    strip (insert p T) g = strip ({p} : Finset _) (strip T g) := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [glArch_strip, glArch_strip, glArch_strip]
  · rw [localAt_strip, localAt_strip, localAt_strip]
    by_cases hvp : v = p
    · subst hvp; simp
    · by_cases hv : v ∈ T
      · simp [hv, hvp]
      · simp [hv, hvp]

theorem placeEmbed_localAt_mul_strip_singleton (p : HeightOneSpectrum (𝓞 ℚ)) (g : G) :
    placeEmbed ℚ p (localAt ℚ p g) * strip ({p} : Finset _) g = g := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [map_mul, glArch_placeEmbed, glArch_strip, one_mul]
  · rw [map_mul, localAt_strip]
    by_cases hvp : v = p
    · subst hvp; simp
    · rw [localAt_placeEmbed_of_ne p _ hvp, one_mul, if_neg (by simpa using hvp)]

theorem strip_singleton_eq (p : HeightOneSpectrum (𝓞 ℚ)) (g : G) :
    strip ({p} : Finset _) g = g * (placeEmbed ℚ p (localAt ℚ p g))⁻¹ := by
  rw [strip, Finset.toList_singleton, List.map_singleton, List.prod_singleton, map_inv]

theorem strip_strip (g : G) : strip T (strip T g) = strip T g :=
  strip_eq_self_of_forall_localAt_eq_one T _ fun q hq => localAt_strip_of_mem T hq g

theorem strip_strip_comm (T' : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : G) : strip T (strip T' g) = strip T' (strip T g) := by
  refine ext_of_glArch_of_localAt (by rw [glArch_strip, glArch_strip, glArch_strip, glArch_strip]) fun v => ?_
  simp only [localAt_strip]
  split_ifs <;> rfl

theorem isSupportedOn_one : IsSupportedOn T 1 :=
  ⟨map_one _, fun q _ => map_one _⟩

theorem IsSupportedOn.mul {e e' : G} (he : IsSupportedOn T e) (he' : IsSupportedOn T e') : IsSupportedOn T (e * e') :=
  ⟨by rw [map_mul, he.1, he'.1, mul_one], fun q hq => by rw [map_mul, he.2 q hq, he'.2 q hq, mul_one]⟩

theorem IsSupportedOn.mono {T' : Finset (HeightOneSpectrum (𝓞 ℚ))} (h : T ⊆ T') {e : G} (he : IsSupportedOn T e) :
    IsSupportedOn T' e :=
  ⟨he.1, fun q hq => he.2 q fun hqT => hq (h hqT)⟩

theorem isSupportedOn_placeEmbed {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∈ T) (x : Gp q) : IsSupportedOn T (placeEmbed ℚ q x) :=
  ⟨glArch_placeEmbed q x, fun q' hq' => localAt_placeEmbed_of_ne q x fun h => hq' (h ▸ hq)⟩

theorem IsSupportedOn.mul_comm_of_forall_localAt_eq_one {e : G} (he : IsSupportedOn T e) (g : G)
    (hg : ∀ q ∈ T, localAt ℚ q g = 1) : e * g = g * e := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [map_mul, map_mul, he.1, one_mul, mul_one]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ T
    · rw [hg v hv, one_mul, mul_one]
    · rw [he.2 v hv, one_mul, mul_one]

theorem IsSupportedOn.mul_placeEmbed_comm {e : G} (he : IsSupportedOn T e) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ T)
    (x : Gp p) : e * placeEmbed ℚ p x = placeEmbed ℚ p x * e :=
  he.mul_comm_of_forall_localAt_eq_one T _ fun q hq => localAt_placeEmbed_of_ne p x fun h => hp (h ▸ hq)

theorem mem_sliceClass_self (W : G → ℂ) : W ∈ sliceClass W ∅ := by
  refine Submodule.subset_span ⟨1, isSupportedOn_one ∅, ?_⟩
  funext g; rw [strip_empty, one_mul]

theorem mem_sliceClass_generator (W : G → ℂ) {e : G} (he : IsSupportedOn T e) :
    (fun g => W (e * strip T g)) ∈ sliceClass W T :=
  Submodule.subset_span ⟨e, he, rfl⟩

theorem sliceClass_placeEmbed_invariant {W : G → ℂ} {F : G → ℂ} (hF : F ∈ sliceClass W T)
    {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∈ T) (x : Gp q) (g : G) : F (g * placeEmbed ℚ q x) = F g := by
  induction hF using Submodule.span_induction generalizing g with
  | mem F hF =>
    obtain ⟨e, he, rfl⟩ := hF
    simp only [strip_mul, strip_placeEmbed_of_mem T hq, mul_one]
  | zero => rfl
  | add F₁ F₂ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂]
  | smul a F _ h => simp only [Pi.smul_apply, h]

end StripAPI

section Whittaker

open NumberField.StandardAddChar

abbrev Wφ (φ : G → ℂ) : G → ℂ := fun g => whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ 1 g

theorem productionPinsGeneral_eq :
    productionPinsGeneral ℚ = productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ) := rfl

theorem productionPinsGeneral_U (N : Ideal (𝓞 ℚ)) :
    (productionPinsGeneral ℚ).U N = levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ := rfl

theorem whittakerCoefficient_translate (pins : CarrierPins ℚ) (ψ : AddChar 𝔸 ℂ) (φ : G → ℂ) (α : ℚ) (h g : G) :
    whittakerCoefficient ℚ pins ψ (fun z => φ (z * h)) α g = whittakerCoefficient ℚ pins ψ φ α (g * h) := by
  simp only [whittakerCoefficient, mul_assoc]

theorem localFnAt_eq (pins : CarrierPins ℚ) (ψ : AddChar 𝔸 ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (φ : G → ℂ) (x : Gp p) :
    WhittakerModel.localFnAt ℚ pins ψ p φ x = whittakerCoefficient ℚ pins ψ φ 1 (placeEmbed ℚ p x) := rfl

theorem map_unipotentGL2' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 t) = unipotentGL2 (f t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem glArch_unipotentGL2 (t : 𝔸) : glArch (𝓞 ℚ) ℚ (unipotentGL2 t) = unipotentGL2 t.1 :=
  map_unipotentGL2' _ t

theorem localAt_unipotentGL2 (p : HeightOneSpectrum (𝓞 ℚ)) (t : 𝔸) : localAt ℚ p (unipotentGL2 t) = unipotentGL2 (t.2 p) := by
  rw [localAt_apply, glFin, map_unipotentGL2', finComponent, map_unipotentGL2']; rfl

theorem unipotent_eq_unipotentGL2 {K : Type*} [Field K] (x : K) : UnramifiedWhittaker.unipotent x = unipotentGL2 x :=
  Units.ext rfl

theorem globalPoints_unipotentGL2 (β : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) = unipotentGL2 (algebraMap ℚ 𝔸 β) :=
  map_unipotentGL2' _ β

theorem placeEmbed_unipotent (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) :
    placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) =
      unipotentGL2 (((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ p x) : 𝔸) := by
  refine ext_of_glArch_of_localAt ?_ fun v => ?_
  · rw [glArch_placeEmbed]
    erw [glArch_unipotentGL2]
    exact (unipotentGL2_zero).symm
  · erw [localAt_unipotentGL2]
    by_cases hv : v = p
    · subst hv; rw [localAt_placeEmbed, unipotent_eq_unipotentGL2]
      exact congrArg _ (finAdeleSingleAt_apply_self ℚ v x).symm
    · rw [localAt_placeEmbed_of_ne p _ hv]
      change (1 : Gp v) = unipotentGL2 (finAdeleSingleAt ℚ p x v)
      rw [finAdeleSingleAt_apply_of_ne ℚ p x hv, unipotentGL2_zero]

theorem psiQ_single (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) :
    psiQ (((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ p x) : 𝔸) = psiLocal ℚ p x := by
  rw [psiLocal_rat_eq_psiV, psiQ_apply, psiFin_apply, AddChar.map_zero_eq_one, one_mul]
  rw [finprod_eq_single (fun v => psiV v (finAdeleSingleAt ℚ p x v)) p fun v hv => by
    show psiV v (finAdeleSingleAt ℚ p x v) = 1
    rw [finAdeleSingleAt_apply_of_ne ℚ p x hv, AddChar.map_zero_eq_one]]
  show psiV p (finAdeleSingleAt ℚ p x p) = psiV p x
  rw [finAdeleSingleAt_apply_self]

variable (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
  {φ : G → ℂ} (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ)
include hiso

private theorem _root_.Ws23Slot.left_invariant (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : G) : φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g := by
  have h := hiso.smoothCusp.1.1
  letI := (productionPinsGeneral ℚ).mS
  exact ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 h).1.left_invariant γ g

p2m_export "Ws23Slot" "left_invariant"

theorem Wφ_unipotentGL2_mul (t : 𝔸) (g : G) : Wφ φ (unipotentGL2 t * g) = psiQ t * Wφ φ g := by
  have h := whittakerCoefficient_unipotentGL2_mul ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) psiQ
    (fun q => psiQ_algebraMap q) φ g (fun β u => by
      rw [unipotentGL2_add, ← globalPoints_unipotentGL2, mul_assoc, left_invariant Φ S R hiso]) 1 t
  simpa [Wφ, productionPinsGeneral_eq] using h

theorem continuous_Wφ : Continuous (Wφ φ) :=
  continuous_whittakerCoefficient ℚ _ _ _ psiQ continuous_psiQ φ hiso.continuous 1

theorem Wφ_mul_of_mem_U (g u : G) (hu : u ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ) :
    Wφ φ (g * u) = Wφ φ g := by
  show whittakerCoefficient _ _ _ _ _ _ = whittakerCoefficient _ _ _ _ _ _
  rw [← whittakerCoefficient_translate]
  congr 1; funext z
  exact hiso.level_invariant z u (by rw [productionPinsGeneral_U]; exact hu)

omit hiso in
theorem placeEmbed_mem_U_of_mem_localLevelOne (p : HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) {k : Gp p}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) :
    placeEmbed ℚ p k ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ :=
  ⟨(finEmbed_mem_levelOne_iff (𝓞 ℚ) ℚ _).2 ((localEmbed_mem_finiteLevelOne_iff (𝓞 ℚ) ℚ p k).2 hk),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).2 (glArch_placeEmbed p k)⟩

omit hiso in

theorem localSpaceAt_translate_stable (pins : CarrierPins ℚ) (ψ : AddChar 𝔸 ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (φ' : G → ℂ)
    {W : Gp p → ℂ} (hW : W ∈ WhittakerModel.localSpaceAt ℚ pins ψ p φ') (h : Gp p) :
    (fun g => W (g * h)) ∈ WhittakerModel.localSpaceAt ℚ pins ψ p φ' := by
  induction hW using Submodule.span_induction with
  | mem W hW =>
    obtain ⟨y, rfl⟩ := hW
    refine Submodule.subset_span ⟨placeEmbed ℚ p h * y, ?_⟩
    funext g
    rw [localFnAt_eq, localFnAt_eq, whittakerCoefficient_translate, whittakerCoefficient_translate, map_mul, mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul a W _ hW => exact Submodule.smul_mem _ a hW

theorem isPsiLocalWhittaker_of_mem_localSpaceAt (p : HeightOneSpectrum (𝓞 ℚ)) {W : Gp p → ℂ}
    (hW : W ∈ WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ) (x : p.adicCompletion ℚ) (g : Gp p) :
    W (UnramifiedWhittaker.unipotent x * g) = psiLocal ℚ p x * W g := by
  induction hW using Submodule.span_induction generalizing g with
  | mem W hW =>
    obtain ⟨y, rfl⟩ := hW
    rw [localFnAt_eq, localFnAt_eq, whittakerCoefficient_translate, whittakerCoefficient_translate, map_mul, mul_assoc,
      placeEmbed_unipotent, ← psiQ_single]
    exact Wφ_unipotentGL2_mul Φ S R hiso _ _
  | zero => simp
  | add W₁ W₂ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂, mul_add]
  | smul a W _ h => simp only [Pi.smul_apply, h, smul_eq_mul]; ring

end Whittaker

section Arch

open Matrix NumberField.InfinitePlace.Completion

abbrev w0 : InfinitePlace ℚ := default
theorem hw0 : (w0).IsReal := IsTotallyReal.isReal _
abbrev ιR : GL (Fin 2) ℝ →* G := archRealGLAt hw0

theorem iotaR_snd (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = (1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j := rfl

theorem glFin_iotaR (M : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (ιR M) = 1 :=
  Units.ext (Matrix.ext fun i j => iotaR_snd M i j)

theorem localAt_iotaR (p : HeightOneSpectrum (𝓞 ℚ)) (M : GL (Fin 2) ℝ) : localAt ℚ p (ιR M) = 1 := by
  rw [localAt_apply, glFin_iotaR, map_one]

theorem iotaR_mul_comm_of_mem {g : G} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) : ιR M * g = g * ιR M :=
  mul_comm_of_glFin_eq_one_of_glArch_eq_one _ _ (glFin_iotaR M) ((mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg)

theorem ratArchGL2_mul (g h : G) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_of_mem {g : G} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem ratArchGL2_apply (g : G) (i j : Fin 2) :
    ((ratArchGL2 g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ringEquivRealOfIsReal hw0 (((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) := rfl

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0 = (ringEquivRealOfIsReal hw0).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  show archMatrixUpdate ℚ w0 ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw0).symm M :
    GL (Fin 2) (w0).Completion) : Matrix _ _ _) i j w0 = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem ratArchGL2_iotaR (M : GL (Fin 2) ℝ) : ratArchGL2 (ιR M) = M := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratArchGL2_apply, iotaR_fst]
  exact (ringEquivRealOfIsReal hw0).apply_symm_apply _

theorem coe_finFactor (g : G) : (RSCarrier.finFactor g : G) = (ιR (ratArchGL2 g))⁻¹ * g := rfl

theorem finFactor_iotaR_mul {k : G} (hk : k ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) :
    (RSCarrier.finFactor (ιR M * k) : G) = k := by
  rw [coe_finFactor, ratArchGL2_mul, ratArchGL2_iotaR, ratArchGL2_of_mem hk, mul_one, ← mul_assoc,
    inv_mul_cancel, one_mul]

theorem finFactor_iotaR_mul' {k : G} (hk : k ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) :
    RSCarrier.finFactor (ιR M * k) = ⟨k, hk⟩ :=
  Subtype.ext (finFactor_iotaR_mul hk M)

theorem localAt_finFactor (p : HeightOneSpectrum (𝓞 ℚ)) (g : G) : localAt ℚ p (RSCarrier.finFactor g : G) = localAt ℚ p g := by
  rw [coe_finFactor, map_mul, map_inv, localAt_iotaR, inv_one, one_mul]

theorem finFactor_mul_of_mem (g : G) {k : G} (hk : k ∈ finiteAdelicGL2Subgroup ℚ) :
    (RSCarrier.finFactor (g * k) : G) = RSCarrier.finFactor g * k := by
  rw [coe_finFactor, coe_finFactor, ratArchGL2_mul, ratArchGL2_of_mem hk, mul_one, mul_assoc]

theorem finFactor_mul_of_mem_left (g : G) {k : G} (hk : k ∈ finiteAdelicGL2Subgroup ℚ) :
    (RSCarrier.finFactor (k * g) : G) = k * RSCarrier.finFactor g := by
  rw [coe_finFactor, coe_finFactor, ratArchGL2_mul, ratArchGL2_of_mem hk, one_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  have h := iotaR_mul_comm_of_mem hk (ratArchGL2 g)⁻¹
  rw [map_inv] at h
  exact h

theorem placeEmbed_mem_fin (p : HeightOneSpectrum (𝓞 ℚ)) (x : Gp p) : placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).2 (glArch_placeEmbed p x)

theorem unipotentGL2_mem_fin {t : 𝔸} (ht : t.1 = 0) : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  erw [glArch_unipotentGL2]
  rw [ht, unipotentGL2_zero]

end Arch

section Continuity

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

open scoped Classical in

theorem continuous_splice (a : FiniteAdeleRing R K) : Continuous (splice R K v a) := by
  let S : Set (HeightOneSpectrum R) := {w | w ≠ v ∧ a w ∈ w.adicCompletionIntegers K}
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    refine (((Filter.eventually_cofinite.1 a.2)).union (Set.finite_singleton v)).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or, not_not] at h
    exact hw ⟨h.2, h.1⟩
  let f₀ : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum R => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal S) :=
    fun t => ⟨Function.update (⇑a) v t, Filter.eventually_principal.2 fun w hw => by
      rw [Function.update_of_ne hw.1]
      exact hw.2⟩
  have hf₀ : Continuous f₀ :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_const.update v continuous_id)
  have heq : splice R K v a = RestrictedProduct.inclusion _ _ hS ∘ f₀ := by
    funext t
    rfl
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hS).comp hf₀

theorem continuous_localMat : Continuous (localMat R K v) :=
  continuous_matrix fun i j => (continuous_splice R K v _).comp (continuous_id.matrix_elem i j)

theorem continuous_localEmbed : Continuous (localEmbed R K v) :=
  Units.continuous_iff.2 ⟨(continuous_localMat R K v).comp Units.continuous_val,
    (continuous_localMat R K v).comp Units.continuous_coe_inv⟩

theorem continuous_finMat : Continuous (finMat R K) :=
  continuous_matrix fun i j =>
    (continuous_const.prodMk (continuous_id.matrix_elem i j) :
      Continuous fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) =>
        ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)))

theorem continuous_finEmbed : Continuous (finEmbed R K) :=
  Units.continuous_iff.2 ⟨(continuous_finMat R K).comp Units.continuous_val,
    (continuous_finMat R K).comp Units.continuous_coe_inv⟩

theorem continuous_placeEmbed : Continuous (placeEmbed K v) :=
  (continuous_finEmbed R K).comp (continuous_localEmbed R K v)

end Continuity

theorem isOpen_setOf_isLocalLevelOne' (p : HeightOneSpectrum (𝓞 ℚ)) {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  have h : {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} =
      (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
        ((fun m => m 1 0) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p} ∩
          (fun m => m 1 1 - 1) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p}) := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hm => ⟨hm.integral, hm.lowerLeft, hm.lowerRight⟩, fun hm => ⟨hm.1, hm.2.1, hm.2.2⟩⟩
  rw [h]
  have hO : IsOpen (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out p
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_id.matrix_elem i j)).inter
    (((isOpen_setOf_valued_le_idealBound p hN).preimage (continuous_id.matrix_elem 1 0)).inter
      ((isOpen_setOf_valued_le_idealBound p hN).preimage
        ((continuous_id.matrix_elem 1 1).sub continuous_const)))

theorem coe_localLevelOne_eq' (p : HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (Gp p)) =
      Units.val ⁻¹' {m | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} ∩
        (fun u : Gp p => ((u⁻¹ : Gp p) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ⁻¹'
          {m | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
  rfl

theorem localLevelOne_isOpen' (p : HeightOneSpectrum (𝓞 ℚ)) {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (Gp p)) := by
  rw [coe_localLevelOne_eq']
  exact ((isOpen_setOf_isLocalLevelOne' p hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLocalLevelOne' p hN).preimage Units.continuous_coe_inv)

private theorem _root_.Module.Basis.exists_coord_eq_eval_combination {K X : Type*} [Field K] {S : Submodule K (X → K)}
    [FiniteDimensional K S] {ι : Type*} (b : Module.Basis ι K S) (i : ι) :
    ∃ c : X →₀ K, ∀ f : S, b.coord i f = c.sum fun x a => a * (f : X → K) x := by
  classical
  let ℓ := b.coord i
  let ev : X → Module.Dual K S := fun x => (LinearMap.proj x).comp S.subtype
  have hev : ∀ x (f : S), ev x f = (f : X → K) x := fun _ _ => rfl
  have hco : (Submodule.span K (Set.range ev)).dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
    rw [Submodule.mem_dualCoannihilator] at hf
    refine Subtype.ext (funext fun x => ?_)
    have h := hf (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at h
    exact h
  have hspan : Submodule.span K (Set.range ev) = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range ev))
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hmem : ℓ ∈ Submodule.span K (Set.range ev) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨c, fun f => ?_⟩
  show ℓ f = _
  rw [← hc]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, hev, smul_eq_mul, Finsupp.sum]

p2m_alias "P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt.Module.Basis.exists_coord_eq_eval_combination" "Module.Basis.exists_coord_eq_eval_combination"

theorem single_place_split
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φ : G → ℂ) (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ)
    (T₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ T₀)
    (hV : (∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ,
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ,
            W ∈ Submodule.span ℂ (Set.range fun h : Gp p => fun g : Gp p => W₀ (g * h))) ∧
        (∀ U : Subgroup (Gp p), IsOpen (U : Set (Gp p)) →
          ∃ B : Finset (Gp p → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ,
            (∀ k ∈ U, ∀ g : Gp p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (Gp p → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ,
          ∃ U : Subgroup (Gp p), IsOpen (U : Set (Gp p)) ∧ ∀ k ∈ U, ∀ g : Gp p, W (g * k) = W g))
    (F : G → ℂ)
    (hF : F ∈ sliceClass (fun g => whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g) T₀) :
    ∃ (m : ℕ) (w : Fin m → Gp p → ℂ) (Rm : Fin m → G → ℂ),
      (∀ i, w i ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ) ∧
      (∀ i (x : p.adicCompletion ℚ) (g : Gp p),
        w i (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w i g) ∧
      (∀ i, ∃ U : Subgroup (Gp p), IsOpen (U : Set (Gp p)) ∧ ∀ k ∈ U, ∀ g : Gp p, w i (g * k) = w i g) ∧
      (∀ v ∈ Submodule.span ℂ (Set.range fun q : Fin m × Gp p => fun g : Gp p => w q.1 (g * q.2)),
        v ≠ 0 → ∀ i, w i ∈ Submodule.span ℂ (Set.range fun h : Gp p => fun g : Gp p => v (g * h))) ∧
      (∀ i, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Φ.level, ∀ g : Gp p, w i (g * k) = w i g) ∧
      (∀ i, Rm i ∈ sliceClass (fun g => whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g) (insert p T₀)) ∧

      (∀ (t : 𝔸), t.1 = 0 → localAt ℚ p (unipotentGL2 t) = 1 →
        (∀ g : G, F (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * F g) →
          ∀ i (g : G), Rm i (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Rm i g) ∧
      ∀ g : G, F g = ∑ i, w i (localAt ℚ p g) * Rm i g := by
  classical

  set W : G → ℂ := fun g => whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g with hWdef
  let V := AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ
  let U₁ : Subgroup (Gp p) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Φ.level

  let σ : G → Gp p → ℂ := fun g x => F (placeEmbed ℚ p x * strip {p} g)
  have hidem : ∀ g : G, strip ({p} : Finset _) (strip {p} g) = strip {p} g := fun g =>
    strip_eq_self_of_forall_localAt_eq_one {p} _ fun q hq => by
      rw [Finset.mem_singleton.1 hq]; exact localAt_strip_of_mem {p} (Finset.mem_singleton_self p) g
  have hcomm : ∀ g : G, strip T₀ (strip ({p} : Finset _) g) = strip {p} (strip T₀ g) := by
    intro g
    refine ext_of_glArch_of_localAt (by rw [glArch_strip, glArch_strip, glArch_strip, glArch_strip]) fun v => ?_
    by_cases hvT : v ∈ T₀
    · rw [localAt_strip_of_mem T₀ hvT, localAt_strip_of_not_mem {p} (fun h => hp (Finset.mem_singleton.1 h ▸ hvT)),
        localAt_strip_of_mem T₀ hvT]
    · rw [localAt_strip_of_not_mem T₀ hvT]
      by_cases hvp : v ∈ ({p} : Finset _)
      · rw [localAt_strip_of_mem {p} hvp, localAt_strip_of_mem {p} hvp]
      · rw [localAt_strip_of_not_mem {p} hvp, localAt_strip_of_not_mem {p} hvp, localAt_strip_of_not_mem T₀ hvT]

  have hevalmem : ∀ y : Gp p, (fun g : G => F (placeEmbed ℚ p y * strip {p} g)) ∈ sliceClass W (insert p T₀) := by
    intro y
    suffices key : ∀ F' ∈ sliceClass W T₀, (fun g : G => F' (placeEmbed ℚ p y * strip {p} g)) ∈ sliceClass W (insert p T₀) from
      key F hF
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem F' hF' =>
      obtain ⟨e, he, rfl⟩ := hF'
      have hfun : (fun g : G => W (e * strip T₀ (placeEmbed ℚ p y * strip {p} g))) =
          fun g => W ((e * placeEmbed ℚ p y) * strip (insert p T₀) g) := by
        funext g
        rw [strip_mul, strip_eq_self_of_forall_localAt_eq_one T₀ (placeEmbed ℚ p y)
          (fun q hq => localAt_placeEmbed_of_ne p y (fun h => hp (h ▸ hq))), hcomm g, ← strip_insert T₀ hp, ← mul_assoc]
      rw [hfun]
      exact mem_sliceClass_generator (insert p T₀) W ((he.mono T₀ (Finset.subset_insert p T₀)).mul (insert p T₀)
        (isSupportedOn_placeEmbed (insert p T₀) (Finset.mem_insert_self p T₀) y))
    | zero => exact Submodule.zero_mem _
    | add F₁ F₂ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
    | smul a F' _ h => exact Submodule.smul_mem _ a h

  have hS1 : ∀ g : G, σ g ∈ V ∧ ∀ k ∈ U₁, ∀ x : Gp p, σ g (x * k) = σ g x := by

    suffices key : ∀ F' ∈ sliceClass W T₀, ∀ g : G,
        (fun x : Gp p => F' (placeEmbed ℚ p x * strip {p} g)) ∈ V ∧
          ∀ k ∈ U₁, ∀ x : Gp p, F' (placeEmbed ℚ p (x * k) * strip {p} g) = F' (placeEmbed ℚ p x * strip {p} g) by
      exact fun g => key F hF g
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem F' hF' =>
      obtain ⟨e, he, rfl⟩ := hF'
      intro g

      have hstrip : ∀ x : Gp p, strip T₀ (placeEmbed ℚ p x * strip {p} g) = placeEmbed ℚ p x * strip T₀ (strip {p} g) := by
        intro x
        rw [strip_mul, strip_eq_self_of_forall_localAt_eq_one T₀ (placeEmbed ℚ p x)
          (fun q hq => localAt_placeEmbed_of_ne p x (fun h => hp (h ▸ hq)))]
      have hz : localAt ℚ p (e * strip T₀ (strip {p} g)) = 1 := by
        rw [map_mul, he.2 p hp, localAt_strip_of_not_mem T₀ hp, localAt_strip_of_mem {p} (Finset.mem_singleton_self p),
          mul_one]
      have hval : ∀ x : Gp p, W (e * strip T₀ (placeEmbed ℚ p x * strip {p} g)) =
          W ((e * strip T₀ (strip {p} g)) * placeEmbed ℚ p x) := by
        intro x
        rw [hstrip, ← mul_assoc, he.mul_placeEmbed_comm T₀ hp x, mul_assoc,
          placeEmbed_mul_comm_of_localAt_eq_one p x _ hz]
      refine ⟨?_, ?_⟩
      · have hfun : (fun x : Gp p => W (e * strip T₀ (placeEmbed ℚ p x * strip {p} g))) =
            AutomorphicForm.WhittakerModel.localFnAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p
              (fun y => φ (y * (e * strip T₀ (strip {p} g)))) := by
          funext x
          rw [hval, localFnAt_eq, whittakerCoefficient_translate, placeEmbed_mul_comm_of_localAt_eq_one p x _ hz]
        rw [hfun]
        exact Submodule.subset_span ⟨_, rfl⟩
      · intro k hk x
        show W (e * strip T₀ (placeEmbed ℚ p (x * k) * strip {p} g)) = W (e * strip T₀ (placeEmbed ℚ p x * strip {p} g))
        rw [hval, hval, map_mul, ← mul_assoc]
        exact Wφ_mul_of_mem_U Φ S R hiso _ _ (placeEmbed_mem_U_of_mem_localLevelOne p Φ.level hk)
    | zero => exact fun g => ⟨Submodule.zero_mem _, fun _ _ _ => rfl⟩
    | add F₁ F₂ _ _ h₁ h₂ =>
      intro g
      refine ⟨Submodule.add_mem _ (h₁ g).1 (h₂ g).1, fun k hk x => ?_⟩
      simp only [Pi.add_apply, (h₁ g).2 k hk x, (h₂ g).2 k hk x]
    | smul a F' _ h =>
      intro g
      refine ⟨Submodule.smul_mem _ a (h g).1, fun k hk x => ?_⟩
      simp only [Pi.smul_apply, (h g).2 k hk x]

  let Sσ : Submodule ℂ (Gp p → ℂ) := Submodule.span ℂ (Set.range σ)
  have hSV : Sσ ≤ V := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact (hS1 g).1)
  have hSK : ∀ f ∈ Sσ, ∀ k ∈ U₁, ∀ x : Gp p, f (x * k) = f x := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨g, rfl⟩ := hf; exact (hS1 g).2
    | zero => intros; rfl
    | add f₁ f₂ _ _ h₁ h₂ => intro k hk x; simp only [Pi.add_apply, h₁ k hk x, h₂ k hk x]
    | smul a f _ h => intro k hk x; simp only [Pi.smul_apply, h k hk x]

  have hU₁open : IsOpen (U₁ : Set (Gp p)) := (Ws23Slot.localLevelOne_isOpen' p Φ.level_ne_bot)
  obtain ⟨B, hB⟩ := hV.2.1 U₁ hU₁open
  have hSB : Sσ ≤ Submodule.span ℂ (B : Set (Gp p → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hB _ (hS1 g).1 (hS1 g).2)
  haveI : FiniteDimensional ℂ Sσ :=
    Submodule.finiteDimensional_of_le hSB

  let m := Module.finrank ℂ Sσ
  let b : Module.Basis (Fin m) ℂ Sσ := Module.finBasis ℂ Sσ
  choose c hc using fun i : Fin m => b.exists_coord_eq_eval_combination i

  refine ⟨m, fun i => ((b i : Sσ) : Gp p → ℂ), fun i g => (c i).sum fun y a => a * F (placeEmbed ℚ p y * strip {p} g),
    fun i => hSV (b i).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i x g
    exact isPsiLocalWhittaker_of_mem_localSpaceAt Φ S R hiso p (hSV (b i).2) x g
  ·
    intro i
    exact hV.2.2 _ (hSV (b i).2)
  ·
    intro v hv hv0 i
    have hvV : v ∈ V := by
      refine (Submodule.span_le.2 ?_) hv
      rintro _ ⟨⟨j, h⟩, rfl⟩
      exact localSpaceAt_translate_stable _ _ p φ (hSV (b j).2) h
    exact hV.1 v hvV hv0 _ (hSV (b i).2)
  ·
    intro i k hk g
    exact hSK _ (b i).2 k hk g
  ·
    intro i
    have hfun : (fun g : G => (c i).sum fun y a => a * F (placeEmbed ℚ p y * strip {p} g)) =
        ∑ y ∈ (c i).support, (c i y) • (fun g : G => F (placeEmbed ℚ p y * strip {p} g)) := by
      funext g
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show (fun g : G => (c i).sum fun y a => a * F (placeEmbed ℚ p y * strip {p} g)) ∈ _
    rw [hfun]
    exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hevalmem y)
  ·
    intro t ht0 htp hlaw i g
    have hstrip : strip ({p} : Finset _) (unipotentGL2 t * g) = unipotentGL2 t * strip {p} g := by
      rw [strip_mul, strip_eq_self_of_forall_localAt_eq_one {p} (unipotentGL2 t)
        (fun q hq => by rw [Finset.mem_singleton.1 hq]; exact htp)]
    show ((c i).sum fun y a => a * F (placeEmbed ℚ p y * strip {p} (unipotentGL2 t * g))) =
      NumberField.StandardAddChar.psiQ t * (c i).sum fun y a => a * F (placeEmbed ℚ p y * strip {p} g)
    simp only [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hstrip, ← mul_assoc, ← unipotentGL2_mul_placeEmbed_comm p t htp y, mul_assoc, hlaw]
    ring
  ·
    intro g
    have hg : F g = σ (strip {p} g) (localAt ℚ p g) := by
      show F g = F (placeEmbed ℚ p (localAt ℚ p g) * strip {p} (strip {p} g))
      rw [hidem, placeEmbed_localAt_mul_strip_singleton]
    let f : Sσ := ⟨σ (strip {p} g), Submodule.subset_span ⟨strip {p} g, rfl⟩⟩
    have hrepr : (f : Gp p → ℂ) = ∑ i, b.coord i f • ((b i : Sσ) : Gp p → ℂ) := by
      conv_lhs => rw [← b.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.coord_apply]
    rw [hg]
    have h1 : σ (strip {p} g) (localAt ℚ p g) = (f : Gp p → ℂ) (localAt ℚ p g) := rfl
    rw [h1, hrepr, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hc i f, mul_comm]
    refine congrArg (fun z => ((b i : Sσ) : Gp p → ℂ) (localAt ℚ p g) * z) ?_
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    show (c i) y * F (placeEmbed ℚ p y * strip {p} (strip {p} g)) = (c i) y * F (placeEmbed ℚ p y * strip {p} g)
    rw [hidem]

section SliceProps

open NumberField.StandardAddChar

variable (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
  {φ : G → ℂ} (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ)
include hiso

theorem sliceClass_psi_law (T : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : G → ℂ} (hF : F ∈ sliceClass (Wφ φ) T)
    (t : 𝔸) (hT : ∀ q ∈ T, localAt ℚ q (unipotentGL2 t) = 1) (g : G) :
    F (unipotentGL2 t * g) = psiQ t * F g := by
  induction hF using Submodule.span_induction generalizing g with
  | mem F hF =>
    obtain ⟨e, he, rfl⟩ := hF
    show Wφ φ (e * strip T (unipotentGL2 t * g)) = psiQ t * Wφ φ (e * strip T g)
    rw [strip_mul, strip_eq_self_of_forall_localAt_eq_one T _ hT, ← mul_assoc,
      he.mul_comm_of_forall_localAt_eq_one T _ hT, mul_assoc]
    exact Wφ_unipotentGL2_mul Φ S R hiso t _
  | zero => simp
  | add F₁ F₂ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂, mul_add]
  | smul a F _ h => simp only [Pi.smul_apply, h, smul_eq_mul]; ring

omit hiso in
theorem continuous_strip' (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (strip T) := by
  refine continuous_id.mul (continuous_list_prod _ fun q _ => ?_)
  exact (continuous_placeEmbed (𝓞 ℚ) ℚ q).comp ((continuous_localAt ℚ q).inv)

theorem continuous_of_mem_sliceClass (T : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : G → ℂ} (hF : F ∈ sliceClass (Wφ φ) T) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨e, he, rfl⟩ := hF
    exact (continuous_Wφ Φ S R hiso).comp ((continuous_const.mul (continuous_strip' T)))
  | zero => exact continuous_const
  | add F₁ F₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul a F _ h => exact h.const_smul a

end SliceProps

section Induction

open NumberField.StandardAddChar

def LocalHyp (φ : G → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  (∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ,
      W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ,
        W ∈ Submodule.span ℂ (Set.range fun h : Gp p => fun g : Gp p => W₀ (g * h))) ∧
    (∀ U : Subgroup (Gp p), IsOpen (U : Set (Gp p)) →
      ∃ B : Finset (Gp p → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ,
        (∀ k ∈ U, ∀ g : Gp p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (Gp p → ℂ))) ∧
    (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ,
      ∃ U : Subgroup (Gp p), IsOpen (U : Set (Gp p)) ∧ ∀ k ∈ U, ∀ g : Gp p, W (g * k) = W g)

variable (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
  {φ : G → ℂ} (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ)
include hiso

omit hiso in

theorem prod_subtype_insert {M : Type*} [CommMonoid M] {p : HeightOneSpectrum (𝓞 ℚ)} {T : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (hp : p ∉ T) (f : HeightOneSpectrum (𝓞 ℚ) → M) :
    ∏ q : ↥(insert p T), f q = f p * ∏ q : ↥T, f q := by
  rw [Finset.prod_coe_sort (insert p T) f, Finset.prod_insert hp, Finset.prod_coe_sort T f]

theorem multi_place_split (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ (T₀ : Finset (HeightOneSpectrum (𝓞 ℚ))), Disjoint T₀ T → (∀ p ∈ T, LocalHyp φ p) →
    ∀ F ∈ sliceClass (Wφ φ) T₀,
    ∃ (m : ℕ) (w : ∀ p : ↥T, Fin m → Gp p → ℂ) (Rm : Fin m → G → ℂ),
      (∀ (p : ↥T) (i : Fin m), w p i ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ (p : HeightOneSpectrum (𝓞 ℚ)) φ) ∧
      (∀ (p : ↥T) (i : Fin m), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) Φ.level,
        ∀ g : Gp p, w p i (g * k) = w p i g) ∧
      (∀ i, Rm i ∈ sliceClass (Wφ φ) (T₀ ∪ T)) ∧
      ∀ g : G, F g = ∑ i, (∏ p : ↥T, w p i (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Rm i g := by
  induction T using Finset.induction_on with
  | empty =>
    intro T₀ _ _ F hF
    haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) := Finset.isEmpty_coe_sort.2 rfl
    refine ⟨1, fun p => isEmptyElim p, fun _ => F, fun p => isEmptyElim p, fun p => isEmptyElim p, fun _ => ?_, fun g => ?_⟩
    · simpa using hF
    · simp
  | insert p T' hpT' IH =>
    intro T₀ hdisj hV F hF
    have hp₀ : p ∉ T₀ := fun h => Finset.disjoint_left.1 hdisj h (Finset.mem_insert_self p T')
    obtain ⟨m₁, w₁, R₁, h0, -, -, -, h8, hR₁, -, hid₁⟩ :=
      single_place_split Φ S R φ hiso T₀ p hp₀ (hV p (Finset.mem_insert_self p T')) F hF

    have hdisj' : Disjoint (insert p T₀) T' := by
      rw [Finset.disjoint_insert_left]
      exact ⟨hpT', Finset.disjoint_of_subset_right (Finset.subset_insert p T') hdisj⟩
    have hV' : ∀ q ∈ T', LocalHyp φ q := fun q hq => hV q (Finset.mem_insert_of_mem hq)
    choose m₂ w₂ R₂ h0₂ h8₂ hR₂ hid₂ using fun i : Fin m₁ => IH (insert p T₀) hdisj' hV' (R₁ i) (hR₁ i)

    let ι : Type := Σ i : Fin m₁, Fin (m₂ i)
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    refine ⟨Fintype.card ι,
      fun q k => if hq : (q : HeightOneSpectrum (𝓞 ℚ)) = p then fun x => w₁ (e.symm k).1 (hq ▸ x)
        else w₂ (e.symm k).1 ⟨q, (Finset.mem_insert.1 q.2).resolve_left hq⟩ (e.symm k).2,
      fun k => R₂ (e.symm k).1 (e.symm k).2, ?_, ?_, ?_, ?_⟩
    · rintro ⟨q, hq⟩ k
      dsimp only
      split_ifs with hqp
      · subst hqp; exact h0 _
      · exact h0₂ (e.symm k).1 ⟨q, (Finset.mem_insert.1 hq).resolve_left hqp⟩ (e.symm k).2
    · rintro ⟨q, hq⟩ k kk hkk g
      dsimp only at hkk ⊢
      split_ifs with hqp
      · subst hqp; exact h8 _ kk hkk g
      · exact h8₂ (e.symm k).1 ⟨q, (Finset.mem_insert.1 hq).resolve_left hqp⟩ (e.symm k).2 kk hkk g
    · intro k
      have := hR₂ (e.symm k).1 (e.symm k).2
      rwa [Finset.insert_union, ← Finset.union_insert] at this
    · intro g

      have key : ∀ k : Fin (Fintype.card ι),
          (∏ q : ↥(insert p T'),
            (if hq : (q : HeightOneSpectrum (𝓞 ℚ)) = p then fun x => w₁ (e.symm k).1 (hq ▸ x)
              else w₂ (e.symm k).1 ⟨q, (Finset.mem_insert.1 q.2).resolve_left hq⟩ (e.symm k).2)
              (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) =
            w₁ (e.symm k).1 (localAt ℚ p g) * ∏ q : ↥T', w₂ (e.symm k).1 q (e.symm k).2 (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g) := by
        intro k
        let f : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun q => if hq' : q ∈ insert p T' then
          (if hq : q = p then fun x => w₁ (e.symm k).1 (hq ▸ x)
            else w₂ (e.symm k).1 ⟨q, (Finset.mem_insert.1 hq').resolve_left hq⟩ (e.symm k).2) (localAt ℚ q g) else 1
        have hf : ∀ q : ↥(insert p T'),
            (if hq : (q : HeightOneSpectrum (𝓞 ℚ)) = p then fun x => w₁ (e.symm k).1 (hq ▸ x)
              else w₂ (e.symm k).1 ⟨q, (Finset.mem_insert.1 q.2).resolve_left hq⟩ (e.symm k).2)
              (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g) = f q := by
          rintro ⟨q, hq⟩
          simp only [f, dif_pos hq]
        rw [Finset.prod_congr rfl fun q _ => hf q, prod_subtype_insert hpT' f]
        congr 1
        · simp only [f, dif_pos (Finset.mem_insert_self p T')]
          simp
        · refine Finset.prod_congr rfl fun q _ => ?_
          have hqp : (q : HeightOneSpectrum (𝓞 ℚ)) ≠ p := fun h => hpT' (h ▸ q.2)
          simp only [f, dif_pos (Finset.mem_insert_of_mem q.2), dif_neg hqp]
      calc F g = ∑ i, ∑ j, w₁ i (localAt ℚ p g) *
            ((∏ q : ↥T', w₂ i q j (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) * R₂ i j g) := by
            rw [hid₁ g]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hid₂ i g, Finset.mul_sum]
        _ = ∑ x : ι, w₁ x.1 (localAt ℚ p g) *
            ((∏ q : ↥T', w₂ x.1 q x.2 (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) * R₂ x.1 x.2 g) :=
            (Fintype.sum_sigma (fun x : ι => w₁ x.1 (localAt ℚ p g) *
              ((∏ q : ↥T', w₂ x.1 q x.2 (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) * R₂ x.1 x.2 g))).symm
        _ = ∑ k : Fin (Fintype.card ι), w₁ (e.symm k).1 (localAt ℚ p g) *
            ((∏ q : ↥T', w₂ (e.symm k).1 q (e.symm k).2 (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) *
              R₂ (e.symm k).1 (e.symm k).2 g) :=
            (e.symm.sum_comp (fun x : ι => w₁ x.1 (localAt ℚ p g) *
              ((∏ q : ↥T', w₂ x.1 q x.2 (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) g)) * R₂ x.1 x.2 g))).symm
        _ = _ := Finset.sum_congr rfl fun k _ => by rw [key k]; ring

end Induction

section Assembly

open NumberField.StandardAddChar

theorem continuous_of_forall_mul_eq_of_isOpen {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {W : H → ℂ} (U : Subgroup H) (hU : IsOpen (U : Set H)) (hW : ∀ k ∈ U, ∀ g, W (g * k) = W g) : Continuous W := by
  refine (IsLocallyConstant.iff_exists_open _).2 (fun g => ⟨(fun k => g * k) '' (U : Set H), ?_, ⟨1, U.one_mem, mul_one g⟩,
    ?_⟩) |>.continuous
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU
  · rintro _ ⟨k, hk, rfl⟩; exact hW k hk g

theorem measurable_comp_coe_fin {F : G → ℂ} (hF : Continuous F) (a : G) :
    Measurable (fun g : ↥(finiteAdelicGL2Subgroup ℚ) => F (a * (g : G))) :=
  (hF.comp (continuous_const.mul continuous_subtype_val)).measurable

theorem measurable_slot (p : HeightOneSpectrum (𝓞 ℚ)) {w : Gp p → ℂ} (U : Subgroup (Gp p)) (hU : IsOpen (U : Set (Gp p)))
    (hw : ∀ k ∈ U, ∀ g, w (g * k) = w g) :
    Measurable (fun g : ↥(finiteAdelicGL2Subgroup ℚ) => w (localAt ℚ p (g : G))) :=
  ((continuous_of_forall_mul_eq_of_isOpen U hU hw).comp ((continuous_localAt ℚ p).comp continuous_subtype_val)).measurable

theorem coe_finFactor_of_mem {g : G} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : (RSCarrier.finFactor g : G) = g := by
  rw [coe_finFactor, ratArchGL2_of_mem hg, map_one, inv_one, one_mul]

end Assembly

end Ws23Slot
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt.Ws23Slot"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt.Ws23Slot"

open Ws23Slot NumberField.StandardAddChar AdelicDock UnramifiedWhittaker in
open scoped Classical in

theorem solution
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (par : InfinitePlace ℚ → ZMod 2) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))

    (hV : ∀ p ∈ T,
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) :
    ∃ (m : ℕ) (w : ∀ p : ↥T, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
      (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ),

      (∀ (p : ↥T) (α : Fin m),
        w p α ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (p : HeightOneSpectrum (𝓞 ℚ)) (φv par)) ∧

      (∀ (α : Fin m) (p : ↥T) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        W' α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g) ∧

      (∀ (p : ↥T) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
        w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g) ∧

      (∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 → (∀ p : ↥T, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * W' α g) ∧

      (∀ (p : ↥T) (α : Fin m),
        Measurable (fun g : finiteAdelicGL2Subgroup ℚ => w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ∧
      (∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ))) ∧

      (∀ (p : ↥T) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      (∀ (p : ↥T), ∀ v ∈ Submodule.span ℂ (Set.range fun q : Fin m × GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => fun g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => w p q.1 (g * q.2)),
        v ≠ 0 → ∀ α : Fin m,
          w p α ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => fun g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => v (g * h))) ∧

      (∀ (p : ↥T) (α : Fin m), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) Φ.level, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf par (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥T, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g := by
  classical

  obtain ⟨m, w, Rm, h0, h8, hRm, hid⟩ := multi_place_split Φ S R (hiso par) T ∅ (Finset.disjoint_empty_left T)
    (fun p hp => hV p hp) (Wφ (φv par)) (mem_sliceClass_self _)

  have hWne : Wφ (φv par) ≠ 0 :=
    whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero _ R.centralChar Φ.level S Φ (φv par) (hiso par) (hφne par)
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hWne
  set a₀ : GL (Fin 2) ℝ := ratArchGL2 g₀ with ha₀
  have hfac : ∀ g : G, Wφ (φv par) g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g) := fun g => hWAf par g
  have hA : WA par a₀ ≠ 0 := by
    intro h; apply hg₀; show Wφ (φv par) g₀ = 0; rw [hfac, ← ha₀, h, zero_mul]

  refine ⟨m, w, fun α g => (WA par a₀)⁻¹ * Rm α (ιR a₀ * (RSCarrier.finFactor g : G)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact fun p α => h0 p α
  ·
    intro α p x g
    dsimp only
    rw [finFactor_mul_of_mem g (placeEmbed_mem_fin _ x), ← mul_assoc,
      sliceClass_placeEmbed_invariant (∅ ∪ T) (hRm α) (by simp) x]
  ·
    intro p α x g
    exact isPsiLocalWhittaker_of_mem_localSpaceAt Φ S R (hiso par) _ (h0 p α) x g
  ·
    intro α t ht hT g
    dsimp only
    rw [finFactor_mul_of_mem_left g (unipotentGL2_mem_fin ht), ← mul_assoc,
      iotaR_mul_comm_of_mem (unipotentGL2_mem_fin ht), mul_assoc,
      sliceClass_psi_law Φ S R (hiso par) (∅ ∪ T) (hRm α) t (fun q hq => hT ⟨q, by simpa using hq⟩)]
    ring
  ·
    intro p α
    obtain ⟨U, hU, hwU⟩ := (hV p p.2).2.2 (w p α) (h0 p α)
    exact measurable_slot _ U hU hwU
  ·
    intro α
    have hc : Continuous (Rm α) := continuous_of_mem_sliceClass Φ S R (hiso par) _ (hRm α)
    have : (fun g : ↥(finiteAdelicGL2Subgroup ℚ) => (WA par a₀)⁻¹ * Rm α (ιR a₀ * (RSCarrier.finFactor (g : G) : G))) =
        fun g : ↥(finiteAdelicGL2Subgroup ℚ) => (WA par a₀)⁻¹ * Rm α (ιR a₀ * (g : G)) := by
      funext g; rw [coe_finFactor_of_mem g.2]
    rw [this]
    exact (measurable_comp_coe_fin hc _).const_mul _
  ·
    intro p α
    exact (hV p p.2).2.2 (w p α) (h0 p α)
  ·
    intro p v hv hv0 α
    have hvV : v ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ (p : HeightOneSpectrum (𝓞 ℚ)) (φv par) := by
      refine (Submodule.span_le.2 ?_) hv
      rintro _ ⟨q, rfl⟩
      exact localSpaceAt_translate_stable _ _ _ _ (h0 p q.1) q.2
    exact (hV p p.2).1 v hvV hv0 (w p α) (h0 p α)
  ·
    exact fun p α k hk g => h8 p α k hk g
  ·
    intro g
    set f : ↥(finiteAdelicGL2Subgroup ℚ) := RSCarrier.finFactor g with hf
    have h1 : Wφ (φv par) (ιR a₀ * (f : G)) = WA par a₀ * Wf par f := by
      rw [hfac, ratArchGL2_mul, ratArchGL2_iotaR, ratArchGL2_of_mem f.2, mul_one, finFactor_iotaR_mul' f.2]
    have h2 := hid (ιR a₀ * (f : G))
    have h3 : ∀ p : ↥T, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (ιR a₀ * (f : G)) = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g := by
      intro p; rw [map_mul, localAt_iotaR, one_mul, hf, localAt_finFactor]
    simp_rw [h3] at h2
    calc Wf par f = (WA par a₀)⁻¹ * Wφ (φv par) (ιR a₀ * (f : G)) := by rw [h1, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
      _ = _ := by rw [h2, Finset.mul_sum]; refine Finset.sum_congr rfl fun α _ => ?_; ring

end S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
end P2MW
export P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt (solution)
