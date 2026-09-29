-- Prove2me | solution 1 for AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2d0b2ccd-5040-5622-bc12-05e92aa6c5a9

import Theorems.Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23Slot

open UnramifiedWhittaker AdelicDock

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem exists_linearIndepOn_finset_repr {K X ι : Type*} [Field K] [Fintype ι] (u : ι → X → K) :
    ∃ (s : Finset ι) (d : ι → ι → K), LinearIndepOn K u (s : Set ι) ∧ ∀ i x, u i x = ∑ j ∈ s, d i j * u j x := by
  classical
  obtain ⟨s, hind, hmax⟩ := exists_maximal_linearIndepOn K u
  have hmem : ∀ i, u i ∈ Submodule.span K (u '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · obtain ⟨a, ha, h⟩ := hmax i hi
      have := Submodule.smul_mem _ a⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  have hrepr : ∀ i, ∃ d : ι →₀ K, (↑d.support ⊆ s) ∧ u i = d.sum fun j a => a • u j := by
    intro i
    obtain ⟨d, hds, hd⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := K) (v := u)).1 (hmem i)
    exact ⟨d, (Finsupp.mem_supported K d).1 hds, by rw [← hd, Finsupp.linearCombination_apply]⟩
  choose d hds hd using hrepr
  refine ⟨s.toFinset, fun i j => d i j, by simpa using hind, fun i x => ?_⟩
  conv_lhs => rw [hd i]
  rw [Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_subset (by simpa using hds i) fun j _ hj => ?_
  rw [Finsupp.notMem_support_iff.1 hj]; simp

theorem localAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ v (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ))
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) : localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem placeEmbed_mul_comm (p : HeightOneSpectrum (𝓞 ℚ)) {g : G2} (hg : localAt ℚ p g = 1)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  have hgp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := congrArg Units.val hg
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x) * _ = _ * finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x)
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = p
    · subst hw
      rw [hgp, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ p _ hw, one_mul, mul_one]

theorem ratArchGL2_mul_coe (g : G2) (k : finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (g * (k : G2)) = ratArchGL2 g := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, mul_one]

theorem finFactor_mul_coe (g : G2) (k : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * (k : G2)) = RSCarrier.finFactor g * k := by
  apply Subtype.ext
  show _ = ((RSCarrier.finFactor g : G2)) * (k : G2)
  simp only [RSCarrier.finFactor, ratArchGL2_mul_coe, mul_assoc]

theorem localAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : G2) (i j : Fin 2) :
    ((localAt ℚ p g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p := rfl

theorem mem_levelOne_of_local (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (hSQ : ∀ p : HeightOneSpectrum (𝓞 ℚ), N ≤ p.asIdeal → p ∈ SQ)
    (k : G2)
    (hk1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (hk2 : ∀ v ∈ SQ, localAt ℚ v k = 1) :
    k ∈ levelOne (𝓞 ℚ) ℚ N := by
  have hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → idealBound (𝓞 ℚ) N v = 1 := fun v hv =>
    idealBound_eq_one_of_not_dvd hN fun h => hv (hSQ v (Ideal.le_of_dvd h))

  have key : ∀ g : G2, (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v g = 1) → IsLevelOneMatrix (𝓞 ℚ) ℚ N (glFin (𝓞 ℚ) ℚ g : Matrix _ _ _) := by
    intro g h1 h2
    have hent : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2),
        ((glFin (𝓞 ℚ) ℚ g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v =
          ((localAt ℚ v g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j :=
      fun v i j => rfl
    have hint : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2),
        ((glFin (𝓞 ℚ) ℚ g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v ∈ v.adicCompletionIntegers ℚ := by
      intro v i j
      rw [hent]
      by_cases hv : v ∈ SQ
      · rw [h2 v hv, Units.val_one]
        rcases eq_or_ne i j with hij | hij
        · subst hij; rw [Matrix.one_apply_eq]; exact one_mem _
        · rw [Matrix.one_apply_ne hij]; exact zero_mem _
      · exact ((AdelicDock.mem_localLevelOne_iff _ _ _ _).1 (h1 v hv)).1.integral i j
    refine ⟨⟨fun i j v => hint v i j, fun v => ?_⟩, fun v => ?_⟩
    · by_cases hv : v ∈ SQ
      · rw [hent, h2 v hv, Units.val_one, Matrix.one_apply_ne (by decide), map_zero]; exact zero_le'
      · rw [hb v hv]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint v 1 0)
    · by_cases hv : v ∈ SQ
      · rw [coe_sub_apply, coe_one_apply, hent, h2 v hv, Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
        exact zero_le'
      · rw [hb v hv, coe_sub_apply, coe_one_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (hint v 1 1) (one_mem _))
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff, ← map_inv]
  exact ⟨key k hk1 hk2, key k⁻¹ (fun v hv => by rw [map_inv]; exact inv_mem (hk1 v hv))
    (fun v hv => by rw [map_inv, hk2 v hv, inv_one])⟩

end Ws23Slot

open Ws23Slot UnramifiedWhittaker in
theorem solution
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

    (hSQ1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (par : InfinitePlace ℚ → ZMod 2)

    (hV : ∀ p ∈ SQ,
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) :
    ∃ (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
      (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ),

      (∀ (p : ↥SQ) (α : Fin m),
        w p α ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (p : HeightOneSpectrum (𝓞 ℚ)) (φv par)) ∧

      (∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        W' α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g) ∧

      (∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
        w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g) ∧

      (∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 → (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * W' α g) ∧

      (∀ (p : ↥SQ) (α : Fin m),
        Measurable (fun g : finiteAdelicGL2Subgroup ℚ => w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ∧
      (∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ))) ∧

      (∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      (∀ (p : ↥SQ) (α : Fin m), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) Φ.level, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      (∀ (α : Fin m) (k : finiteAdelicGL2Subgroup ℚ),
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
          localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
        (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' α g) ∧

      (∀ c : Fin m → ℂ,
        (∀ y : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ),
          ∑ α : Fin m, c α * ∏ p : ↥SQ, w p α (y p) = 0) → ∀ α : Fin m, c α = 0) ∧

      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf par (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g := by
  classical
  obtain ⟨m, w, W', hA, hB, hC, hD, hE, hF, hG, -, hI, hJ⟩ :=
    AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
      Φ S R φv hiso hφne WA Wf hWAf par SQ hV

  set U : Fin m → (∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) → ℂ :=
    fun α y => ∏ p : ↥SQ, w p α (y p) with hUdef
  obtain ⟨s, d, hind, hrepr⟩ := exists_linearIndepOn_finset_repr U
  set e : Fin s.card ≃ ↥s := s.equivFin.symm with hedef

  have hregroup : ∀ (y : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : G2),
      ∑ α : Fin m, U α y * W' α g = ∑ γ : Fin s.card, U (e γ) y * ∑ α : Fin m, d α (e γ) * W' α g := by
    intro y g
    calc ∑ α : Fin m, U α y * W' α g = ∑ α : Fin m, ∑ β ∈ s, d α β * U β y * W' α g := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hrepr α y, Finset.sum_mul]
      _ = ∑ β ∈ s, U β y * ∑ α : Fin m, d α β * W' α g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          ring
      _ = ∑ x : ↥s, U x y * ∑ α : Fin m, d α x * W' α g := (Finset.sum_coe_sort s _).symm
      _ = ∑ γ : Fin s.card, U (e γ) y * ∑ α : Fin m, d α (e γ) * W' α g :=
          (Fintype.sum_equiv e _ _ fun _ => rfl).symm

  have hindep : ∀ c : Fin s.card → ℂ,
      (∀ y : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ),
        ∑ γ : Fin s.card, c γ * U (e γ) y = 0) → ∀ γ : Fin s.card, c γ = 0 := by
    intro c hc γ
    have hli := Fintype.linearIndependent_iff.1 hind (fun x => c (e.symm x)) ?_
    · simpa using hli (e γ)
    · funext y
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hc y]
      exact Fintype.sum_equiv e.symm _ _ fun x => by simp

  have hWne := AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
    (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) R.centralChar Φ.level S Φ (φv par) (hiso par) (hφne par)
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : G2, whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      NumberField.StandardAddChar.psiQ (φv par) 1 g₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hWne (funext h)
  have hWA : WA par (ratArchGL2 g₁) ≠ 0 := by
    rw [hWAf] at hg₁
    exact left_ne_zero_of_mul hg₁

  have hcoef : ∀ (k : finiteAdelicGL2Subgroup ℚ),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (k : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : G2) = 1) →
      ∀ h : finiteAdelicGL2Subgroup ℚ, Wf par (h * k) = Wf par h := by
    intro k hk1 hk2 h
    have hkU : (k : G2) ∈ (productionPinsGeneral ℚ).U Φ.level := by
      show (k : G2) ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ
      exact Subgroup.mem_inf.2 ⟨mem_levelOne_of_local SQ Φ.level Φ.level_ne_bot hSQ1 k hk1 hk2, k.2⟩
    set g : G2 := g₁ * (((RSCarrier.finFactor g₁)⁻¹ * h : finiteAdelicGL2Subgroup ℚ) : G2) with hgdef
    have hga : ratArchGL2 g = ratArchGL2 g₁ := ratArchGL2_mul_coe _ _
    have hgf : RSCarrier.finFactor g = h := by rw [hgdef, finFactor_mul_coe, mul_inv_cancel_left]
    have hinv : whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (φv par) 1 (g * (k : G2)) =
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (φv par) 1 g := by
      unfold whittakerCoefficient
      congr 1
      funext x
      rw [← mul_assoc, (hiso par).level_invariant _ _ hkU]
    rw [hWAf, hWAf, ratArchGL2_mul_coe, finFactor_mul_coe, hga, hgf] at hinv
    exact mul_left_cancel₀ hWA hinv

  have hvary : ∀ (g : G2) (y : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      ∃ X : G2, (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X) = y p) ∧
        (∀ (α : Fin m) (h : G2), W' α (h * X) = W' α h) ∧
        (∀ h : G2, (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) h = 1) → X * h = h * X) := by
    intro g y
    suffices hB' : ∀ B : Finset ↥SQ, ∃ X : G2, (∀ p ∈ B, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X) = y p) ∧
        (∀ (α : Fin m) (h : G2), W' α (h * X) = W' α h) ∧
        (∀ h : G2, (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) h = 1) → X * h = h * X) by
      obtain ⟨X, h1, h2, h3⟩ := hB' Finset.univ
      exact ⟨X, fun p => h1 p (Finset.mem_univ p), h2, h3⟩
    intro B
    induction B using Finset.induction_on with
    | empty => exact ⟨1, fun p hp => (Finset.notMem_empty p hp).elim, fun α h => by rw [mul_one], fun h _ => by rw [one_mul, mul_one]⟩
    | @insert p B hpB ih =>
      obtain ⟨X, h1, h2, h3⟩ := ih
      refine ⟨X * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X))⁻¹ * y p),
        fun q hq => ?_, fun α h => ?_, fun h hh => ?_⟩
      · rcases Finset.mem_insert.1 hq with hqp | hqB
        · subst hqp
          rw [← mul_assoc, map_mul, localAt_placeEmbed_self, mul_inv_cancel_left]
        · have hne : (q : HeightOneSpectrum (𝓞 ℚ)) ≠ (p : HeightOneSpectrum (𝓞 ℚ)) := fun h =>
            hpB ((Subtype.ext h) ▸ hqB)
          rw [← mul_assoc, map_mul, localAt_placeEmbed_of_ne _ _ hne, mul_one]
          exact h1 q hqB
      · rw [← mul_assoc, hB, h2]
      · rw [mul_assoc, placeEmbed_mul_comm _ (hh p), ← mul_assoc, h3 h hh, mul_assoc]

  refine ⟨s.card, fun p γ => w p (e γ), fun γ g => ∑ α : Fin m, d α (e γ) * W' α g,
    fun p γ => hA p (e γ), fun γ p x g => ?_, fun p γ => hC p (e γ), fun γ t ht1 ht2 g => ?_,
    fun p γ => hE p (e γ), fun γ => ?_, fun p γ => hG p (e γ), fun p γ => hI p (e γ), fun γ k hk1 hk2 g => ?_,
    fun c hc => ?_, fun g => ?_⟩
  ·
    exact Finset.sum_congr rfl fun α _ => by rw [hB]
  ·
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by rw [hD α t ht1 ht2 g]; ring
  ·
    exact Finset.measurable_sum _ fun α _ => (hF α).const_mul _
  ·
    have hzero : ∀ y : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ),
        ∑ γ : Fin s.card, ((∑ α : Fin m, d α (e γ) * W' α (g * (k : G2))) - ∑ α : Fin m, d α (e γ) * W' α g) *
          U (e γ) y = 0 := by
      intro y
      obtain ⟨X, hX1, hX2, hX3⟩ := hvary g y
      have hJ1 := hJ (g * X)
      have hJ2 := hJ (g * X * (k : G2))
      rw [finFactor_mul_coe, hcoef k hk1 hk2, hJ1, hregroup, hregroup] at hJ2
      have hy1 : (fun p : ↥SQ => localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X)) = y := funext hX1
      have hy2 : (fun p : ↥SQ => localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X * (k : G2))) = y := by
        funext p; rw [map_mul, hk2 p p.2, mul_one, hX1]
      have hU1 : ∀ γ, U (e γ) (fun p : ↥SQ => localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X)) = U (e γ) y := fun γ => by rw [hy1]
      have hU2 : ∀ γ, U (e γ) (fun p : ↥SQ => localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g * X * (k : G2))) = U (e γ) y :=
        fun γ => by rw [hy2]
      have hW1 : ∀ α, W' α (g * X) = W' α g := fun α => hX2 α g
      have hW2 : ∀ α, W' α (g * X * (k : G2)) = W' α (g * (k : G2)) := fun α => by
        rw [mul_assoc, hX3 (k : G2) (fun p => hk2 p p.2), ← mul_assoc, hX2]
      simp only [hUdef] at hU1 hU2 hJ2 ⊢
      simp only [hU1, hU2, hW1, hW2] at hJ2
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hJ2
      have hJ3 := congrArg Neg.neg hJ2
      rw [neg_zero, ← Finset.sum_neg_distrib] at hJ3
      rw [← hJ3]
      refine Finset.sum_congr rfl fun γ _ => ?_
      ring
    have := hindep (fun γ => (∑ α : Fin m, d α (e γ) * W' α (g * (k : G2))) - ∑ α : Fin m, d α (e γ) * W' α g) hzero γ
    exact sub_eq_zero.1 this
  ·
    exact hindep c (fun y => by simpa only [hUdef] using hc y)
  ·
    rw [hJ g]
    have := hregroup (fun p : ↥SQ => localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g) g
    simpa only [hUdef] using this

#print axioms solution

end S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
end P2MW
export P2MW.S_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt (solution)
