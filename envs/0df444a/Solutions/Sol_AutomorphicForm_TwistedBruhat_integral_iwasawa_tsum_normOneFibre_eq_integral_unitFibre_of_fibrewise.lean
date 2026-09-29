-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f488b764-576f-565c-9a7d-008f410e3c00

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicKernel
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped Pointwise ENNReal NNReal Topology

noncomputable section

namespace R1IwTorus

section Generic

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem continuous_comp_pair {X W P : Type} [TopologicalSpace X] [TopologicalSpace W] [TopologicalSpace P]
    (G : X → W → ℂ) (hG : Continuous fun q : X × W => G q.1 q.2) (a : P → X) (ha : Continuous a) (e : P → W)
    (he : Continuous e) : Continuous fun p : P => G (a p) (e p) :=
  hG.comp (ha.prodMk he)

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem continuous_diagOne : Continuous (diagOne : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 L) L), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 L) L)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

theorem continuous_word : Continuous fun r : ((AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) × adelicMaximalCompact L =>
    unipotentGL2 r.1.1 * diagOne r.1.2 * (r.2 : AdelicGL2 (𝓞 L) L) :=
  (((AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)).comp (continuous_fst.comp continuous_fst)).mul
    ((continuous_diagOne L).comp (continuous_snd.comp continuous_fst))).mul (continuous_subtype_val.comp continuous_snd)

theorem exists_finite_forall_ne_zero_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ Γ : Set (GL (Fin 2) L), Γ.Finite ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ δ : GL (Fin 2) L,
      φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) ≠ 0 → δ ∈ Γ := by
  have hC : IsCompact (X * tsupport φ * Y⁻¹) := (hX.mul hφs).mul hY.inv
  refine ⟨{δ | (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹}, hfin _ hC 1 1, ?_⟩
  intro x hx y hy δ hδ
  have hmem : x⁻¹ * globalPoints (𝓞 L) L δ * y ∈ tsupport φ := subset_tsupport φ hδ
  have h : globalPoints (𝓞 L) L δ = x * (x⁻¹ * globalPoints (𝓞 L) L δ * y) * y⁻¹ := by group
  change (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹
  rw [inv_one, one_mul, mul_one, h]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hmem) (Set.inv_mem_inv.mpr hy)

theorem continuous_finsum_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T, φ (p.1⁻¹ * globalPoints (𝓞 L) L δ * p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨X, hX, hXn⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Y, hY, hYn⟩ := exists_compact_mem_nhds p.2
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hfin φ hφs hX hY
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  have ht : ∀ x ∈ X, ∀ y ∈ Y, (∑ᶠ δ ∈ T, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)) =
      ∑ δ ∈ hΓT.toFinset, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) := by
    intro x hx y hy
    apply finsum_mem_eq_sum_of_subset
    · rintro δ ⟨hδT, hδs⟩; exact hΓT.mem_toFinset.mpr ⟨hmem x hx y hy δ hδs, hδT⟩
    · intro δ hδ; exact (hΓT.mem_toFinset.mp hδ).2
  have hsum : Continuous fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ δ ∈ hΓT.toFinset, φ (q.1⁻¹ * globalPoints (𝓞 L) L δ * q.2) :=
    continuous_finsetSum _ fun δ _ => hφc.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)
  exact ((hsum.continuousOn (s := X ×ˢ Y)).congr fun q hq => ht q.1 hq.1 q.2 hq.2).continuousAt (prod_mem_nhds hXn hYn)

variable (K : Type) [Field K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def Kgen (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * g))

def Tgen (T : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator (highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (@constantTerm _ (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
    (centralScalar (𝓞 L) L z * g)

theorem continuous_sigmaAdelicAct : Continuous (sigmaAdelicAct K L D σ) :=
  Continuous.units_map _ ((continuous_id.matrix_map (D.continuous_act σ)) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) => m.map (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)

theorem continuous_fold (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Kgen L K D σ T' φ p.2 p.1 :=
  continuous_comp_pair (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T') Prod.fst continuous_fst _
    ((continuous_sigmaAdelicAct L K D σ).comp (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst))

theorem continuous_truncationIntegrand (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      ∑ᶠ δ ∈ T', φ (r.1.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
          (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1))) :=
  continuous_comp_pair (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T') (fun r => r.1.1) (continuous_fst.comp continuous_fst)
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      sigmaAdelicAct K L D σ (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)))
    ((continuous_sigmaAdelicAct L K D σ).comp
      (((AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)).comp continuous_snd).mul
        ((((continuous_centralScalar L).comp (continuous_snd.comp continuous_fst))).mul (continuous_fst.comp continuous_fst))))

open Classical in
theorem Tgen_eq_ite (T' : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Tgen L K D σ T' R φ z g =
      if Real.exp R < NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L z * g) then
        ∫ q, ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (unipotentGL2 q * (centralScalar (𝓞 L) L z * g)))
          ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      else 0 := by
  unfold Tgen; rw [Set.indicator_apply]; rfl

theorem measurable_Kgen_sub_Tgen [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ) (T' T'' : Set (GL (Fin 2) L)) :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Kgen L K D σ T' φ p.2 p.1 - Tgen L K D σ T'' R φ p.2 p.1 := by
  classical
  have hloc := AutomorphicForm.adelicKernelLocalFiniteness L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  have hKm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Kgen L K D σ T' φ p.2 p.1 :=
    (continuous_fold L K D σ hloc φ hφc hφs T').measurable
  have hhigh : MeasurableSet {p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L p.2 * p.1)} :=
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)).measurable measurableSet_Ioi
  have hCT : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ T'', φ (r.1.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
            (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)))) (p, q)
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (continuous_truncationIntegrand L K D σ hloc φ hφc hφs T'').stronglyMeasurable.integral_prod_right'
  have hTm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Tgen L K D σ T'' R φ p.2 p.1 := by
    simp_rw [Tgen_eq_ite]
    exact Measurable.ite hhigh hCT.measurable measurable_const
  exact hKm.sub hTm

end Generic

section Fibres

open AutomorphicForm.TwistedBruhat

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

abbrev N1 : Type := {α : Lˣ // Algebra.norm K (α : L) = 1}

def I1 (a : N1 K L) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)}

def J1 (a : N1 K L) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)}

def I11 : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1}

def J11 : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1}

def Wa (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : N1 K L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Kgen L K D σ (I1 K L σ hgen a) φ ζ g - Tgen L K D σ (J1 K L a) R φ ζ g

def W1 (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Kgen L K D σ (I11 K L σ hgen) φ ζ g - Tgen L K D σ (J11 L) R φ ζ g

theorem map_diagOne {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne u) = diagOne (Units.map (f : A →* B) u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change f ((diagOne u : Matrix (Fin 2) (Fin 2) A) i j) = (diagOne (Units.map (f : A →* B) u) : Matrix (Fin 2) (Fin 2) B) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_inv_mul_unipotentGL2 {A : Type*} [CommRing A] (u : Aˣ) (q : A) :
    (diagOne u)⁻¹ * unipotentGL2 q = unipotentGL2 (((u⁻¹ : Aˣ) : A) * q) * (diagOne u)⁻¹ := by
  rw [← map_inv]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply,
    unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem unipotent_mul_word (l : L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) :
    globalPoints (𝓞 L) L (unipotentGL2 l) * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) =
      unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l + x) * diagOne t * (k : AdelicGL2 (𝓞 L) L) := by
  have h : globalPoints (𝓞 L) L (unipotentGL2 l) = unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    change algebraMap L (AdeleRing (𝓞 L) L) ((unipotentGL2 l : Matrix (Fin 2) (Fin 2) L) i j) =
      (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
    rw [unipotentGL2_coe, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp
  rw [h, unipotentGL2_add]
  simp only [mul_assoc]

theorem ideleNorm_principal (e : Lˣ) :
    NumberField.TateGlobal.ideleNorm L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e) = 1 := by
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := L) (diagOne e)
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L (diagOne e)) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e := by
    rw [show globalPoints (𝓞 L) L (diagOne e) = diagOne (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) e) from
      map_diagOne _ _]
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show (Matrix.diagonal ![((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e :
      (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]).det = _
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  rwa [hdet] at h

theorem ideleNorm_prin_inv_mul (e : Lˣ) (t : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e)⁻¹ * t) =
      NumberField.TateGlobal.ideleNorm L t := by
  have h1 := NumberField.TateGlobal.ideleNorm_mul (F := L)
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e)⁻¹)
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e)
  rw [inv_mul_cancel, ideleNorm_principal, mul_one] at h1
  have h0 : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
    have h := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
    rw [one_mul] at h
    have hpos := NumberField.TateGlobal.ideleNorm_pos (F := L) 1
    nlinarith
  rw [NumberField.TateGlobal.ideleNorm_mul, ← h1, h0, one_mul]

include hgen

theorem exists_eOf (a : N1 K L) : ∃ e : Lˣ, ((a : Lˣ) : L) * σ (e : L) = (e : L) := by
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, fun τ => Subgroup.mem_zpowers_iff.mp (hgen τ)⟩⟩
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one (K := K) (L := L) hgen a.2
  have hσy : σ (y : L) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact y.ne_zero
  exact ⟨y, by rw [← hy, div_mul_cancel₀ _ hσy]⟩

def eOf (a : N1 K L) : Lˣ := (exists_eOf K L σ hgen a).choose

theorem eOf_spec (a : N1 K L) : ((a : Lˣ) : L) * σ (eOf K L σ hgen a : L) = (eOf K L σ hgen a : L) :=
  (exists_eOf K L σ hgen a).choose_spec

def Eid (a : N1 K L) : (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (eOf K L σ hgen a)

def Hof (a : N1 K L) : AdelicGL2 (𝓞 L) L := globalPoints (𝓞 L) L (diagOne (eOf K L σ hgen a))

theorem Hof_eq (a : N1 K L) : Hof K L σ hgen a = diagOne (Eid K L σ hgen a) := map_diagOne _ _

theorem Hof_inv_mul_word (a : N1 K L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) :
    (Hof K L σ hgen a)⁻¹ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) =
      unipotentGL2 (((Eid K L σ hgen a)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) * x) * diagOne ((Eid K L σ hgen a)⁻¹ * t) *
        (k : AdelicGL2 (𝓞 L) L) := by
  rw [Hof_eq, ← mul_assoc, ← mul_assoc, diagOne_inv_mul_unipotentGL2, mul_assoc (unipotentGL2 _), ← map_inv, ← map_mul]

theorem Wa_eq_W1 (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : N1 K L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Wa K L D σ hgen R φ a ζ g = W1 K L D σ hgen R φ ζ ((Hof K L σ hgen a)⁻¹ * g) := by
  obtain ⟨hK, hT⟩ := (finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq K L D σ hgen φ R).1
    (eOf K L σ hgen a) ((a : Lˣ) : L) (eOf_spec K L σ hgen a) ζ g
  exact congrArg₂ (· - ·) hK hT

theorem W1_unipotent_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (l : L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    W1 K L D σ hgen R φ ζ (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = W1 K L D σ hgen R φ ζ g := by
  obtain ⟨hK, hT⟩ := (finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq K L D σ hgen φ R).2 l ζ g
  exact congrArg₂ (· - ·) hK hT

theorem W1_eq_W1_torus_of_fixed (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) {e : Lˣ} (he : σ (e : L) = (e : L))
    (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    W1 K L D σ hgen R φ ζ g = W1 K L D σ hgen R φ ζ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) := by
  obtain ⟨hK, hT⟩ := (finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq K L D σ hgen φ R).1
    e 1 (by rw [one_mul, he]) ζ g
  exact congrArg₂ (· - ·) hK hT

end Fibres

section Zeta

open AutomorphicForm.TwistedBruhat

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
variable (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
variable (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ)

def Afun (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ := ∫⁻ ζ, ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ * ‖W1 K L D σ hgen R φ ζ g‖ₑ ∂νZL

def Ufun (g : AdelicGL2 (𝓞 L) L) : ℂ := ∫ ζ, ((ξ' ζ : ℂˣ) : ℂ) * W1 K L D σ hgen R φ ζ g ∂νZL

def Finf (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ ζ, ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ * ∑' a : N1 K L, ‖Wa K L D σ hgen R φ a ζ g‖ₑ ∂νZL

def Linf (g : AdelicGL2 (𝓞 L) L) : ℂ := ∫ ζ, ((ξ' ζ : ℂˣ) : ℂ) * ∑' a : N1 K L, Wa K L D σ hgen R φ a ζ g ∂νZL

variable (hφc : Continuous φ) (hφs : HasCompactSupport φ)
variable (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ))

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

include hφc hφs in
theorem measurable_W1 : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => W1 K L D σ hgen R φ p.2 p.1 :=
  measurable_Kgen_sub_Tgen L K D σ φ hφc hφs R _ _

include hφc hφs hξc in
theorem measurable_integrandA :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ‖((ξ' p.2 : ℂˣ) : ℂ)‖ₑ * ‖W1 K L D σ hgen R φ p.2 p.1‖ₑ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hξc.comp continuous_snd).measurable.enorm.mul (measurable_W1 K L D σ hgen R φ hφc hφs).enorm

include hφc hφs hξc in
theorem measurable_integrandU :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ((ξ' p.2 : ℂˣ) : ℂ) * W1 K L D σ hgen R φ p.2 p.1 := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hξc.comp continuous_snd).measurable.mul (measurable_W1 K L D σ hgen R φ hφc hφs)

include hφc hφs hξc in
theorem measurable_A_slice (g : AdelicGL2 (𝓞 L) L) :
    Measurable fun ζ : (AdeleRing (𝓞 L) L)ˣ => ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ * ‖W1 K L D σ hgen R φ ζ g‖ₑ :=
  (measurable_integrandA K L D σ hgen ξ' R φ hφc hφs hξc).of_uncurry_left
    (f := fun (g : AdelicGL2 (𝓞 L) L) (ζ : (AdeleRing (𝓞 L) L)ˣ) => ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ * ‖W1 K L D σ hgen R φ ζ g‖ₑ)

include hφc hφs hξc in
theorem measurable_U_slice (g : AdelicGL2 (𝓞 L) L) :
    Measurable fun ζ : (AdeleRing (𝓞 L) L)ˣ => ((ξ' ζ : ℂˣ) : ℂ) * W1 K L D σ hgen R φ ζ g :=
  (measurable_integrandU K L D σ hgen ξ' R φ hφc hφs hξc).of_uncurry_left
    (f := fun (g : AdelicGL2 (𝓞 L) L) (ζ : (AdeleRing (𝓞 L) L)ˣ) => ((ξ' ζ : ℂˣ) : ℂ) * W1 K L D σ hgen R φ ζ g)

include hφc hφs hξc in

theorem measurable_Afun : Measurable (Afun K L D σ hgen νZL ξ' R φ) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  haveI : SigmaFinite νZL := inferInstance
  exact (measurable_integrandA K L D σ hgen ξ' R φ hφc hφs hξc).lintegral_prod_right'

include hφc hφs hξc in

theorem measurable_Ufun : Measurable (Ufun K L D σ hgen νZL ξ' R φ) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  haveI : SigmaFinite νZL := inferInstance
  exact ((measurable_integrandU K L D σ hgen ξ' R φ hφc hφs hξc).stronglyMeasurable.integral_prod_right'
    (ν := νZL)).measurable

theorem enorm_Ufun_le (g : AdelicGL2 (𝓞 L) L) : ‖Ufun K L D σ hgen νZL ξ' R φ g‖ₑ ≤ Afun K L D σ hgen νZL ξ' R φ g := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun ζ => ?_))
  rw [enorm_mul]

include hφc hφs hξc in

theorem Finf_eq (g : AdelicGL2 (𝓞 L) L) :
    Finf K L D σ hgen νZL ξ' R φ g = ∑' a : N1 K L, Afun K L D σ hgen νZL ξ' R φ ((Hof K L σ hgen a)⁻¹ * g) := by
  haveI : Countable Lˣ := countable_units L
  unfold Finf Afun
  rw [← lintegral_tsum fun a => (measurable_A_slice K L D σ hgen ξ' R φ hφc hφs hξc ((Hof K L σ hgen a)⁻¹ * g)).aemeasurable]
  refine lintegral_congr fun ζ => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by rw [Wa_eq_W1]

include hφc hφs hξc in

theorem Linf_eq (g : AdelicGL2 (𝓞 L) L) (hg : Finf K L D σ hgen νZL ξ' R φ g < ⊤) :
    Linf K L D σ hgen νZL ξ' R φ g = ∑' a : N1 K L, Ufun K L D σ hgen νZL ξ' R φ ((Hof K L σ hgen a)⁻¹ * g) := by
  haveI : Countable Lˣ := countable_units L
  unfold Linf Ufun
  rw [← integral_tsum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show ((ξ' ζ : ℂˣ) : ℂ) * ∑' a : N1 K L, Wa K L D σ hgen R φ a ζ g = _
    rw [← tsum_mul_left]
    exact tsum_congr fun a => by rw [Wa_eq_W1]
  · exact fun a => (measurable_U_slice K L D σ hgen ξ' R φ hφc hφs hξc ((Hof K L σ hgen a)⁻¹ * g)).aestronglyMeasurable
  · rw [Finf_eq K L D σ hgen νZL ξ' R φ hφc hφs hξc] at hg
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (tsum_congr fun a => lintegral_congr fun ζ => ?_)) hg)
    rw [enorm_mul]

theorem Afun_unipotent_mul (l : L) (g : AdelicGL2 (𝓞 L) L) :
    Afun K L D σ hgen νZL ξ' R φ (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = Afun K L D σ hgen νZL ξ' R φ g :=
  lintegral_congr fun ζ => by rw [W1_unipotent_mul]

theorem Ufun_unipotent_mul (l : L) (g : AdelicGL2 (𝓞 L) L) :
    Ufun K L D σ hgen νZL ξ' R φ (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = Ufun K L D σ hgen νZL ξ' R φ g :=
  integral_congr_ae (Filter.Eventually.of_forall fun ζ => by simp only [W1_unipotent_mul])

theorem Afun_torus_fixed {e : Lˣ} (he : σ (e : L) = (e : L)) (g : AdelicGL2 (𝓞 L) L) :
    Afun K L D σ hgen νZL ξ' R φ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = Afun K L D σ hgen νZL ξ' R φ g :=
  lintegral_congr fun ζ => by rw [← W1_eq_W1_torus_of_fixed K L D σ hgen R φ he]

theorem Ufun_torus_fixed {e : Lˣ} (he : σ (e : L) = (e : L)) (g : AdelicGL2 (𝓞 L) L) :
    Ufun K L D σ hgen νZL ξ' R φ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = Ufun K L D σ hgen νZL ξ' R φ g :=
  integral_congr_ae (Filter.Eventually.of_forall fun ζ => by simp only [← W1_eq_W1_torus_of_fixed K L D σ hgen R φ he])

end Zeta

section XT

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

abbrev pE (e : Lˣ) : (AdeleRing (𝓞 L) L)ˣ := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e

theorem distribHaarChar_pE (e : Lˣ) : distribHaarChar (AdeleRing (𝓞 L) L) (pE L e) = 1 := by
  have h := ideleNorm_principal L e
  rw [NumberField.TateGlobal.ideleNorm] at h
  exact_mod_cast h

theorem regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  show (Measure.addHaar : Measure (AdeleRing (𝓞 L) L)).Regular
  rw [Measure.addHaar]; infer_instance

variable {L} in
theorem measurePreserving_smul_of_distribHaarChar_eq_one {u : (AdeleRing (𝓞 L) L)ˣ}
    (hu : distribHaarChar (AdeleRing (𝓞 L) L) u = 1) :
    MeasurePreserving (fun q : AdeleRing (𝓞 L) L => u • q) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  haveI := regular_adelicAddHaar L
  refine ⟨measurable_const_smul u, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_smul u) hs, Set.preimage_smul, ← distribHaarChar_mul, map_inv, hu, inv_one,
    ENNReal.coe_one, one_mul]

scoped instance : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 L) L) (AdeleRing (𝓞 L) L) :=
  ⟨fun c => measurable_const_add (c : AdeleRing (𝓞 L) L)⟩

scoped instance : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 L) L) (AdeleRing (𝓞 L) L) (adelicAddHaar (𝓞 L) L) :=
  ⟨fun c s hs => measure_preimage_add (adelicAddHaar (𝓞 L) L) (c : AdeleRing (𝓞 L) L) s⟩

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 L) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact (Set.countable_range (algebraMap L (AdeleRing (𝓞 L) L))).to_subtype

def prinMul (e : Lˣ) : AdeleRing.principalSubgroup (𝓞 L) L ≃ AdeleRing.principalSubgroup (𝓞 L) L where
  toFun g := ⟨algebraMap L (AdeleRing (𝓞 L) L) (e : L) * g, by obtain ⟨_, l, rfl⟩ := g; exact ⟨(e : L) * l, by simp⟩⟩
  invFun g := ⟨algebraMap L (AdeleRing (𝓞 L) L) ((e⁻¹ : Lˣ) : L) * g, by
    obtain ⟨_, l, rfl⟩ := g; exact ⟨((e⁻¹ : Lˣ) : L) * l, by simp⟩⟩
  left_inv g := by
    refine Subtype.ext ?_
    show algebraMap L _ ((e⁻¹ : Lˣ) : L) * (algebraMap L _ (e : L) * (g : AdeleRing (𝓞 L) L)) = g
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  right_inv g := by
    refine Subtype.ext ?_
    show algebraMap L _ (e : L) * (algebraMap L _ ((e⁻¹ : Lˣ) : L) * (g : AdeleRing (𝓞 L) L)) = g
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

theorem isAddFundamentalDomain_smul (e : Lˣ) {X : Set (AdeleRing (𝓞 L) L)}
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L)) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) ((pE L e)⁻¹ • X) (adelicAddHaar (𝓞 L) L) := by
  set f : AdeleRing (𝓞 L) L ≃ AdeleRing (𝓞 L) L := MulAction.toPerm ((pE L e)⁻¹) with hf
  have hfimg : f '' X = (pE L e)⁻¹ • X := by rw [← Set.image_smul]; rfl
  rw [← hfimg]
  refine hX.image_of_equiv f ?_ (prinMul L e) fun g x => ?_
  · have hsymm : (f.symm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = fun q => (pE L e) • q := by
      funext q; simp [hf, MulAction.toPerm_symm_apply, inv_inv]
    rw [hsymm]
    exact (measurePreserving_smul_of_distribHaarChar_eq_one (distribHaarChar_pE L e)).quasiMeasurePreserving
  · show (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * (algebraMap L _ (e : L) * (g : AdeleRing (𝓞 L) L) + x) =
      (g : AdeleRing (𝓞 L) L) + (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * x
    have hEe : (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * algebraMap L _ (e : L) = 1 := Units.inv_mul (pE L e)
    rw [mul_add, ← mul_assoc, hEe, one_mul]

theorem setLIntegral_X_smul (e : Lˣ) {X : Set (AdeleRing (𝓞 L) L)}
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (P : AdeleRing (𝓞 L) L → ℝ≥0∞) (hP : ∀ (l : L) (q : AdeleRing (𝓞 L) L), P (algebraMap L (AdeleRing (𝓞 L) L) l + q) = P q) :
    ∫⁻ x in X, P (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) ∂adelicAddHaar (𝓞 L) L = ∫⁻ x in X, P x ∂adelicAddHaar (𝓞 L) L := by
  haveI := countable_principalSubgroup L
  have hE1 : distribHaarChar (AdeleRing (𝓞 L) L) (pE L e)⁻¹ = 1 := by rw [map_inv, distribHaarChar_pE, inv_one]
  have hmp := measurePreserving_smul_of_distribHaarChar_eq_one hE1
  have hpre : (fun q : AdeleRing (𝓞 L) L => (pE L e)⁻¹ • q) ⁻¹' ((pE L e)⁻¹ • X) = X := by ext q; exact Set.smul_mem_smul_set_iff
  calc ∫⁻ x in X, P ((pE L e)⁻¹ • x) ∂adelicAddHaar (𝓞 L) L
      = ∫⁻ x in (fun q : AdeleRing (𝓞 L) L => (pE L e)⁻¹ • q) ⁻¹' ((pE L e)⁻¹ • X), P ((pE L e)⁻¹ • x) ∂adelicAddHaar (𝓞 L) L := by
        rw [hpre]
    _ = ∫⁻ x in (pE L e)⁻¹ • X, P x ∂adelicAddHaar (𝓞 L) L := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_const_smul _) P _
    _ = ∫⁻ x in X, P x ∂adelicAddHaar (𝓞 L) L :=
        (isAddFundamentalDomain_smul L e hX).setLIntegral_eq hX P fun g q => by
          obtain ⟨_, l, rfl⟩ := g; exact hP l q

theorem setIntegral_X_smul (e : Lˣ) {X : Set (AdeleRing (𝓞 L) L)}
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (P : AdeleRing (𝓞 L) L → ℂ) (hP : ∀ (l : L) (q : AdeleRing (𝓞 L) L), P (algebraMap L (AdeleRing (𝓞 L) L) l + q) = P q) :
    ∫ x in X, P (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) ∂adelicAddHaar (𝓞 L) L = ∫ x in X, P x ∂adelicAddHaar (𝓞 L) L := by
  haveI := countable_principalSubgroup L
  have hE1 : distribHaarChar (AdeleRing (𝓞 L) L) (pE L e)⁻¹ = 1 := by rw [map_inv, distribHaarChar_pE, inv_one]
  have hmp := measurePreserving_smul_of_distribHaarChar_eq_one hE1
  have hpre : (fun q : AdeleRing (𝓞 L) L => (pE L e)⁻¹ • q) ⁻¹' ((pE L e)⁻¹ • X) = X := by ext q; exact Set.smul_mem_smul_set_iff
  calc ∫ x in X, P ((pE L e)⁻¹ • x) ∂adelicAddHaar (𝓞 L) L
      = ∫ x in (fun q : AdeleRing (𝓞 L) L => (pE L e)⁻¹ • q) ⁻¹' ((pE L e)⁻¹ • X), P ((pE L e)⁻¹ • x) ∂adelicAddHaar (𝓞 L) L := by
        rw [hpre]
    _ = ∫ x in (pE L e)⁻¹ • X, P x ∂adelicAddHaar (𝓞 L) L := hmp.setIntegral_preimage_emb (measurableEmbedding_const_smul _) P _
    _ = ∫ x in X, P x ∂adelicAddHaar (𝓞 L) L :=
        (isAddFundamentalDomain_smul L e hX).setIntegral_eq hX fun g q => by
          obtain ⟨_, l, rfl⟩ := g; exact hP l q

abbrev ΓL : Subgroup (AdeleRing (𝓞 L) L)ˣ := (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range

abbrev ΓK : Subgroup (AdeleRing (𝓞 L) L)ˣ :=
  ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
    (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range

theorem idelesBaseChange_principal (κ : Kˣ) :
    (AutomorphicForm.TransversalMeasure.idelesBaseChange K L)
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) κ) =
      pE L (Units.map (algebraMap K L : K →* L) κ) :=
  Units.ext (M4aHerbrand.Bridge.genuineβ_compat K L (κ : K))

theorem mem_ΓK_iff (u : (AdeleRing (𝓞 L) L)ˣ) : u ∈ ΓK K L ↔ ∃ κ : Kˣ, u = pE L (Units.map (algebraMap K L : K →* L) κ) := by
  constructor
  · rintro ⟨κ, rfl⟩; exact ⟨κ, idelesBaseChange_principal K L κ⟩
  · rintro ⟨κ, rfl⟩; exact ⟨κ, idelesBaseChange_principal K L κ⟩

theorem ΓK_le_ΓL : ΓK K L ≤ ΓL L := by
  intro u hu
  obtain ⟨κ, rfl⟩ := (mem_ΓK_iff K L u).mp hu
  exact ⟨_, rfl⟩

theorem pE_injective : Function.Injective (pE L) := by
  intro e e' h
  exact Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L (congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h))

theorem norm_map_algEquiv (x : L) : Algebra.norm K (σ x) = Algebra.norm K x := Algebra.norm_eq_of_algEquiv σ x

include hgen in

def Rrep (a : N1 K L) : ΓL L := ⟨Eid K L σ hgen a, ⟨eOf K L σ hgen a, rfl⟩⟩

theorem Rrep_coe (a : N1 K L) : ((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ) = Eid K L σ hgen a := rfl

theorem coe_a_eq (a : N1 K L) : ((a : Lˣ) : L) = (eOf K L σ hgen a : L) * (σ (eOf K L σ hgen a : L))⁻¹ := by
  have hσe : σ (eOf K L σ hgen a : L) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact (eOf K L σ hgen a).ne_zero
  exact (eq_mul_inv_iff_mul_eq₀ hσe).mpr (eOf_spec K L σ hgen a)

include hgen in

theorem existsUnique_coset (γ : ΓL L) :
    ∃! a : N1 K L, (((Rrep K L σ hgen a)⁻¹ * γ : ΓL L) : (AdeleRing (𝓞 L) L)ˣ) ∈ ΓK K L := by
  obtain ⟨_, ℓ, rfl⟩ := γ
  have hval : ∀ a : N1 K L, (((Rrep K L σ hgen a)⁻¹ *
      (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ℓ, ⟨ℓ, rfl⟩⟩ : ΓL L) : ΓL L) :
        (AdeleRing (𝓞 L) L)ˣ) = pE L ((eOf K L σ hgen a)⁻¹ * ℓ) := by
    intro a
    show (Eid K L σ hgen a)⁻¹ * pE L ℓ = pE L ((eOf K L σ hgen a)⁻¹ * ℓ)
    simp only [Eid, pE, map_mul, map_inv]
  have hiff : ∀ a : N1 K L, pE L ((eOf K L σ hgen a)⁻¹ * ℓ) ∈ ΓK K L ↔
      ∃ κ : Kˣ, (eOf K L σ hgen a)⁻¹ * ℓ = Units.map (algebraMap K L : K →* L) κ := by
    intro a
    rw [mem_ΓK_iff]
    exact ⟨fun ⟨κ, h⟩ => ⟨κ, pE_injective L h⟩, fun ⟨κ, h⟩ => ⟨κ, by rw [h]⟩⟩
  simp only [hval, hiff]
  have hσℓ : σ (ℓ : L) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact ℓ.ne_zero

  have hdet : ∀ (a : N1 K L) (κ : Kˣ), (eOf K L σ hgen a)⁻¹ * ℓ = Units.map (algebraMap K L : K →* L) κ →
      ((a : Lˣ) : L) = (ℓ : L) * (σ (ℓ : L))⁻¹ := by
    intro a κ h
    have h' : ((eOf K L σ hgen a : L))⁻¹ * (ℓ : L) = algebraMap K L (κ : K) := by
      have h'' := congrArg (fun u : Lˣ => (u : L)) h
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h''
      exact h''
    have hκ : algebraMap K L (κ : K) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact κ.ne_zero
    have he : (eOf K L σ hgen a : L) = (ℓ : L) * (algebraMap K L (κ : K))⁻¹ := by
      rw [← h', mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel₀ ℓ.ne_zero, one_mul]
    rw [coe_a_eq K L σ hgen a, he, map_mul, map_inv₀, AlgEquiv.commutes]
    field_simp
  refine ⟨⟨ℓ * (Units.map ((σ : L →+* L) : L →* L) ℓ)⁻¹, ?_⟩, ?_, ?_⟩
  · show Algebra.norm K ((ℓ : L) * ((Units.map ((σ : L →+* L) : L →* L) ℓ)⁻¹ : Lˣ)) = 1
    rw [Units.val_inv_eq_inv_val]
    show Algebra.norm K ((ℓ : L) * (σ (ℓ : L))⁻¹) = 1
    have hN : Algebra.norm K ((ℓ : L) * (σ (ℓ : L))⁻¹) * Algebra.norm K (σ (ℓ : L)) = Algebra.norm K (σ (ℓ : L)) := by
      rw [← map_mul, inv_mul_cancel_right₀ hσℓ, norm_map_algEquiv]
    exact (mul_eq_right₀ (by rw [norm_map_algEquiv]; exact Algebra.norm_ne_zero_iff.mpr ℓ.ne_zero)).mp hN
  ·
    set a₀ : N1 K L := ⟨ℓ * (Units.map ((σ : L →+* L) : L →* L) ℓ)⁻¹, _⟩ with ha₀
    have ha₀v : ((a₀ : Lˣ) : L) = (ℓ : L) * (σ (ℓ : L))⁻¹ := by
      show ((ℓ * (Units.map ((σ : L →+* L) : L →* L) ℓ)⁻¹ : Lˣ) : L) = _
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl
    set e₀ := eOf K L σ hgen a₀ with he₀
    have hσe : σ (e₀ : L) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact e₀.ne_zero
    have hfix : σ (((e₀⁻¹ * ℓ : Lˣ) : L)) = ((e₀⁻¹ * ℓ : Lˣ) : L) := by
      have h1 : (e₀ : L) * (σ (e₀ : L))⁻¹ = (ℓ : L) * (σ (ℓ : L))⁻¹ := by rw [← coe_a_eq K L σ hgen a₀, ha₀v]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      field_simp
      field_simp at h1
      linear_combination h1
    obtain ⟨κ₀, hκ₀⟩ := LT.TwistedNorm.mem_range_algebraMap_of_generator_apply_eq hgen hfix
    have hκ₀0 : κ₀ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hκ₀; exact (e₀⁻¹ * ℓ).ne_zero hκ₀.symm
    exact ⟨Units.mk0 κ₀ hκ₀0, Units.ext (by rw [Units.coe_map, MonoidHom.coe_coe, Units.val_mk0, hκ₀])⟩
  ·
    rintro a ⟨κ, hκ⟩
    have h1 := hdet a κ hκ
    refine Subtype.ext (Units.ext ?_)
    rw [h1]
    show (ℓ : L) * (σ (ℓ : L))⁻¹ = ((ℓ * (Units.map ((σ : L →+* L) : L →* L) ℓ)⁻¹ : Lˣ) : L)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl

end XT

section Unfold

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar L) := by
  haveI := secondCountableTopology_idele L; infer_instance

theorem sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 L) L) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  infer_instance

def word (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) : AdelicGL2 (𝓞 L) L :=
  unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)

def wt (t : (AdeleRing (𝓞 L) L)ˣ) : ℝ≥0∞ := ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹

def wc (t : (AdeleRing (𝓞 L) L)ˣ) : ℂ := (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)

theorem enorm_wc (t : (AdeleRing (𝓞 L) L)ˣ) : ‖wc L t‖ₑ = wt L t := by
  rw [wc, wt, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (NumberField.TateGlobal.ideleNorm_pos t).le)]

theorem wt_pE_inv_mul (e : Lˣ) (t : (AdeleRing (𝓞 L) L)ˣ) : wt L ((pE L e)⁻¹ * t) = wt L t := by
  rw [wt, wt, ideleNorm_prin_inv_mul]

theorem wc_pE_inv_mul (e : Lˣ) (t : (AdeleRing (𝓞 L) L)ˣ) : wc L ((pE L e)⁻¹ * t) = wc L t := by
  rw [wc, wc, ideleNorm_prin_inv_mul]

theorem wt_pE_mul (e : Lˣ) (t : (AdeleRing (𝓞 L) L)ˣ) : wt L (pE L e * t) = wt L t := by
  rw [← wt_pE_inv_mul L e (pE L e * t), inv_mul_cancel_left]

theorem wc_pE_mul (e : Lˣ) (t : (AdeleRing (𝓞 L) L)ˣ) : wc L (pE L e * t) = wc L t := by
  rw [← wc_pE_inv_mul L e (pE L e * t), inv_mul_cancel_left]

theorem torus_word (e : Lˣ) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) :
    (globalPoints (𝓞 L) L (diagOne e))⁻¹ * word L x t k = word L (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) ((pE L e)⁻¹ * t) k := by
  rw [word, word, show globalPoints (𝓞 L) L (diagOne e) = diagOne (pE L e) from map_diagOne _ _, ← mul_assoc, ← mul_assoc,
    diagOne_inv_mul_unipotentGL2, mul_assoc (unipotentGL2 _), ← map_inv diagOne, ← map_mul diagOne]
  rfl

theorem unipotent_word (l : L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) :
    globalPoints (𝓞 L) L (unipotentGL2 l) * word L x t k = word L (algebraMap L (AdeleRing (𝓞 L) L) l + x) t k :=
  unipotent_mul_word L l x t k

theorem continuous_word' : Continuous fun r : ((AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) × adelicMaximalCompact L =>
    word L r.1.1 r.1.2 r.2 := continuous_word L

theorem measurable_wt : Measurable (wt L) :=
  ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm L).measurable.inv

theorem continuous_wc : Continuous (wc L) :=
  Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm L).inv₀
    fun t => (NumberField.TateGlobal.ideleNorm_pos t).ne')

def Φf (A : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) : ℝ≥0∞ :=
  ∫⁻ k, A (word L x t k) * wt L t ∂maximalCompactHaar L

def Ψf (A : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (X : Set (AdeleRing (𝓞 L) L)) (t : (AdeleRing (𝓞 L) L)ˣ) : ℝ≥0∞ :=
  ∫⁻ x in X, Φf L A x t ∂adelicAddHaar (𝓞 L) L

def Vf (U : AdelicGL2 (𝓞 L) L → ℂ) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∫ k, U (word L x t k) * wc L t ∂maximalCompactHaar L

def Vtf (U : AdelicGL2 (𝓞 L) L → ℂ) (X : Set (AdeleRing (𝓞 L) L)) (t : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∫ x in X, Vf L U x t ∂adelicAddHaar (𝓞 L) L

variable {A : AdelicGL2 (𝓞 L) L → ℝ≥0∞} {U : AdelicGL2 (𝓞 L) L → ℂ}

theorem measurable_Aword (hA : Measurable A) :
    Measurable fun r : ((AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) × adelicMaximalCompact L =>
      A (word L r.1.1 r.1.2 r.2) * wt L r.1.2 := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hA.comp (continuous_word L).measurable).mul ((measurable_wt L).comp (measurable_snd.comp measurable_fst))

theorem measurable_Uword (hU : Measurable U) :
    Measurable fun r : ((AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) × adelicMaximalCompact L =>
      U (word L r.1.1 r.1.2 r.2) * wc L r.1.2 := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hU.comp (continuous_word L).measurable).mul ((continuous_wc L).measurable.comp (measurable_snd.comp measurable_fst))

theorem measurable_Φf (hA : Measurable A) : Measurable fun q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ => Φf L A q.1 q.2 :=
  (measurable_Aword L hA).lintegral_prod_right'

theorem measurable_Ψf (hA : Measurable A) (X : Set (AdeleRing (𝓞 L) L)) : Measurable (Ψf L A X) := by
  haveI := sigmaFinite_adelicAddHaar L
  exact (measurable_Φf L hA).lintegral_prod_left' (μ := (adelicAddHaar (𝓞 L) L).restrict X)

theorem stronglyMeasurable_Vf (hU : Measurable U) :
    StronglyMeasurable fun q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ => Vf L U q.1 q.2 :=
  (measurable_Uword L hU).stronglyMeasurable.integral_prod_right'

theorem stronglyMeasurable_Vtf (hU : Measurable U) (X : Set (AdeleRing (𝓞 L) L)) : StronglyMeasurable (Vtf L U X) := by
  haveI := sigmaFinite_adelicAddHaar L
  exact (stronglyMeasurable_Vf L hU).integral_prod_left' (μ := (adelicAddHaar (𝓞 L) L).restrict X)

theorem enorm_Vf_le (hUA : ∀ g, ‖U g‖ₑ ≤ A g) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    ‖Vf L U x t‖ₑ ≤ Φf L A x t := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun k => ?_)
  rw [enorm_mul, enorm_wc]
  exact mul_le_mul_left (hUA _) _

theorem enorm_Vtf_le (hUA : ∀ g, ‖U g‖ₑ ≤ A g) (X : Set (AdeleRing (𝓞 L) L)) (t : (AdeleRing (𝓞 L) L)ˣ) :
    ‖Vtf L U X t‖ₑ ≤ Ψf L A X t :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => enorm_Vf_le L hUA x t)

theorem Φf_add (hAu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), A (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = A g)
    (l : L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Φf L A (algebraMap L (AdeleRing (𝓞 L) L) l + x) t = Φf L A x t :=
  lintegral_congr fun k => by rw [← unipotent_word, hAu]

theorem Vf_add (hUu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), U (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = U g)
    (l : L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Vf L U (algebraMap L (AdeleRing (𝓞 L) L) l + x) t = Vf L U x t :=
  integral_congr_ae (Filter.Eventually.of_forall fun k => by simp only [← unipotent_word, hUu])

theorem Φf_pE_mul (hAt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, A ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = A g)
    {e : Lˣ} (he : σ (e : L) = (e : L)) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Φf L A x (pE L e * t) = Φf L A (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) t :=
  lintegral_congr fun k => by rw [← hAt e he (word L x (pE L e * t) k), torus_word, inv_mul_cancel_left, wt_pE_mul]

theorem Vf_pE_mul (hUt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, U ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = U g)
    {e : Lˣ} (he : σ (e : L) = (e : L)) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Vf L U x (pE L e * t) = Vf L U (((pE L e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) t :=
  integral_congr_ae (Filter.Eventually.of_forall fun k => by
    simp only [← hUt e he (word L x (pE L e * t) k), torus_word, inv_mul_cancel_left, wc_pE_mul])

theorem Ψf_smul (hAu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), A (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = A g)
    (hAt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, A ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = A g)
    {X : Set (AdeleRing (𝓞 L) L)} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (u : ΓK K L) (t : (AdeleRing (𝓞 L) L)ˣ) : Ψf L A X (u • t) = Ψf L A X t := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨κ, rfl⟩ := (mem_ΓK_iff K L u).mp hu
  have he : σ ((Units.map (algebraMap K L : K →* L) κ : Lˣ) : L) = ((Units.map (algebraMap K L : K →* L) κ : Lˣ) : L) :=
    σ.commutes (κ : K)
  rw [Subgroup.mk_smul, smul_eq_mul]
  unfold Ψf
  rw [show (fun x => Φf L A x (pE L (Units.map (algebraMap K L : K →* L) κ) * t)) =
      fun x => Φf L A (((pE L (Units.map (algebraMap K L : K →* L) κ))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) t from
    funext fun x => Φf_pE_mul K L σ hAt he x t]
  exact setLIntegral_X_smul L _ hX (fun x => Φf L A x t) fun l q => Φf_add L hAu l q t

theorem Vtf_smul (hUu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), U (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = U g)
    (hUt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, U ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = U g)
    {X : Set (AdeleRing (𝓞 L) L)} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (u : ΓK K L) (t : (AdeleRing (𝓞 L) L)ˣ) : Vtf L U X (u • t) = Vtf L U X t := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨κ, rfl⟩ := (mem_ΓK_iff K L u).mp hu
  have he : σ ((Units.map (algebraMap K L : K →* L) κ : Lˣ) : L) = ((Units.map (algebraMap K L : K →* L) κ : Lˣ) : L) :=
    σ.commutes (κ : K)
  rw [Subgroup.mk_smul, smul_eq_mul]
  unfold Vtf
  rw [show (fun x => Vf L U x (pE L (Units.map (algebraMap K L : K →* L) κ) * t)) =
      fun x => Vf L U (((pE L (Units.map (algebraMap K L : K →* L) κ))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x) t from
    funext fun x => Vf_pE_mul K L σ hUt he x t]
  exact setIntegral_X_smul L _ hX (fun x => Vf L U x t) fun l q => Vf_add L hUu l q t

theorem countable_ΓK : Countable (ΓK K L) := by
  haveI : Countable Kˣ := countable_units K
  exact (MonoidHom.rangeRestrict_surjective _).countable

theorem smulInvariantMeasure_subgroup (H : Subgroup (AdeleRing (𝓞 L) L)ˣ) :
    SMulInvariantMeasure H (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.idelicHaar L) :=
  ⟨fun c s _ => measure_preimage_mul (NumberField.Idele.idelicHaar L) (c : (AdeleRing (𝓞 L) L)ˣ) s⟩

def sx (a : N1 K L) (x : AdeleRing (𝓞 L) L) : AdeleRing (𝓞 L) L := ((Eid K L σ hgen a)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • x

def st (a : N1 K L) (t : (AdeleRing (𝓞 L) L)ˣ) : (AdeleRing (𝓞 L) L)ˣ := (Eid K L σ hgen a)⁻¹ * t

theorem Hof_inv_mul_word' (a : N1 K L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) :
    (Hof K L σ hgen a)⁻¹ * word L x t k = word L (sx K L σ hgen a x) (st K L σ hgen a t) k :=
  torus_word L (eOf K L σ hgen a) x t k

theorem wt_st (a : N1 K L) (t : (AdeleRing (𝓞 L) L)ˣ) : wt L (st K L σ hgen a t) = wt L t := wt_pE_inv_mul L _ t

theorem wc_st (a : N1 K L) (t : (AdeleRing (𝓞 L) L)ˣ) : wc L (st K L σ hgen a t) = wc L t := wc_pE_inv_mul L _ t

theorem continuous_shift (a : N1 K L) :
    Continuous fun q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ => (sx K L σ hgen a q.1, st K L σ hgen a q.2) :=
  (continuous_fst.const_smul _).prodMk (continuous_snd.const_mul _)

def Gf (A : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) : ℝ≥0∞ :=
  ∑' a : N1 K L, Φf L A (sx K L σ hgen a q.1) (st K L σ hgen a q.2)

def SVf (U : AdelicGL2 (𝓞 L) L → ℂ) (q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∑' a : N1 K L, Vf L U (sx K L σ hgen a q.1) (st K L σ hgen a q.2)

theorem measurable_Aword_shift (hA : Measurable A) (a : N1 K L) :
    Measurable fun r : ((AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) × adelicMaximalCompact L =>
      A (word L (sx K L σ hgen a r.1.1) (st K L σ hgen a r.1.2) r.2) * wt L (st K L σ hgen a r.1.2) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hA.comp ((continuous_word L).comp (((continuous_shift K L σ hgen a).comp continuous_fst).prodMk
    continuous_snd)).measurable).mul ((measurable_wt L).comp ((measurable_snd.comp measurable_fst).const_mul _))

theorem measurable_Uword_shift (hU : Measurable U) (a : N1 K L) :
    Measurable fun r : ((AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) × adelicMaximalCompact L =>
      U (word L (sx K L σ hgen a r.1.1) (st K L σ hgen a r.1.2) r.2) * wc L (st K L σ hgen a r.1.2) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hU.comp ((continuous_word L).comp (((continuous_shift K L σ hgen a).comp continuous_fst).prodMk
    continuous_snd)).measurable).mul ((continuous_wc L).measurable.comp ((measurable_snd.comp measurable_fst).const_mul _))

theorem measurable_Φf_shift (hA : Measurable A) (a : N1 K L) :
    Measurable fun q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ => Φf L A (sx K L σ hgen a q.1) (st K L σ hgen a q.2) :=
  (measurable_Aword_shift K L σ hgen hA a).lintegral_prod_right'

theorem stronglyMeasurable_Vf_shift (hU : Measurable U) (a : N1 K L) :
    StronglyMeasurable fun q : (AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ => Vf L U (sx K L σ hgen a q.1) (st K L σ hgen a q.2) :=
  (measurable_Uword_shift K L σ hgen hU a).stronglyMeasurable.integral_prod_right'

theorem measurable_Gf (hA : Measurable A) : Measurable (Gf K L σ hgen A) := by
  haveI : Countable Lˣ := countable_units L
  exact Measurable.ennreal_tsum fun a => measurable_Φf_shift K L σ hgen hA a

theorem measurable_SVf (hU : Measurable U) : Measurable (SVf K L σ hgen U) := by
  haveI : Countable Lˣ := countable_units L
  exact Measurable.tsum fun a => (stronglyMeasurable_Vf_shift K L σ hgen hU a).measurable

theorem measurable_Ashift (hA : Measurable A) (a : N1 K L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Measurable fun k : adelicMaximalCompact L => A (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wt L (st K L σ hgen a t) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hA.comp ((continuous_word L).comp ((continuous_const (y := (sx K L σ hgen a x, st K L σ hgen a t))).prodMk
    continuous_id)).measurable).mul measurable_const

theorem measurable_Ushift (hU : Measurable U) (a : N1 K L) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Measurable fun k : adelicMaximalCompact L => U (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wc L (st K L σ hgen a t) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  exact (hU.comp ((continuous_word L).comp ((continuous_const (y := (sx K L σ hgen a x, st K L σ hgen a t))).prodMk
    continuous_id)).measurable).mul measurable_const

theorem lintegral_Fi_word (A Fi : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hA : Measurable A)
    (hFiA : ∀ g, Fi g = ∑' a : N1 K L, A ((Hof K L σ hgen a)⁻¹ * g)) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    ∫⁻ k, Fi (word L x t k) * wt L t ∂maximalCompactHaar L = Gf K L σ hgen A (x, t) := by
  haveI : Countable Lˣ := countable_units L
  have h1 : ∀ k, Fi (word L x t k) * wt L t =
      ∑' a : N1 K L, A (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wt L (st K L σ hgen a t) := by
    intro k
    rw [hFiA, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun a => by rw [Hof_inv_mul_word', wt_st]
  simp_rw [h1]
  rw [lintegral_tsum fun a => (measurable_Ashift K L σ hgen hA a x t).aemeasurable]
  rfl

theorem Gf_eq_lintegral_tsum (hA : Measurable A) (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) :
    Gf K L σ hgen A (x, t) = ∫⁻ k, ∑' a : N1 K L, A (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wt L t ∂maximalCompactHaar L := by
  haveI : Countable Lˣ := countable_units L
  rw [lintegral_tsum fun a => ((measurable_Ashift K L σ hgen hA a x t).aemeasurable.congr
    (Filter.Eventually.of_forall fun k => by rw [wt_st]))]
  exact tsum_congr fun a => lintegral_congr fun k => by rw [wt_st]

theorem integral_Li_word (A Fi : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hA : Measurable A)
    (U Li : AdelicGL2 (𝓞 L) L → ℂ) (hU : Measurable U) (hUA : ∀ g, ‖U g‖ₑ ≤ A g)
    (hFiA : ∀ g, Fi g = ∑' a : N1 K L, A ((Hof K L σ hgen a)⁻¹ * g))
    (hLiU : ∀ g, Fi g < ⊤ → Li g = ∑' a : N1 K L, U ((Hof K L σ hgen a)⁻¹ * g))
    (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) (hG : Gf K L σ hgen A (x, t) < ⊤) :
    ∫ k, Li (word L x t k) * wc L t ∂maximalCompactHaar L = SVf K L σ hgen U (x, t) := by
  haveI : Countable Lˣ := countable_units L
  have hGk := Gf_eq_lintegral_tsum K L σ hgen hA x t
  have hae : ∀ᵐ k ∂maximalCompactHaar L, Fi (word L x t k) < ⊤ := by
    have h1 : ∀ᵐ k ∂maximalCompactHaar L,
        (∑' a : N1 K L, A (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wt L t) < ⊤ := by
      rw [hGk] at hG
      exact ae_lt_top' (AEMeasurable.ennreal_tsum fun a => ((measurable_Ashift K L σ hgen hA a x t).aemeasurable.congr
        (Filter.Eventually.of_forall fun k => by rw [wt_st]))) hG.ne
    refine h1.mono fun k hk => ?_
    rw [ENNReal.tsum_mul_right] at hk
    have hpos : wt L t ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos t))).ne'
    have h2 := ENNReal.lt_top_of_mul_ne_top_left hk.ne hpos
    rw [hFiA]; simpa only [Hof_inv_mul_word'] using h2
  calc ∫ k, Li (word L x t k) * wc L t ∂maximalCompactHaar L
      = ∫ k, ∑' a : N1 K L, U (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wc L (st K L σ hgen a t)
          ∂maximalCompactHaar L := by
        refine integral_congr_ae (hae.mono fun k hk => ?_)
        show Li (word L x t k) * wc L t = _
        rw [hLiU _ hk, ← tsum_mul_right]
        exact tsum_congr fun a => by rw [Hof_inv_mul_word', wc_st]
    _ = ∑' a : N1 K L, ∫ k, U (word L (sx K L σ hgen a x) (st K L σ hgen a t) k) * wc L (st K L σ hgen a t)
          ∂maximalCompactHaar L := by
        refine integral_tsum (fun a => (measurable_Ushift K L σ hgen hU a x t).aestronglyMeasurable)
          (ne_of_lt (lt_of_le_of_lt ?_ hG))
        rw [hGk, lintegral_tsum fun a => ((measurable_Ashift K L σ hgen hA a x t).aemeasurable.congr
          (Filter.Eventually.of_forall fun k => by rw [wt_st]))]
        refine ENNReal.tsum_le_tsum fun a => lintegral_mono fun k => ?_
        rw [enorm_mul, enorm_wc, wt_st]
        exact mul_le_mul_left (hUA _) _
    _ = SVf K L σ hgen U (x, t) := rfl

include hgen in

theorem chain2 (hA : Measurable A)
    (hAu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), A (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = A g)
    (hAt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, A ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = A g)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₂ Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂ : IsFundamentalDomain (ΓL L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hΩ₂K : IsFundamentalDomain (ΓK K L) Ω₂K (NumberField.Idele.idelicHaar L)) :
    ∫⁻ x in X, ∫⁻ t in Ω₂K, Φf L A x t ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L =
      ∫⁻ x in X, ∫⁻ t in Ω₂, Gf K L σ hgen A (x, t) ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L := by
  haveI := sigmaFinite_idelicHaar L
  haveI := sigmaFinite_adelicAddHaar L
  haveI : Countable Lˣ := countable_units L
  haveI : Countable (ΓL L) := (MonoidHom.rangeRestrict_surjective _).countable
  haveI := countable_ΓK K L
  haveI := smulInvariantMeasure_subgroup L (ΓK K L)
  have hΦm := measurable_Φf L hA
  have hGm := measurable_Gf K L σ hgen hA
  have hR := existsUnique_coset K L σ hgen
  have hΩ₂' := MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives (NumberField.Idele.idelicHaar L)
    (ΓL L) (ΓK K L) (ΓK_le_ΓL K L) Ω₂ hΩ₂ (Rrep K L σ hgen) hR
  have hunf := (MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives.{0, 0, 0, 0}
    (NumberField.Idele.idelicHaar L) (ΓL L) (ΓK K L) (ΓK_le_ΓL K L) Ω₂ hΩ₂ (Rrep K L σ hgen) hR).1
  have hΨsh : ∀ (a : N1 K L) t, Ψf L A X (st K L σ hgen a t) =
      ∫⁻ x in X, Φf L A (sx K L σ hgen a x) (st K L σ hgen a t) ∂adelicAddHaar (𝓞 L) L :=
    fun a t => (setLIntegral_X_smul L (eOf K L σ hgen a) hX (fun x => Φf L A x (st K L σ hgen a t))
      fun l q => Φf_add L hAu l q _).symm
  calc ∫⁻ x in X, ∫⁻ t in Ω₂K, Φf L A x t ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L
      = ∫⁻ t in Ω₂K, Ψf L A X t ∂NumberField.Idele.idelicHaar L := lintegral_lintegral_swap (f := Φf L A) hΦm.aemeasurable
    _ = ∫⁻ t in ⋃ a : N1 K L, ((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • Ω₂, Ψf L A X t ∂NumberField.Idele.idelicHaar L :=
        hΩ₂K.setLIntegral_eq hΩ₂' _ fun u t => Ψf_smul K L σ hAu hAt hX u t
    _ = ∫⁻ t in Ω₂, ∑' a : N1 K L, Ψf L A X (((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • t)
          ∂NumberField.Idele.idelicHaar L := hunf _ (measurable_Ψf L hA X)
    _ = ∫⁻ t in Ω₂, ∫⁻ x in X, Gf K L σ hgen A (x, t) ∂adelicAddHaar (𝓞 L) L ∂NumberField.Idele.idelicHaar L := by
        refine lintegral_congr fun t => ?_
        have h : ∀ a : N1 K L, Ψf L A X (((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • t) =
            ∫⁻ x in X, Φf L A (sx K L σ hgen a x) (st K L σ hgen a t) ∂adelicAddHaar (𝓞 L) L := fun a => hΨsh a t
        simp_rw [h]
        exact (lintegral_tsum fun a => ((measurable_Φf_shift K L σ hgen hA a).of_uncurry_right
          (f := fun x t' => Φf L A (sx K L σ hgen a x) (st K L σ hgen a t'))).aemeasurable).symm
    _ = ∫⁻ x in X, ∫⁻ t in Ω₂, Gf K L σ hgen A (x, t) ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L :=
        (lintegral_lintegral_swap (f := fun x t => Gf K L σ hgen A (x, t)) hGm.aemeasurable).symm

include hgen in

theorem torus_unfold (A Fi : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hA : Measurable A)
    (U Li : AdelicGL2 (𝓞 L) L → ℂ) (hU : Measurable U) (hUA : ∀ g, ‖U g‖ₑ ≤ A g)
    (hFiA : ∀ g, Fi g = ∑' a : N1 K L, A ((Hof K L σ hgen a)⁻¹ * g))
    (hLiU : ∀ g, Fi g < ⊤ → Li g = ∑' a : N1 K L, U ((Hof K L σ hgen a)⁻¹ * g))
    (hAu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), A (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = A g)
    (hUu : ∀ (l : L) (g : AdelicGL2 (𝓞 L) L), U (globalPoints (𝓞 L) L (unipotentGL2 l) * g) = U g)
    (hAt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, A ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = A g)
    (hUt : ∀ (e : Lˣ), σ (e : L) = (e : L) → ∀ g : AdelicGL2 (𝓞 L) L, U ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g) = U g)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₂ Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂ : IsFundamentalDomain (ΓL L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hΩ₂K : IsFundamentalDomain (ΓK K L) Ω₂K (NumberField.Idele.idelicHaar L))
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k, Fi (word L x t k) * wt L t
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫ x in X, ∫ t in Ω₂, ∫ k, Li (word L x t k) * wc L t
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) =
      ∫ x in X, ∫ t in Ω₂K, ∫ k, U (word L x t k) * wc L t
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L)) ∧
    (∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k, A (word L x t k) * wt L t
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) := by
  haveI := sigmaFinite_idelicHaar L
  haveI := sigmaFinite_adelicAddHaar L
  haveI : Countable Lˣ := countable_units L
  haveI : Countable (ΓL L) := (MonoidHom.rangeRestrict_surjective _).countable
  haveI := countable_ΓK K L
  haveI := smulInvariantMeasure_subgroup L (ΓK K L)
  have hΦm := measurable_Φf L hA
  have hGm := measurable_Gf K L σ hgen hA
  have hVsm := stronglyMeasurable_Vf L hU
  have hVΦ : ∀ x t, ‖Vf L U x t‖ₑ ≤ Φf L A x t := enorm_Vf_le L hUA
  have hfin' : ∫⁻ x in X, ∫⁻ t in Ω₂, Gf K L σ hgen A (x, t) ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L ≠ ⊤ := by
    simpa only [lintegral_Fi_word K L σ hgen A Fi hA hFiA] using hfin
  have hswap : ∫⁻ x in X, ∫⁻ t in Ω₂, Gf K L σ hgen A (x, t) ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L =
      ∫⁻ t in Ω₂, ∫⁻ x in X, Gf K L σ hgen A (x, t) ∂adelicAddHaar (𝓞 L) L ∂NumberField.Idele.idelicHaar L :=
    lintegral_lintegral_swap (f := fun x t => Gf K L σ hgen A (x, t)) hGm.aemeasurable
  have hc2 := chain2 K L σ hgen hA hAu hAt X Ω₂ Ω₂K hX hΩ₂ hΩ₂K
  refine ⟨?_, by rw [show (∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k, A (word L x t k) * wt L t ∂maximalCompactHaar L
    ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L) = ∫⁻ x in X, ∫⁻ t in Ω₂K, Φf L A x t
    ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L from rfl, hc2]; exact hfin'⟩

  have hR := existsUnique_coset K L σ hgen
  have hΩ₂' := MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives (NumberField.Idele.idelicHaar L)
    (ΓL L) (ΓK K L) (ΓK_le_ΓL K L) Ω₂ hΩ₂ (Rrep K L σ hgen) hR
  have hΨsh : ∀ (a : N1 K L) t, Ψf L A X (st K L σ hgen a t) =
      ∫⁻ x in X, Φf L A (sx K L σ hgen a x) (st K L σ hgen a t) ∂adelicAddHaar (𝓞 L) L :=
    fun a t => (setLIntegral_X_smul L (eOf K L σ hgen a) hX (fun x => Φf L A x (st K L σ hgen a t))
      fun l q => Φf_add L hAu l q _).symm
  have hlint : ∀ t, ∫⁻ x in X, Gf K L σ hgen A (x, t) ∂adelicAddHaar (𝓞 L) L =
      ∑' a : N1 K L, ∫⁻ x in X, Φf L A (sx K L σ hgen a x) (st K L σ hgen a t) ∂adelicAddHaar (𝓞 L) L :=
    fun t => lintegral_tsum fun a => ((measurable_Φf_shift K L σ hgen hA a).of_uncurry_right
      (f := fun x t' => Φf L A (sx K L σ hgen a x) (st K L σ hgen a t'))).aemeasurable

  have hGx : Measurable fun x => ∫⁻ t in Ω₂, Gf K L σ hgen A (x, t) ∂NumberField.Idele.idelicHaar L :=
    Measurable.lintegral_prod_right' (ν := (NumberField.Idele.idelicHaar L).restrict Ω₂) (f := Gf K L σ hgen A) hGm
  have h1ae : ∀ᵐ x ∂(adelicAddHaar (𝓞 L) L).restrict X, ∫⁻ t in Ω₂, Gf K L σ hgen A (x, t) ∂NumberField.Idele.idelicHaar L < ⊤ :=
    ae_lt_top' hGx.aemeasurable hfin'
  have step1 : ∫ x in X, ∫ t in Ω₂, ∫ k, Li (word L x t k) * wc L t
        ∂maximalCompactHaar L ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L =
      ∫ x in X, ∫ t in Ω₂, SVf K L σ hgen U (x, t) ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L := by
    refine integral_congr_ae (h1ae.mono fun x hx => ?_)
    have h2 : ∀ᵐ t ∂(NumberField.Idele.idelicHaar L).restrict Ω₂, Gf K L σ hgen A (x, t) < ⊤ :=
      ae_lt_top' (Measurable.of_uncurry_left (f := fun x t => Gf K L σ hgen A (x, t)) hGm).aemeasurable hx.ne
    exact integral_congr_ae (h2.mono fun t ht => integral_Li_word K L σ hgen A Fi hA U Li hU hUA hFiA hLiU x t ht)

  have hSVm := measurable_SVf K L σ hgen hU
  have hSVG : ∀ q, ‖SVf K L σ hgen U q‖ₑ ≤ Gf K L σ hgen A q := fun q =>
    enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun a => hVΦ _ _)
  have hInt : Integrable (Function.uncurry fun x t => SVf K L σ hgen U (x, t))
      (((adelicAddHaar (𝓞 L) L).restrict X).prod ((NumberField.Idele.idelicHaar L).restrict Ω₂)) := by
    refine ⟨(hSVm.aestronglyMeasurable : AEStronglyMeasurable (SVf K L σ hgen U) _), ?_⟩
    show ∫⁻ q, ‖SVf K L σ hgen U q‖ₑ ∂(((adelicAddHaar (𝓞 L) L).restrict X).prod
      ((NumberField.Idele.idelicHaar L).restrict Ω₂)) < ⊤
    rw [lintegral_prod _ hSVm.enorm.aemeasurable]
    exact lt_of_le_of_lt (lintegral_mono fun x => lintegral_mono fun t => hSVG (x, t)) (lt_top_iff_ne_top.mpr hfin')
  have step2 : ∫ x in X, ∫ t in Ω₂, SVf K L σ hgen U (x, t) ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L =
      ∫ t in Ω₂, ∫ x in X, SVf K L σ hgen U (x, t) ∂adelicAddHaar (𝓞 L) L ∂NumberField.Idele.idelicHaar L :=
    integral_integral_swap hInt

  have hGt : Measurable fun t => ∫⁻ x in X, Gf K L σ hgen A (x, t) ∂adelicAddHaar (𝓞 L) L :=
    Measurable.lintegral_prod_left' (μ := (adelicAddHaar (𝓞 L) L).restrict X) (f := Gf K L σ hgen A) hGm
  have h3ae : ∀ᵐ t ∂(NumberField.Idele.idelicHaar L).restrict Ω₂, ∫⁻ x in X, Gf K L σ hgen A (x, t) ∂adelicAddHaar (𝓞 L) L < ⊤ :=
    ae_lt_top' hGt.aemeasurable (by rwa [← hswap])
  have hVtsh : ∀ (a : N1 K L) t, ∫ x in X, Vf L U (sx K L σ hgen a x) (st K L σ hgen a t) ∂adelicAddHaar (𝓞 L) L =
      Vtf L U X (st K L σ hgen a t) :=
    fun a t => setIntegral_X_smul L (eOf K L σ hgen a) hX (fun x => Vf L U x (st K L σ hgen a t)) fun l q => Vf_add L hUu l q _
  have step3 : ∫ t in Ω₂, ∫ x in X, SVf K L σ hgen U (x, t) ∂adelicAddHaar (𝓞 L) L ∂NumberField.Idele.idelicHaar L =
      ∫ t in Ω₂, ∑' a : N1 K L, Vtf L U X (st K L σ hgen a t) ∂NumberField.Idele.idelicHaar L := by
    refine integral_congr_ae (h3ae.mono fun t ht => ?_)
    show ∫ x in X, ∑' a : N1 K L, Vf L U (sx K L σ hgen a x) (st K L σ hgen a t) ∂adelicAddHaar (𝓞 L) L = _
    rw [integral_tsum (f := fun (a : N1 K L) (x : AdeleRing (𝓞 L) L) => Vf L U (sx K L σ hgen a x) (st K L σ hgen a t))
      (fun a => ((stronglyMeasurable_Vf_shift K L σ hgen hU a).measurable.of_uncurry_right
        (f := fun x t' => Vf L U (sx K L σ hgen a x) (st K L σ hgen a t'))).aestronglyMeasurable)]
    · exact tsum_congr fun a => hVtsh a t
    · refine ne_of_lt (lt_of_le_of_lt ?_ ht)
      rw [hlint]
      exact ENNReal.tsum_le_tsum fun a => lintegral_mono fun x => hVΦ _ _

  have hVtsm := stronglyMeasurable_Vtf L hU X
  have hbound : ∫⁻ t in Ω₂, ∑' a : N1 K L, ‖Vtf L U X (((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • t)‖ₑ
      ∂NumberField.Idele.idelicHaar L < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) (by rwa [← hswap, lt_top_iff_ne_top])
    rw [hlint]
    refine ENNReal.tsum_le_tsum fun a => (enorm_Vtf_le L hUA X _).trans (le_of_eq ?_)
    exact hΨsh a t
  have step4 : ∫ t in Ω₂, ∑' a : N1 K L, Vtf L U X (st K L σ hgen a t) ∂NumberField.Idele.idelicHaar L =
      ∫ t in ⋃ a : N1 K L, ((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • Ω₂, Vtf L U X t ∂NumberField.Idele.idelicHaar L :=
    (((MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
      (NumberField.Idele.idelicHaar L) (ΓL L) (ΓK K L) (ΓK_le_ΓL K L) Ω₂ hΩ₂ (Rrep K L σ hgen) hR).2
      (Vtf L U X) hVtsm.aestronglyMeasurable hbound).2.2).symm

  have step5 : ∫ t in ⋃ a : N1 K L, ((Rrep K L σ hgen a : ΓL L) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • Ω₂, Vtf L U X t ∂NumberField.Idele.idelicHaar L =
      ∫ t in Ω₂K, Vtf L U X t ∂NumberField.Idele.idelicHaar L := hΩ₂'.setIntegral_eq hΩ₂K fun u t => Vtf_smul K L σ hUu hUt hX u t

  have hInt' : Integrable (Function.uncurry fun t x => Vf L U x t)
      (((NumberField.Idele.idelicHaar L).restrict Ω₂K).prod ((adelicAddHaar (𝓞 L) L).restrict X)) := by
    refine ⟨(hVsm.measurable.comp measurable_swap).aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖Vf L U q.2 q.1‖ₑ ∂(((NumberField.Idele.idelicHaar L).restrict Ω₂K).prod ((adelicAddHaar (𝓞 L) L).restrict X)) < ⊤
    rw [lintegral_prod _ (show AEMeasurable (fun q : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L => ‖Vf L U q.2 q.1‖ₑ) _ from
      ((hVsm.measurable.comp measurable_swap).enorm).aemeasurable)]
    calc ∫⁻ t in Ω₂K, ∫⁻ x in X, ‖Vf L U x t‖ₑ ∂adelicAddHaar (𝓞 L) L ∂NumberField.Idele.idelicHaar L
        ≤ ∫⁻ t in Ω₂K, ∫⁻ x in X, Φf L A x t ∂adelicAddHaar (𝓞 L) L ∂NumberField.Idele.idelicHaar L :=
          lintegral_mono fun t => lintegral_mono fun x => hVΦ x t
      _ = ∫⁻ x in X, ∫⁻ t in Ω₂K, Φf L A x t ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L :=
          (lintegral_lintegral_swap (f := Φf L A) hΦm.aemeasurable).symm
      _ < ⊤ := by rw [hc2]; exact lt_top_iff_ne_top.mpr hfin'
  have step6 : ∫ t in Ω₂K, Vtf L U X t ∂NumberField.Idele.idelicHaar L =
      ∫ x in X, ∫ t in Ω₂K, Vf L U x t ∂NumberField.Idele.idelicHaar L ∂adelicAddHaar (𝓞 L) L := integral_integral_swap hInt'
  exact step1.trans (step2.trans (step3.trans (step4.trans (step5.trans step6))))

end Unfold

end R1IwTorus
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise.R1IwTorus"

end
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise.R1IwTorus"

def R1IwTorus.toTop (G : Type*) [Group G] : G →* (⊤ : Subgroup G) where
  toFun z := ⟨z, Subgroup.mem_top z⟩
  map_one' := rfl
  map_mul' _ _ := rfl

section Solution

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      ∫ x in X, ∫ t in Ω₂K, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) ∧
    (∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) := by
  set ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (R1IwTorus.toTop (AdeleRing (𝓞 L) L)ˣ) with hξ'
  have hξc' : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ) := hξc
  exact R1IwTorus.torus_unfold K L σ hgen (R1IwTorus.Afun K L D σ hgen νZL ξ' R φ) (R1IwTorus.Finf K L D σ hgen νZL ξ' R φ)
    (R1IwTorus.measurable_Afun K L D σ hgen νZL ξ' R φ hφc hφs hξc')
    (R1IwTorus.Ufun K L D σ hgen νZL ξ' R φ) (R1IwTorus.Linf K L D σ hgen νZL ξ' R φ)
    (R1IwTorus.measurable_Ufun K L D σ hgen νZL ξ' R φ hφc hφs hξc')
    (R1IwTorus.enorm_Ufun_le K L D σ hgen νZL ξ' R φ)
    (R1IwTorus.Finf_eq K L D σ hgen νZL ξ' R φ hφc hφs hξc')
    (R1IwTorus.Linf_eq K L D σ hgen νZL ξ' R φ hφc hφs hξc')
    (R1IwTorus.Afun_unipotent_mul K L D σ hgen νZL ξ' R φ) (R1IwTorus.Ufun_unipotent_mul K L D σ hgen νZL ξ' R φ)
    (fun e he g => R1IwTorus.Afun_torus_fixed K L D σ hgen νZL ξ' R φ he g)
    (fun e he g => R1IwTorus.Ufun_torus_fixed K L D σ hgen νZL ξ' R φ he g)
    X Ω₂ Ω₂K hX hΩ₂ hΩ₂K hfin

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise.R1IwTorus"

end S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise (solution)
