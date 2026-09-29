-- Prove2me | solution 1 for AutomorphicForm.exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/44be33b2-02ba-54ec-a85e-1f1d1cc069e0

import Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicHaar NumberField.InfinitePlace
open NumberField.AdelicVolume

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws31
namespace KFin

section Generic

variable {F : Type} [Field F] [NumberField F]

def Cc (h : AdelicGL2 (𝓞 F) F → ℂ) : Prop := Continuous h ∧ HasCompactSupport h

theorem Cc_add {h₁ h₂ : AdelicGL2 (𝓞 F) F → ℂ} (h1 : Cc h₁) (h2 : Cc h₂) : Cc (h₁ + h₂) :=
  ⟨h1.1.add h2.1, h1.2.add h2.2⟩

theorem Cc_smul (c : ℂ) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : Cc h) : Cc (c • h) :=
  ⟨hh.1.const_smul c, hh.2.smul_left⟩

theorem Cc_zero : Cc (0 : AdelicGL2 (𝓞 F) F → ℂ) := ⟨continuous_const, HasCompactSupport.zero⟩

def lt (g : AdelicGL2 (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun y => h (g⁻¹ * y)

theorem Cc_lt (g : AdelicGL2 (𝓞 F) F) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : Cc h) : Cc (lt g h) := by
  have e : lt g h = h ∘ (Homeomorph.mulLeft g⁻¹) := rfl
  rw [e]
  exact ⟨hh.1.comp (Homeomorph.mulLeft g⁻¹).continuous, hh.2.comp_homeomorph _⟩

theorem lt_mul (a b : AdelicGL2 (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F → ℂ) : lt (a * b) h = lt a (lt b h) := by
  funext y
  simp only [lt, mul_inv_rev, mul_assoc]

def invP (h : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun y => h y⁻¹

theorem Cc_invP {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : Cc h) : Cc (invP h) := by
  have e : invP h = h ∘ (Homeomorph.inv (AdelicGL2 (𝓞 F) F)) := rfl
  rw [e]
  exact ⟨hh.1.comp (Homeomorph.inv _).continuous, hh.2.comp_homeomorph _⟩

theorem lt_eq_invP_rightTranslate (g : AdelicGL2 (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F → ℂ) :
    lt g h = invP (CuspidalConstituent.rightTranslate F g (invP h)) := by
  funext y
  simp only [lt, invP, CuspidalConstituent.rightTranslate_apply, mul_inv_rev, inv_inv]

def invPₗ : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun := invP
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ltₗ (g : AdelicGL2 (𝓞 F) F) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun := lt g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invPₗ_apply (h : AdelicGL2 (𝓞 F) F → ℂ) : invPₗ h = invP h := rfl

theorem ltₗ_apply (g : AdelicGL2 (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F → ℂ) : ltₗ g h = lt g h := rfl

theorem rightConv_mul_right [SecondCountableTopology (AdelicGL2 (𝓞 F) F)]
    (φ h : AdelicGL2 (𝓞 F) F → ℂ) (x g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ h (x * g) = rightConv F φ (lt g h) x := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  rw [rightConv_apply, rightConv_apply,
    ← integral_mul_left_eq_self (fun y => φ (x * y) * lt g h y) g]
  simp only [lt, inv_mul_cancel_left, mul_assoc]

theorem rightConv_add (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    {h₁ h₂ : AdelicGL2 (𝓞 F) F → ℂ} (h1 : Cc h₁) (h2 : Cc h₂) :
    rightConv F φ (h₁ + h₂) = rightConv F φ h₁ + rightConv F φ h₂ := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  simp only [rightConv_apply, Pi.add_apply, mul_add]
  have hi : ∀ {h : AdelicGL2 (𝓞 F) F → ℂ}, Cc h →
      Integrable (fun y => φ (x * y) * h y) (adelicGLHaar (Fin 2) (𝓞 F) F) := fun hh =>
    ((hφc.comp (continuous_const.mul continuous_id)).mul hh.1).integrable_of_hasCompactSupport hh.2.mul_left
  exact integral_add (hi h1) (hi h2)

theorem rightConv_smul (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) (h : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F φ (c • h) = c • rightConv F φ h := by
  funext x
  simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem rightConv_sum_smul (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (b : ι → AdelicGL2 (𝓞 F) F → ℂ) (hb : ∀ i, Cc (b i)) :
    rightConv F φ (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i • rightConv F φ (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rightConv_zero_right F φ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, rightConv_add φ hφc (Cc_smul _ (hb a)) ?_,
      rightConv_smul, ih]
    exact Finset.sum_induction _ (fun h => Cc h) (fun _ _ ha hb => Cc_add ha hb) Cc_zero (fun i _ => Cc_smul _ (hb i))

theorem exists_finset_span (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ W] (hW : ∀ h ∈ W, Cc h) :
    ∃ s : Finset (AdelicGL2 (𝓞 F) F → ℂ), ∀ h ∈ W,
      rightConv F φ h ∈ Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ)) := by
  classical
  let b := Module.finBasis ℂ W
  refine ⟨Finset.univ.image fun i => rightConv F φ ((b i : W) : AdelicGL2 (𝓞 F) F → ℂ), fun h hh => ?_⟩
  have hrep : h = ∑ i, (b.repr ⟨h, hh⟩ i) • ((b i : W) : AdelicGL2 (𝓞 F) F → ℂ) := by
    have := b.sum_repr ⟨h, hh⟩
    have := congrArg (fun v : W => (v : AdelicGL2 (𝓞 F) F → ℂ)) this
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
  rw [hrep, rightConv_sum_smul φ hφc _ _ _ (fun i => hW _ (b i).2)]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

end Generic

section Places

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem det_eq_one_or_neg_one_of_isReal {w : InfinitePlace F} (hw : w.IsReal)
    {k : GL (Fin 2) w.Completion} (hk : IsRowIsometry k) :
    (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 ∨ (k : Matrix (Fin 2) (Fin 2) w.Completion).det = -1 := by
  set e := Completion.extensionEmbeddingOfIsReal hw
  have hn : |e (k : Matrix (Fin 2) (Fin 2) w.Completion).det| = 1 := by
    rw [← Real.norm_eq_abs, (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero e)]
    exact hk.1
  rcases (abs_eq (zero_le_one' ℝ)).mp hn with h | h
  · left
    exact e.injective (by rw [h, map_one])
  · right
    exact e.injective (by rw [h, map_neg, map_one])

def diagGL {L : Type*} [Field L] (a d : L) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) L where
  val := !![a, 0; 0, d]
  inv := !![a⁻¹, 0; 0, d⁻¹]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]

theorem isRowIsometry_diagGL {L : Type*} [NormedField L] (a d : L) (ha : ‖a‖ = 1) (hd : ‖d‖ = 1) :
    IsRowIsometry (diagGL a d (norm_ne_zero_iff.mp (by rw [ha]; exact one_ne_zero))
      (norm_ne_zero_iff.mp (by rw [hd]; exact one_ne_zero))) := by
  constructor
  · show ‖(!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) L).det‖ = 1
    rw [Matrix.det_fin_two_of]; simp [ha, hd]
  · intro x y
    show ‖x * (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) L) 0 0 + y * (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2
        + ‖x * (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) L) 0 1 + y * (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, add_zero, zero_add, norm_mul, ha, hd, mul_one]

theorem det_diagGL {L : Type*} [Field L] (a d : L) (ha : a ≠ 0) (hd : d ≠ 0) :
    ((diagGL a d ha hd : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = a * d := by
  show (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) L).det = a * d
  rw [Matrix.det_fin_two_of]; ring

theorem centralScalar_val (u : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(u : AdeleRing (𝓞 F) F), 0; 0, (u : AdeleRing (𝓞 F) F)] := by
  change Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F) = _
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem adelicArchGLInclAt_entry (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) := rfl

theorem adelicArchGLInclAt_diagGL_eq_centralScalar (w : InfinitePlace F) (c : (w.Completion)ˣ) :
    adelicArchGLInclAt F w (diagGL (c : w.Completion) (c : w.Completion) c.ne_zero c.ne_zero)
      = centralScalar (𝓞 F) F (NumberField.TateGlobal.archUnitHom w c) := by
  classical
  apply Units.ext
  rw [centralScalar_val]
  ext i j
  rw [adelicArchGLInclAt_entry]
  have hu : ((NumberField.TateGlobal.archUnitHom w c : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((archCentralUnit F w c : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := rfl
  have hval : ((diagGL (c : w.Completion) (c : w.Completion) c.ne_zero c.ne_zero : GL (Fin 2) w.Completion)
      : Matrix (Fin 2) (Fin 2) w.Completion) = !![(c : w.Completion), 0; 0, (c : w.Completion)] := rfl
  rw [hval]
  fin_cases i <;> fin_cases j
  · show (_, _) = ((NumberField.TateGlobal.archUnitHom w c : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    rw [hu]
    refine Prod.ext (funext fun v => ?_) ?_
    · dsimp only
      by_cases hv : v = w
      · subst hv; rw [archMatrixUpdate_apply_self, archCentralUnit_fst_self]; rfl
      · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv, archCentralUnit_fst_of_ne w c hv]; rfl
    · dsimp only; rw [archCentralUnit_snd]; rfl
  · show (_, _) = (0 : AdeleRing (𝓞 F) F)
    refine Prod.ext (funext fun v => ?_) ?_
    · dsimp only
      by_cases hv : v = w
      · subst hv; rw [archMatrixUpdate_apply_self]; rfl
      · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]; rfl
    · dsimp only; rfl
  · show (_, _) = (0 : AdeleRing (𝓞 F) F)
    refine Prod.ext (funext fun v => ?_) ?_
    · dsimp only
      by_cases hv : v = w
      · subst hv; rw [archMatrixUpdate_apply_self]; rfl
      · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]; rfl
    · dsimp only; rfl
  · show (_, _) = ((NumberField.TateGlobal.archUnitHom w c : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    rw [hu]
    refine Prod.ext (funext fun v => ?_) ?_
    · dsimp only
      by_cases hv : v = w
      · subst hv; rw [archMatrixUpdate_apply_self, archCentralUnit_fst_self]; rfl
      · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv, archCentralUnit_fst_of_ne w c hv]; rfl
    · dsimp only; rw [archCentralUnit_snd]; rfl

theorem centralScalar_commute (u : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F u * g = g * centralScalar (𝓞 F) F u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rightConv_mul_centralScalar (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (h : AdelicGL2 (𝓞 F) F → ℂ)
    (u : (AdeleRing (𝓞 F) F)ˣ) (x : AdelicGL2 (𝓞 F) F) :
    rightConv F φ h (x * centralScalar (𝓞 F) F u)
      = (((χ₁ u : ℂˣ) : ℂ) * ((χ₂ u : ℂˣ) : ℂ)) * rightConv F φ h x := by
  rw [rightConv_apply, rightConv_apply, ← integral_const_mul]
  congr 1
  funext y
  have e : x * centralScalar (𝓞 F) F u * y = centralScalar (𝓞 F) F u * (x * y) := by
    rw [← centralScalar_commute, mul_assoc]
  rw [e, hφ _ (centralScalar_mem_adelicBorel (𝓞 F) F u) (x * y), borelDiagFst_centralScalar,
    borelDiagSnd_centralScalar]
  ring

end Places

end Ws31.KFin

end

open Ws31.KFin in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (tys : ArchTypeFamily F) (_hfty : (fun x => f x⁻¹) ∈ archCutSubmodule F tys)
    (w : InfinitePlace F) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ), FiniteDimensional ℂ W ∧
      ∀ (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), (∀ x, χ₁ x * χ₂ x = η x) →
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ), IsInducedSection (𝓞 F) F χ₁ χ₂ φ → Continuous φ →
      ∀ g : AdelicGL2 (𝓞 F) F,
        (fun k : ↥(archRowIsometrySubgroup F w) => rightConv F φ f (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

  have hmem : invP f ∈ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) :=
    (mem_archCutSubmodule_iff F tys _).mp _hfty w
  obtain ⟨hSfd, hSstab, -⟩ :=
    CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt F w
      (tys.card w) (tys.rep w) (invP f) hmem
  set S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
    CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w k) (invP f)) with hS
  haveI : FiniteDimensional ℂ S := hSfd
  have hfCc : Cc f := ⟨_hf, _hfc⟩
  have hSCc : ∀ h ∈ S, Cc h := by
    intro h hh
    refine Submodule.span_induction (p := fun h _ => Cc h) ?_ Cc_zero (fun _ _ _ _ ha hb => Cc_add ha hb) (fun c _ _ hx => Cc_smul c hx) hh
    rintro _ ⟨k, rfl⟩
    show Cc (CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w k) (invP f))
    have e : CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w k) (invP f)
        = invP f ∘ Homeomorph.mulRight (rowIsometryInclAt₀ F w k) := rfl
    rw [e]
    exact ⟨(Cc_invP hfCc).1.comp (Homeomorph.mulRight _).continuous, (Cc_invP hfCc).2.comp_homeomorph _⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : GL (Fin 2) w.Completion,
      ε = diagGL (-1 : w.Completion) 1 (neg_ne_zero.mpr one_ne_zero) one_ne_zero := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      W = S.map invPₗ ⊔ (S.map invPₗ).map (ltₗ (adelicArchGLInclAt F w ε)) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ W := by rw [hWdef]; infer_instance
  have hWCc : ∀ h ∈ W, Cc h := by
    intro h hh
    rw [hWdef] at hh
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hh
    obtain ⟨a', ha', rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨b'', hb'', rfl⟩ := Submodule.mem_map.mp hb
    obtain ⟨b', hb', rfl⟩ := Submodule.mem_map.mp hb''
    rw [invPₗ_apply, invPₗ_apply, ltₗ_apply]
    exact Cc_add (Cc_invP (hSCc a' ha')) (Cc_lt _ (Cc_invP (hSCc b' hb')))
  have hW1 : ∀ h, h ∈ S.map invPₗ → h ∈ W := fun h hh => by rw [hWdef]; exact Submodule.mem_sup_left hh
  have hW2 : ∀ h, h ∈ S.map invPₗ → lt (adelicArchGLInclAt F w ε) h ∈ W := fun h hh => by
    rw [hWdef]; exact Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨h, hh, rfl⟩)
  have hS' : ∀ k₁ : rowIsometrySubgroup₀ w.Completion,
      lt (adelicArchGLInclAt F w (k₁ : GL (Fin 2) w.Completion)) f ∈ S.map invPₗ := by
    intro k₁
    rw [lt_eq_invP_rightTranslate]
    exact Submodule.mem_map.mpr ⟨_, Submodule.subset_span ⟨k₁, rfl⟩, rfl⟩

  have hEv : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ), Continuous φ → ∀ g : AdelicGL2 (𝓞 F) F,
      ∃ Ev : W →ₗ[ℂ] ℂ, ∀ h : W, Ev h = rightConv F φ (h : AdelicGL2 (𝓞 F) F → ℂ) g := by
    intro φ hφc g
    refine ⟨{ toFun := fun h => rightConv F φ (h : AdelicGL2 (𝓞 F) F → ℂ) g
              map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, fun h => rfl⟩
    · show rightConv F φ ((a : AdelicGL2 (𝓞 F) F → ℂ) + b) g = _
      rw [rightConv_add φ hφc (hWCc _ a.2) (hWCc _ b.2)]; rfl
    · show rightConv F φ (c • (a : AdelicGL2 (𝓞 F) F → ℂ)) g = c • rightConv F φ a g
      rw [rightConv_smul]; rfl

  by_cases hw : w.IsReal
  ·
    have hltW : ∀ k : ↥(archRowIsometrySubgroup F w), lt (k : AdelicGL2 (𝓞 F) F) f ∈ W := by
      intro k
      obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp k.2
      have hk'iso : IsRowIsometry k' := mem_rowIsometrySubgroup_iff.mp hk'
      rw [← hkk]
      rcases det_eq_one_or_neg_one_of_isReal hw hk'iso with h1 | hm1
      · exact hW1 _ (hS' ⟨k', (mem_rowIsometrySubgroup₀_iff _).mpr ⟨h1, hk'iso⟩⟩)
      · have hεiso : IsRowIsometry ε := by
          rw [hεdef]; exact isRowIsometry_diagGL (-1 : w.Completion) 1 (by simp) norm_one
        have hεdet : ((ε : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = -1 := by
          rw [hεdef, det_diagGL]; ring
        have hk₁ : ε * k' ∈ rowIsometrySubgroup₀ w.Completion := by
          refine (mem_rowIsometrySubgroup₀_iff _).mpr ⟨?_, hεiso.mul hk'iso⟩
          rw [Units.val_mul, Matrix.det_mul, hεdet, hm1]; ring
        have hεε : ε * ε = 1 := by
          rw [hεdef]
          apply Units.ext
          show (!![(-1 : w.Completion), 0; 0, 1] : Matrix (Fin 2) (Fin 2) w.Completion) * !![(-1 : w.Completion), 0; 0, 1] = 1
          ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        obtain ⟨k₁, hk₁def⟩ : ∃ k₁ : GL (Fin 2) w.Completion, k₁ = ε * k' := ⟨_, rfl⟩
        have hk₁' : k₁ ∈ rowIsometrySubgroup₀ w.Completion := by rw [hk₁def]; exact hk₁
        have hk'eq : k' = ε * k₁ := by rw [hk₁def, ← mul_assoc, hεε, one_mul]
        rw [hk'eq, map_mul, lt_mul]
        exact hW2 _ (hS' ⟨k₁, hk₁'⟩)
    let Λ : (W →ₗ[ℂ] ℂ) →ₗ[ℂ] (↥(archRowIsometrySubgroup F w) → ℂ) :=
      { toFun := fun l k => l ⟨lt (k : AdelicGL2 (𝓞 F) F) f, hltW k⟩
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl }
    refine ⟨LinearMap.range Λ, inferInstance, ?_⟩
    intro χ₁ χ₂ hχ φ hφ hφc g
    obtain ⟨Ev, hEv'⟩ := hEv φ hφc g
    refine ⟨Ev, funext fun k => ?_⟩
    show Ev ⟨lt (k : AdelicGL2 (𝓞 F) F) f, hltW k⟩ = rightConv F φ f (g * k)
    rw [hEv', rightConv_mul_right φ f g]
  ·
    have hwc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have hdec : ∀ k : ↥(archRowIsometrySubgroup F w), ∃ (c : (w.Completion)ˣ) (k₁ : GL (Fin 2) w.Completion),
        k₁ ∈ rowIsometrySubgroup₀ w.Completion ∧ ∀ x : AdelicGL2 (𝓞 F) F,
          x * (k : AdelicGL2 (𝓞 F) F) = x * adelicArchGLInclAt F w k₁ *
            centralScalar (𝓞 F) F (NumberField.TateGlobal.archUnitHom w c) := by
      intro k
      obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp k.2
      have hk'iso : IsRowIsometry k' := mem_rowIsometrySubgroup_iff.mp hk'
      set e := Completion.ringEquivComplexOfIsComplex hwc with he
      have hen : ∀ x : w.Completion, ‖e x‖ = ‖x‖ := fun x =>
        (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
      set d : ℂ := e (k' : Matrix (Fin 2) (Fin 2) w.Completion).det with hd
      set c' : ℂ := d ^ (((2 : ℕ) : ℂ)⁻¹) with hc'
      have hc'2 : c' ^ 2 = d := by rw [hc']; exact Complex.cpow_nat_inv_pow _ two_ne_zero
      have hdn : ‖d‖ = 1 := by rw [hd, hen]; exact hk'iso.1
      have hc'n : ‖c'‖ = 1 := by
        have : ‖c'‖ ^ 2 = 1 := by rw [← norm_pow, hc'2, hdn]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
      have hc'0 : c' ≠ 0 := norm_ne_zero_iff.mp (by rw [hc'n]; exact one_ne_zero)
      set cK : w.Completion := e.symm c' with hcK
      have hcKn : ‖cK‖ = 1 := by rw [← hen, hcK, RingEquiv.apply_symm_apply]; exact hc'n
      have hcK0 : cK ≠ 0 := norm_ne_zero_iff.mp (by rw [hcKn]; exact one_ne_zero)
      have hcK2 : cK * cK = (k' : Matrix (Fin 2) (Fin 2) w.Completion).det := by
        apply e.injective
        rw [map_mul, hcK, RingEquiv.apply_symm_apply, ← sq, hc'2, hd]
      let c : (w.Completion)ˣ := Units.mk0 cK hcK0
      let z : GL (Fin 2) w.Completion := diagGL (c : w.Completion) (c : w.Completion) c.ne_zero c.ne_zero
      have hziso : IsRowIsometry z := isRowIsometry_diagGL (c : w.Completion) (c : w.Completion) hcKn hcKn
      have hzdet : ((z : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det
          = (k' : Matrix (Fin 2) (Fin 2) w.Completion).det := by
        show ((diagGL (c : w.Completion) (c : w.Completion) _ _ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = _
        rw [det_diagGL]; exact hcK2
      have hdet0 : (k' : Matrix (Fin 2) (Fin 2) w.Completion).det ≠ 0 := by rw [← hcK2]; exact mul_ne_zero hcK0 hcK0
      have hk₁ : z⁻¹ * k' ∈ rowIsometrySubgroup₀ w.Completion := by
        refine (mem_rowIsometrySubgroup₀_iff _).mpr ⟨?_, hziso.inv.mul hk'iso⟩
        rw [Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hzdet,
          inv_mul_cancel₀ hdet0]
      obtain ⟨k₁, hk₁def⟩ : ∃ k₁ : GL (Fin 2) w.Completion, k₁ = z⁻¹ * k' := ⟨_, rfl⟩
      have hk₁' : k₁ ∈ rowIsometrySubgroup₀ w.Completion := by rw [hk₁def]; exact hk₁
      have hk'eq : k' = z * k₁ := by rw [hk₁def, mul_inv_cancel_left]
      have hzc : adelicArchGLInclAt F w z = centralScalar (𝓞 F) F (NumberField.TateGlobal.archUnitHom w c) :=
        adelicArchGLInclAt_diagGL_eq_centralScalar w c
      refine ⟨c, k₁, hk₁', fun x => ?_⟩
      rw [← hkk, hk'eq, map_mul, hzc, centralScalar_commute, mul_assoc]
    choose u k₁ hk₁ hdec' using hdec
    let Λ : (W →ₗ[ℂ] ℂ) →ₗ[ℂ] (↥(archRowIsometrySubgroup F w) → ℂ) :=
      { toFun := fun l k => ((η (NumberField.TateGlobal.archUnitHom w (u k)) : ℂˣ) : ℂ) *
            l ⟨lt (adelicArchGLInclAt F w (k₁ k)) f, hW1 _ (hS' ⟨k₁ k, hk₁ k⟩)⟩
        map_add' := fun a b => by funext k; simp only [LinearMap.add_apply, Pi.add_apply, mul_add]
        map_smul' := fun r a => by funext k; simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    refine ⟨LinearMap.range Λ, inferInstance, ?_⟩
    intro χ₁ χ₂ hχ φ hφ hφc g
    obtain ⟨Ev, hEv'⟩ := hEv φ hφc g
    refine ⟨Ev, funext fun k => ?_⟩
    show ((η (NumberField.TateGlobal.archUnitHom w (u k)) : ℂˣ) : ℂ) *
        Ev ⟨lt (adelicArchGLInclAt F w (k₁ k)) f, hW1 _ (hS' ⟨k₁ k, hk₁ k⟩)⟩ = rightConv F φ f (g * k)
    rw [hEv', hdec' k g, rightConv_mul_centralScalar χ₁ χ₂ φ hφ f, rightConv_mul_right φ f g, ← hχ, Units.val_mul]

end S_AutomorphicForm_exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule (solution)
