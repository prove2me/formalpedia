-- Prove2me | solution 1 for AutomorphicForm.exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/08772615-3463-5d32-bf5f-f3729b351947

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_RestrictedProduct_measurable_iff_forall_measurable_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain Filter
open scoped ENNReal RestrictedProduct

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "unipotentGL2 unipotentGL2_coe unipotentGL2_add"
namespace BruhatUnipotent
p2m_open "AutomorphicForm"

section UnitsMeasurable

variable {M : Type*} [Monoid M] [TopologicalSpace M]

theorem isInducing_val_prod_inv :
    Topology.IsInducing (fun u : Mˣ => ((u : M), ((u⁻¹ : Mˣ) : M))) := by
  have h1 : Topology.IsInducing (Units.embedProduct M) := Units.isEmbedding_embedProduct.isInducing
  have h2 : Topology.IsInducing
      (fun q : M × Mᵐᵒᵖ => (q.1, MulOpposite.unop q.2)) :=
    (Homeomorph.prodCongr (Homeomorph.refl M) MulOpposite.opHomeomorph.symm).isInducing
  exact h2.comp h1

theorem measurable_units_of_val_of_inv [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] {mU : MeasurableSpace Mˣ} [BorelSpace Mˣ]
    {Z : Type*} [MeasurableSpace Z] {f : Z → Mˣ}
    (h1 : Measurable fun z => ((f z : Mˣ) : M)) (h2 : Measurable fun z => (((f z)⁻¹ : Mˣ) : M)) :
    Measurable f := by
  set e : Mˣ → M × M := fun u => ((u : M), ((u⁻¹ : Mˣ) : M)) with he
  have hind := isInducing_val_prod_inv (M := M)
  have hU : mU = MeasurableSpace.comap e (borel (M × M)) := by
    rw [BorelSpace.measurable_eq (α := Mˣ)]
    have : (borel Mˣ) = @borel Mˣ (TopologicalSpace.induced e inferInstance) := by
      congr 1
      exact hind.eq_induced
    rw [this]
    exact borel_comap
  have hprod : borel (M × M) = (Prod.instMeasurableSpace : MeasurableSpace (M × M)) :=
    (BorelSpace.measurable_eq (α := M × M)).symm
  have hef : Measurable (e ∘ f) := by
    show Measurable fun z => (((f z : Mˣ) : M), (((f z)⁻¹ : Mˣ) : M))
    exact h1.prodMk h2
  rw [measurable_iff_comap_le, hU, MeasurableSpace.comap_comp, hprod]
  exact hef.comap_le

end UnitsMeasurable

section Pivot

variable {F : Type*} [NormedField F]

private def _root_.AutomorphicForm.BruhatUnipotent.piv (a b : F) : F × F := if ‖b‖ ≤ ‖a‖ then (a⁻¹, 0) else (0, b⁻¹)

p2m_export "AutomorphicForm.BruhatUnipotent" "piv"
theorem piv_dot {a b : F} (h : ¬ (a = 0 ∧ b = 0)) : (piv a b).1 * a + (piv a b).2 * b = 1 := by
  unfold piv
  split_ifs with hle
  · have ha : a ≠ 0 := by
      intro ha
      apply h
      refine ⟨ha, ?_⟩
      have : ‖b‖ ≤ 0 := by simpa [ha] using hle
      exact norm_le_zero_iff.mp this
    simp [ha]
  · have hb : b ≠ 0 := by
      intro hb; apply hle; simp [hb]
    simp [hb]

theorem norm_piv_fst_le (a b : F) : ‖(piv a b).1‖ ≤ ‖a‖⁻¹ := by
  unfold piv; split_ifs <;> simp

theorem norm_piv_snd_le (a b : F) : ‖(piv a b).2‖ ≤ ‖b‖⁻¹ := by
  unfold piv; split_ifs <;> simp

theorem norm_piv_le_one {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : ¬ (‖a‖ < 1 ∧ ‖b‖ < 1)) :
    ‖(piv a b).1‖ ≤ 1 ∧ ‖(piv a b).2‖ ≤ 1 := by
  unfold piv
  split_ifs with hle
  · have ha1 : ‖a‖ = 1 := by
      rcases eq_or_lt_of_le ha with h1 | h1
      · exact h1
      · exact absurd ⟨h1, lt_of_le_of_lt hle h1⟩ h
    refine ⟨?_, by simp⟩
    simp [ha1]
  · have hb1 : ‖b‖ = 1 := by
      rcases eq_or_lt_of_le hb with h1 | h1
      · exact h1
      · exact absurd ⟨(lt_of_not_ge hle).trans h1, h1⟩ h
    refine ⟨by simp, ?_⟩
    simp [hb1]

private theorem _root_.Measurable.piv [MeasurableSpace F] [BorelSpace F] {Z : Type*} [MeasurableSpace Z]
    {f g : Z → F} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun z => AutomorphicForm.BruhatUnipotent.piv (f z) (g z) := by
  unfold AutomorphicForm.BruhatUnipotent.piv
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hg.norm hf.norm
  · exact hf.inv.prodMk measurable_const
  · exact measurable_const.prodMk hg.inv

p2m_alias "P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.Measurable.piv" "Measurable.piv"
end Pivot

section Adele

variable (K : Type) [Field K] [NumberField K]

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 K)) := by
  classical
  haveI : Countable K := by
    let b := Module.finBasis ℚ K
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (𝓞 K) := (RingOfIntegers.coe_injective (K := K)).countable
  have hsurj : Function.Surjective (fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  haveI : Countable (Ideal (𝓞 K)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

scoped instance secondCountableTopology_completion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) :=
  secondCountable_of_proper

scoped instance secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

theorem measurable_adele_of_components {Z : Type*} [MeasurableSpace Z] {f : Z → AdeleRing (𝓞 K) K}
    (h1 : ∀ w : InfinitePlace K, Measurable[_, borel _] fun z => (f z).1 w)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), Measurable[_, borel _] fun z => (f z).2 v) :
    Measurable f := by
  letI mA : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  letI mF : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  letI mw : ∀ w : InfinitePlace K, MeasurableSpace w.Completion := fun w => borel _
  haveI : ∀ w : InfinitePlace K, BorelSpace w.Completion := fun w => ⟨rfl⟩
  letI mv : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K) := fun v => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K) := fun v => ⟨rfl⟩
  haveI : Countable (HeightOneSpectrum (𝓞 K)) := countable_heightOneSpectrum K

  have hA : Measurable fun z => (f z).1 := by
    have : mA = MeasurableSpace.pi := (BorelSpace.measurable_eq (α := (w : InfinitePlace K) → w.Completion)).symm
    rw [this]
    exact measurable_pi_iff.mpr h1

  have hBF : @BorelSpace (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K,
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))]) _ mF := @BorelSpace.mk _ _ mF rfl
  have hF : Measurable[_, mF] fun z => (f z).2 :=
    (@RestrictedProduct.measurable_iff_forall_measurable_apply (HeightOneSpectrum (𝓞 K)) _
      (fun v => v.adicCompletion K) _ _ mv _
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (fun v => (Valued.isOpen_valuationSubring _).measurableSet) mF hBF Z _ (fun z => (f z).2)).mpr h2

  have hBP : @BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) _
      (@Prod.instMeasurableSpace _ _ mA mF) := Prod.borelSpace
  have hprod : (‹MeasurableSpace (AdeleRing (𝓞 K) K)›) = @Prod.instMeasurableSpace _ _ mA mF := by
    rw [BorelSpace.measurable_eq (α := AdeleRing (𝓞 K) K)]
    exact hBP.measurable_eq.symm
  have : @Measurable Z (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) _ (@Prod.instMeasurableSpace _ _ mA mF)
      (fun z => (((f z).1, (f z).2) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)) :=
    hA.prodMk hF
  rw [measurable_iff_comap_le, hprod]
  exact this.comap_le

theorem measurable_fst_apply (w : InfinitePlace K) :
    Measurable[_, borel _] fun x : AdeleRing (𝓞 K) K => x.1 w := by
  letI : MeasurableSpace w.Completion := borel _
  haveI : BorelSpace w.Completion := ⟨rfl⟩
  have hc : Continuous fun x : AdeleRing (𝓞 K) K => x.1 w := (continuous_apply w).comp continuous_fst
  exact hc.measurable

theorem measurable_snd_apply (v : HeightOneSpectrum (𝓞 K)) :
    Measurable[_, borel _] fun x : AdeleRing (𝓞 K) K => x.2 v := by
  letI : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  have hc : Continuous fun x : AdeleRing (𝓞 K) K => x.2 v :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact hc.measurable

end Adele

section GLtwo

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)
local notation "Xp" => (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ

def proj (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ :=
  (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0, Matrix.GeneralLinearGroup.det g)

def act (h : GL (Fin 2) (AdeleRing (𝓞 K) K)) (p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ) :
    (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ :=
  ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).mulVec p.1, Matrix.GeneralLinearGroup.det h * p.2)

variable {K}

theorem proj_mul (h g : Gp) : proj K (h * g) = act K h (proj K g) := by
  refine Prod.ext ?_ ?_
  · funext i
    simp only [proj, act, Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp only [proj, act, map_mul]

theorem act_mul (h h' : Gp) (p : Xp) : act K (h * h') p = act K h (act K h' p) := by
  refine Prod.ext ?_ ?_
  · simp only [act, Units.val_mul, Matrix.mulVec_mulVec]
  · simp only [act, map_mul, mul_assoc]

theorem act_one (p : Xp) : act K 1 p = p := by
  refine Prod.ext ?_ ?_
  · simp only [act, Units.val_one, Matrix.one_mulVec]
  · simp only [act, map_one, one_mul]

theorem act_inv_act (h : Gp) (p : Xp) : act K h⁻¹ (act K h p) = p := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem eq_mul_unipotentGL2_of_proj_eq {g g' : Gp} (hgg : proj K g = proj K g') :
    g' = g * unipotentGL2 (((g⁻¹ * g' : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1) := by
  set m : Gp := g⁻¹ * g' with hm
  have hpm : proj K m = proj K 1 := by
    rw [hm, proj_mul, ← hgg, ← proj_mul, inv_mul_cancel]
  have h00 : (m : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 = 1 := by
    have := congr_fun (congr_arg Prod.fst hpm) 0
    simpa [proj] using this
  have h10 : (m : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := by
    have := congr_fun (congr_arg Prod.fst hpm) 1
    simpa [proj] using this
  have hdet : Matrix.GeneralLinearGroup.det m = 1 := by
    have := congr_arg Prod.snd hpm
    simpa [proj] using this
  have h11 : (m : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 = 1 := by
    have h := congr_arg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h10] at h
    simpa using h
  have hmu : m = unipotentGL2 ((m : Matrix (Fin 2) (Fin 2) 𝔸) 0 1) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe, h00, h10, h11]
  calc g' = g * m := by rw [hm, mul_inv_cancel_left]
    _ = g * unipotentGL2 ((m : Matrix (Fin 2) (Fin 2) 𝔸) 0 1) := by rw [← hmu]

theorem proj_mul_unipotentGL2 (g : Gp) (x : 𝔸) : proj K (g * unipotentGL2 x) = proj K g := by
  rw [proj_mul]
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i <;> simp [proj, act, unipotentGL2_coe]
  · have : Matrix.GeneralLinearGroup.det (unipotentGL2 x : Gp) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
      simp
    simp [proj, act, this]

def IsUnimod (c : Fin 2 → AdeleRing (𝓞 K) K) : Prop :=
  (∀ w : InfinitePlace K, ¬ ((c 0).1 w = 0 ∧ (c 1).1 w = 0)) ∧
  (∀ v : HeightOneSpectrum (𝓞 K), ¬ ((c 0).2 v = 0 ∧ (c 1).2 v = 0)) ∧
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1)

theorem mem_integers_iff (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem fst_apply_ne_zero_of_units (u : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) : (u : 𝔸).1 w ≠ 0 := by
  intro h
  have h1 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).1 w = 1 := by rw [Units.mul_inv]; rfl
  have h2 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).1 w = (u : 𝔸).1 w * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).1 w :=
    rfl
  rw [h2, h, zero_mul] at h1
  exact zero_ne_one h1

theorem snd_apply_ne_zero_of_units (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : 𝔸).2 v ≠ 0 := by
  intro h
  have h1 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = 1 := by rw [Units.mul_inv]; rfl
  have h2 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = (u : 𝔸).2 v * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v :=
    rfl
  rw [h2, h, zero_mul] at h1
  exact zero_ne_one h1

theorem norm_snd_units_mul_inv (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(u : 𝔸).2 v‖ * ‖((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ = 1 := by
  have h1 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = 1 := by rw [Units.mul_inv]; rfl
  have h2 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = (u : 𝔸).2 v * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v :=
    rfl
  rw [← norm_mul, ← h2, h1, norm_one]

theorem isUnimod_of_proj (g : Gp) : IsUnimod (proj K g).1 := by
  have hcol0 : (proj K g).1 0 = (g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 := rfl
  have hcol1 : (proj K g).1 1 = (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 := rfl
  set d : (AdeleRing (𝓞 K) K)ˣ := Matrix.GeneralLinearGroup.det g with hd
  have hdv : (d : 𝔸) = (g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 * (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 * (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
  · apply fst_apply_ne_zero_of_units d w
    rw [hcol0] at h; rw [hcol1] at h
    show (d : 𝔸).1 w = 0
    rw [hdv]
    show ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).1 w * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w -
      ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).1 w * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).1 w = 0
    rw [h.1, h.2]; ring
  · apply snd_apply_ne_zero_of_units d v
    rw [hcol0] at h; rw [hcol1] at h
    show (d : 𝔸).2 v = 0
    rw [hdv]
    show ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2 v -
      ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v = 0
    rw [h.1, h.2]; ring
  ·
    have h01 := ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2.2
    have h11 := ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2.2
    have hdi := (((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2.2
    filter_upwards [h01, h11, hdi] with v h01 h11 hdi
    rw [hcol0, hcol1]
    rintro ⟨ha, hc⟩
    rw [SetLike.mem_coe, mem_integers_iff] at h01 h11 hdi
    have hnon := IsUltrametricDist.isNonarchimedean_norm (R := v.adicCompletion K)
    have hdet : ‖(d : 𝔸).2 v‖ < 1 := by
      have : (d : 𝔸).2 v = ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2 v -
          ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v := by
        rw [hdv]; rfl
      rw [this, sub_eq_add_neg]
      refine lt_of_le_of_lt (hnon _ _) (max_lt ?_ ?_)
      · dsimp only
        rw [norm_mul]
        calc ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v‖ * ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2 v‖
            ≤ ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v‖ * 1 :=
              mul_le_mul_of_nonneg_left h11 (norm_nonneg _)
          _ < 1 := by rw [mul_one]; exact ha
      · dsimp only
        rw [norm_neg, norm_mul]
        calc ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2 v‖ * ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v‖
            ≤ 1 * ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v‖ :=
              mul_le_mul_of_nonneg_right h01 (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hc
    have h1 := norm_snd_units_mul_inv d v
    have : ‖(d : 𝔸).2 v‖ * ‖((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ < 1 := by
      calc ‖(d : 𝔸).2 v‖ * ‖((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ ≤ ‖(d : 𝔸).2 v‖ * 1 :=
            mul_le_mul_of_nonneg_left hdi (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hdet
    rw [h1] at this
    exact lt_irrefl _ this

private def _root_.AutomorphicForm.BruhatUnipotent.pv {F : Type*} [NormedField F] (i : Fin 2) (a b : F) : F := ![(piv a b).1, (piv a b).2] i

p2m_export "AutomorphicForm.BruhatUnipotent" "pv"
theorem pv_zero {F : Type*} [NormedField F] (a b : F) : pv 0 a b = (piv a b).1 := rfl
theorem pv_one {F : Type*} [NormedField F] (a b : F) : pv 1 a b = (piv a b).2 := rfl

private theorem _root_.Measurable.pv {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    {Z : Type*} [MeasurableSpace Z] {f g : Z → F} (hf : Measurable f) (hg : Measurable g) (i : Fin 2) :
    Measurable fun z => AutomorphicForm.BruhatUnipotent.pv i (f z) (g z) := by
  fin_cases i
  · exact (hf.piv hg).fst
  · exact (hf.piv hg).snd

p2m_alias "P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.Measurable.pv" "Measurable.pv"

def rArch (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) : InfiniteAdeleRing K :=
  fun w => pv i ((c 0).1 w) ((c 1).1 w)

open Classical in

def rFin (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) : FiniteAdeleRing (𝓞 K) K :=
  if h : IsUnimod c then
    ⟨fun v => pv i ((c 0).2 v) ((c 1).2 v), by
      have h0 := (c 0).2.2
      have h1 := (c 1).2.2
      filter_upwards [h0, h1, h.2.2] with v h0 h1 h2
      rw [SetLike.mem_coe, mem_integers_iff] at h0 h1 ⊢
      have := norm_piv_le_one h0 h1 h2
      fin_cases i
      · exact this.1
      · exact this.2⟩
  else 0

def rRow (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) : AdeleRing (𝓞 K) K := (rArch c i, rFin c i)

open Classical in
theorem rFin_apply (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    (rFin c i) v = if IsUnimod c then pv i ((c 0).2 v) ((c 1).2 v) else 0 := by
  unfold rFin
  split_ifs with h
  · rfl
  · rfl

open Classical in
theorem rRow_dot {c : Fin 2 → AdeleRing (𝓞 K) K} (hc : IsUnimod c) : rRow c 0 * c 0 + rRow c 1 * c 1 = 1 := by
  refine Prod.ext ?_ ?_
  · funext w
    show pv 0 ((c 0).1 w) ((c 1).1 w) * (c 0).1 w + pv 1 ((c 0).1 w) ((c 1).1 w) * (c 1).1 w = 1
    rw [pv_zero, pv_one]
    exact piv_dot (hc.1 w)
  · apply RestrictedProduct.ext
    intro v
    show (rFin c 0) v * (c 0).2 v + (rFin c 1) v * (c 1).2 v = 1
    rw [rFin_apply, rFin_apply, if_pos hc, if_pos hc, pv_zero, pv_one]
    exact piv_dot (hc.2.1 v)

def secMat (p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  !![p.1 0, -((p.2 : 𝔸) * rRow p.1 1); p.1 1, (p.2 : 𝔸) * rRow p.1 0]

theorem det_secMat {p : Xp} (hp : IsUnimod p.1) : (secMat p).det = (p.2 : 𝔸) := by
  rw [secMat, Matrix.det_fin_two_of]
  have := rRow_dot hp
  linear_combination (p.2 : 𝔸) * this

open Classical in

def sec (p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ) : GL (Fin 2) (AdeleRing (𝓞 K) K) :=
  if hp : IsUnimod p.1 then Matrix.nonsingInvUnit (secMat p) (by rw [det_secMat hp]; exact Units.isUnit _)
  else 1

theorem sec_val {p : Xp} (hp : IsUnimod p.1) : ((sec p : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) = secMat p := by
  classical
  unfold sec
  rw [dif_pos hp]
  rfl

theorem proj_sec {p : Xp} (hp : IsUnimod p.1) : proj K (sec p) = p := by
  refine Prod.ext ?_ ?_
  · funext i
    show ((sec p : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) i 0 = p.1 i
    rw [sec_val hp]
    fin_cases i <;> rfl
  · apply Units.ext
    show ((Matrix.GeneralLinearGroup.det (sec p) : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) = p.2
    rw [Matrix.GeneralLinearGroup.val_det_apply, sec_val hp, det_secMat hp]

theorem proj_sec_of_exists {p : Xp} (hp : ∃ g : Gp, proj K g = p) : proj K (sec p) = p := by
  obtain ⟨g, rfl⟩ := hp
  exact proj_sec (isUnimod_of_proj g)

theorem sec_inv_val {p : Xp} (hp : IsUnimod p.1) :
    (((sec p)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) = ((p.2⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) • (secMat p).adjugate := by
  rw [Matrix.coe_units_inv, sec_val hp, Matrix.inv_def, det_secMat hp, Ring.inverse_unit]

end GLtwo

theorem measurableSet_eventually_cofinite {ι α : Type*} [MeasurableSpace α] [Countable ι]
    {P : ι → α → Prop} (hP : ∀ i, MeasurableSet {a | P i a}) :
    MeasurableSet {a | ∀ᶠ i in cofinite, P i a} := by
  have : {a | ∀ᶠ i in cofinite, P i a} = ⋃ T : Finset ι, ⋂ i, {a | i ∉ T → P i a} := by
    ext a
    simp only [Set.mem_setOf_eq, eventually_cofinite, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨h.toFinset, fun i hi => ?_⟩
      by_contra hc
      exact hi (h.mem_toFinset.mpr hc)
    · rintro ⟨T, hT⟩
      exact T.finite_toSet.subset fun i hi => by
        by_contra hiT
        exact hi (hT i hiT)
  rw [this]
  refine MeasurableSet.iUnion fun T => MeasurableSet.iInter fun i => ?_
  by_cases hi : i ∈ T
  · have : {a : α | i ∉ T → P i a} = Set.univ := by ext a; simp [hi]
    rw [this]; exact MeasurableSet.univ
  · have : {a : α | i ∉ T → P i a} = {a | P i a} := by ext a; simp [hi]
    rw [this]; exact hP i

section Measurability

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)
local notation "Xp" => (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ

attribute [local instance 2000] NumberField.AdelicHaar.glBorel

theorem borelSpace_G : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := borelSpace_glBorel _ _ _

theorem secondCountable_A : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

theorem secondCountable_G : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

attribute [local instance] borelSpace_G secondCountable_A secondCountable_G

@[reducible] def matMeasurableSpace : MeasurableSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))

attribute [local instance] matMeasurableSpace

theorem borelSpace_mat : BorelSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))

theorem secondCountable_mat : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))

attribute [local instance] borelSpace_mat secondCountable_mat

variable {K}

theorem measurable_matrix_iff {Z : Type*} [MeasurableSpace Z] {f : Z → Matrix (Fin 2) (Fin 2) 𝔸} :
    Measurable f ↔ ∀ i j, Measurable fun z => f z i j := by
  constructor
  · intro hf i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)
  · intro hf
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hf i j

theorem measurable_units_val : Measurable fun u : (AdeleRing (𝓞 K) K)ˣ => (u : 𝔸) :=
  Units.continuous_val.measurable

theorem measurable_units_inv_val : Measurable fun u : (AdeleRing (𝓞 K) K)ˣ => ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) :=
  (Units.continuous_val.comp continuous_inv).measurable

theorem measurable_GL_val : Measurable fun g : Gp => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) :=
  Units.continuous_val.measurable

theorem measurable_GL_entry (i j : Fin 2) : Measurable fun g : Gp => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) i j :=
  (Units.continuous_val.matrix_elem i j).measurable

theorem continuous_GLdet : Continuous (Matrix.GeneralLinearGroup.det : Gp → (AdeleRing (𝓞 K) K)ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ (Matrix.GeneralLinearGroup.det : Gp → (AdeleRing (𝓞 K) K)ˣ)) =
        fun g : Gp => ((g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : Gp => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)) =
        fun g : Gp => (((g⁻¹ : Gp) : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem measurable_proj : Measurable (proj K) := by
  refine Measurable.prodMk ?_ continuous_GLdet.measurable
  exact measurable_pi_iff.mpr fun i => measurable_GL_entry i 0

theorem measurable_act (h : Gp) : Measurable (act K h) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun i => ?_
    show Measurable fun p : Xp => ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec p.1 i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((measurable_pi_apply j).comp measurable_fst).const_mul _
  · exact (measurable_snd (α := Fin 2 → 𝔸)).const_mul _

theorem continuous_unipotentGL2 : Continuous fun y : 𝔸 => (unipotentGL2 y : Gp) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun y : 𝔸 => (unipotentGL2 y : Gp)) = fun y => !![1, y; 0, 1] := funext fun y => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun y : 𝔸 => (((unipotentGL2 y : Gp)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)) = fun y => !![1, -y; 0, 1] :=
      funext fun y => rfl
    show Continuous fun y : 𝔸 => (((unipotentGL2 y : Gp)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

theorem measurable_unipotentGL2 : Measurable fun y : 𝔸 => (unipotentGL2 y : Gp) :=
  continuous_unipotentGL2.measurable

theorem measurable_col_fst (i : Fin 2) (w : InfinitePlace K) :
    Measurable[_, borel _] fun c : Fin 2 → 𝔸 => (c i).1 w :=
  (measurable_fst_apply K w).comp (measurable_pi_apply i)

theorem measurable_col_snd (i : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    Measurable[_, borel _] fun c : Fin 2 → 𝔸 => (c i).2 v :=
  (measurable_snd_apply K v).comp (measurable_pi_apply i)

theorem measurableSet_isUnimod : MeasurableSet {c : Fin 2 → 𝔸 | IsUnimod c} := by
  have hA : ∀ w : InfinitePlace K, MeasurableSet {c : Fin 2 → 𝔸 | ¬ ((c 0).1 w = 0 ∧ (c 1).1 w = 0)} := by
    intro w
    letI : MeasurableSpace w.Completion := borel _
    haveI : BorelSpace w.Completion := ⟨rfl⟩
    have h0 := measurable_col_fst (K := K) 0 w (measurableSet_singleton 0)
    have h1 := measurable_col_fst (K := K) 1 w (measurableSet_singleton 0)
    have : {c : Fin 2 → 𝔸 | ¬ ((c 0).1 w = 0 ∧ (c 1).1 w = 0)} =
        ((fun c : Fin 2 → 𝔸 => (c 0).1 w) ⁻¹' {0} ∩ (fun c : Fin 2 → 𝔸 => (c 1).1 w) ⁻¹' {0})ᶜ := by
      ext c; simp
    rw [this]
    exact (h0.inter h1).compl
  have hB : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSet {c : Fin 2 → 𝔸 | ¬ ((c 0).2 v = 0 ∧ (c 1).2 v = 0)} := by
    intro v
    letI : MeasurableSpace (v.adicCompletion K) := borel _
    haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
    have h0 := measurable_col_snd (K := K) 0 v (measurableSet_singleton 0)
    have h1 := measurable_col_snd (K := K) 1 v (measurableSet_singleton 0)
    have : {c : Fin 2 → 𝔸 | ¬ ((c 0).2 v = 0 ∧ (c 1).2 v = 0)} =
        ((fun c : Fin 2 → 𝔸 => (c 0).2 v) ⁻¹' {0} ∩ (fun c : Fin 2 → 𝔸 => (c 1).2 v) ⁻¹' {0})ᶜ := by
      ext c; simp
    rw [this]
    exact (h0.inter h1).compl
  have hC : ∀ v : HeightOneSpectrum (𝓞 K),
      MeasurableSet {c : Fin 2 → 𝔸 | ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1)} := by
    intro v
    letI : MeasurableSpace (v.adicCompletion K) := borel _
    haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
    have h0 : Measurable fun c : Fin 2 → 𝔸 => ‖(c 0).2 v‖ := (measurable_col_snd (K := K) 0 v).norm
    have h1 : Measurable fun c : Fin 2 → 𝔸 => ‖(c 1).2 v‖ := (measurable_col_snd (K := K) 1 v).norm
    have : {c : Fin 2 → 𝔸 | ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1)} =
        ({c : Fin 2 → 𝔸 | ‖(c 0).2 v‖ < 1} ∩ {c : Fin 2 → 𝔸 | ‖(c 1).2 v‖ < 1})ᶜ := by
      ext c; simp
    rw [this]
    exact ((measurableSet_lt h0 measurable_const).inter (measurableSet_lt h1 measurable_const)).compl
  haveI : Countable (HeightOneSpectrum (𝓞 K)) := countable_heightOneSpectrum K
  have h1 : MeasurableSet {c : Fin 2 → 𝔸 | ∀ w : InfinitePlace K, ¬ ((c 0).1 w = 0 ∧ (c 1).1 w = 0)} := by
    rw [Set.setOf_forall]; exact MeasurableSet.iInter hA
  have h2 : MeasurableSet {c : Fin 2 → 𝔸 | ∀ v : HeightOneSpectrum (𝓞 K), ¬ ((c 0).2 v = 0 ∧ (c 1).2 v = 0)} := by
    rw [Set.setOf_forall]; exact MeasurableSet.iInter hB
  have h3 := measurableSet_eventually_cofinite hC
  simpa only [IsUnimod, Set.setOf_and] using h1.inter (h2.inter h3)

open Classical in
theorem measurable_rRow (i : Fin 2) : Measurable fun c : Fin 2 → 𝔸 => rRow c i := by
  refine measurable_adele_of_components K (fun w => ?_) (fun v => ?_)
  · letI : MeasurableSpace w.Completion := borel _
    haveI : BorelSpace w.Completion := ⟨rfl⟩
    exact (measurable_col_fst (K := K) 0 w).pv (measurable_col_fst (K := K) 1 w) i
  · letI : MeasurableSpace (v.adicCompletion K) := borel _
    haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
    have hpv : Measurable fun c : Fin 2 → 𝔸 => pv i ((c 0).2 v) ((c 1).2 v) :=
      (measurable_col_snd (K := K) 0 v).pv (measurable_col_snd (K := K) 1 v) i
    have hF : Measurable fun c : Fin 2 → 𝔸 => if IsUnimod c then pv i ((c 0).2 v) ((c 1).2 v) else 0 :=
      Measurable.ite measurableSet_isUnimod hpv measurable_const
    have hEq : (fun c : Fin 2 → 𝔸 => (rFin c i) v) =
        fun c => if IsUnimod c then pv i ((c 0).2 v) ((c 1).2 v) else 0 :=
      funext fun c => rFin_apply c i v
    show Measurable fun c : Fin 2 → 𝔸 => (rFin c i) v
    rw [hEq]
    exact hF

theorem measurable_secMat : Measurable fun p : Xp => secMat p := by
  rw [measurable_matrix_iff]
  have hc : ∀ i : Fin 2, Measurable fun p : Xp => p.1 i := fun i => (measurable_pi_apply i).comp measurable_fst
  have hδ : Measurable fun p : Xp => ((p.2 : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) := measurable_units_val.comp measurable_snd
  have hr : ∀ i : Fin 2, Measurable fun p : Xp => rRow p.1 i := fun i => (measurable_rRow i).comp measurable_fst
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [secMat] using hc 0
  · exact (hδ.mul (hr 1)).neg
  · simpa [secMat] using hc 1
  · have h__af := hδ.mul (hr 0)
    simp [secMat] at h__af ⊢
    exact h__af

theorem measurableSet_isUnimod_fst : MeasurableSet {p : Xp | IsUnimod p.1} :=
  measurableSet_isUnimod.preimage measurable_fst

open Classical in
theorem sec_val_eq (p : Xp) : ((sec p : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) = if IsUnimod p.1 then secMat p else 1 := by
  by_cases hp : IsUnimod p.1
  · rw [if_pos hp, sec_val hp]
  · unfold sec
    rw [dif_neg hp, if_neg hp]
    rfl

open Classical in
theorem sec_inv_val_eq (p : Xp) : (((sec p)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) =
    if IsUnimod p.1 then ((p.2⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) • (secMat p).adjugate else 1 := by
  by_cases hp : IsUnimod p.1
  · rw [if_pos hp, sec_inv_val hp]
  · unfold sec
    rw [dif_neg hp, if_neg hp, inv_one]
    rfl

theorem measurable_sec : Measurable (sec : Xp → Gp) := by
  classical
  refine measurable_units_of_val_of_inv ?_ ?_
  · have : (fun p : Xp => ((sec p : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)) =
        fun p : Xp => if IsUnimod p.1 then secMat p else 1 := funext fun p => sec_val_eq p
    rw [this]
    exact Measurable.ite measurableSet_isUnimod_fst measurable_secMat measurable_const
  · have : (fun p : Xp => (((sec p)⁻¹ : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)) =
        fun p : Xp => if IsUnimod p.1 then ((p.2⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) • (secMat p).adjugate else 1 :=
      funext fun p => sec_inv_val_eq p
    rw [this]
    refine Measurable.ite measurableSet_isUnimod_fst ?_ measurable_const
    have hδ : Measurable fun p : Xp => ((p.2⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸) :=
      measurable_units_inv_val.comp measurable_snd
    have hM := (measurable_matrix_iff (K := K)).mp measurable_secMat
    rw [measurable_matrix_iff]
    intro i j
    have hadj : Measurable fun p : Xp => (secMat p).adjugate i j := by
      fin_cases i <;> fin_cases j
      · simpa [Matrix.adjugate_fin_two] using hM 1 1
      · simpa [Matrix.adjugate_fin_two, Pi.neg_def] using (hM 0 1).neg
      · simpa [Matrix.adjugate_fin_two, Pi.neg_def] using (hM 1 0).neg
      · simpa [Matrix.adjugate_fin_two] using hM 0 0
    simpa [Matrix.smul_apply, Pi.mul_def] using hδ.mul hadj

end Measurability

section Bruhat

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance 2000] NumberField.AdelicHaar.glBorel

@[reducible] def unitsMeasurableSpace : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := borel _

attribute [local instance] unitsMeasurableSpace

theorem borelSpace_units : BorelSpace (AdeleRing (𝓞 K) K)ˣ := ⟨rfl⟩

attribute [local instance] borelSpace_units borelSpace_G secondCountable_A secondCountable_G

def uco (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K :=
  (((sec (proj K g))⁻¹ * g : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1

variable {K}

theorem measurable_uco : Measurable (uco K) :=
  (measurable_GL_entry 0 1).comp (((measurable_sec.comp measurable_proj).inv).mul measurable_id)

theorem sec_proj_inv_mul_eq (g : Gp) : (sec (proj K g))⁻¹ * g = unipotentGL2 (uco K g) := by
  have h := eq_mul_unipotentGL2_of_proj_eq (K := K) (g := sec (proj K g)) (g' := g)
    (proj_sec_of_exists ⟨g, rfl⟩)

  exact inv_mul_eq_iff_eq_mul.mpr h

theorem uco_mul_unipotentGL2 (g : Gp) (t : 𝔸) : uco K (g * unipotentGL2 t) = uco K g + t := by
  have hproj : proj K (g * unipotentGL2 t) = proj K g := proj_mul_unipotentGL2 g t
  have h1 : (sec (proj K (g * unipotentGL2 t)))⁻¹ * (g * unipotentGL2 t) =
      unipotentGL2 (uco K g + t) := by
    rw [hproj, ← mul_assoc, sec_proj_inv_mul_eq, unipotentGL2_add]
  show ((((sec (proj K (g * unipotentGL2 t)))⁻¹ * (g * unipotentGL2 t) : Gp) :
      Matrix (Fin 2) (Fin 2) 𝔸) 0 1) = uco K g + t
  rw [h1, unipotentGL2_coe]
  simp

theorem exists_bruhat (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure] :
    ∃ w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞, Measurable w ∧
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), ∫⁻ x, w (g * unipotentGL2 x) ∂μ = 1 := by

  obtain ⟨B⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts 𝔸))
  have hB0 : μ (B : Set 𝔸) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ B.interior_nonempty).ne'
  have hBtop : μ (B : Set 𝔸) ≠ ⊤ := B.isCompact.measure_lt_top.ne
  have hBm : MeasurableSet (B : Set 𝔸) := B.isCompact.isClosed.measurableSet
  refine ⟨fun g => (μ (B : Set 𝔸))⁻¹ * (B : Set 𝔸).indicator 1 (uco K g), ?_, ?_⟩
  · exact ((measurable_const.indicator hBm).comp measurable_uco).const_mul _
  · intro g
    have hfun : (fun x : 𝔸 => (μ (B : Set 𝔸))⁻¹ * (B : Set 𝔸).indicator 1 (uco K (g * unipotentGL2 x))) =
        fun x => (fun z : 𝔸 => (μ (B : Set 𝔸))⁻¹ * (B : Set 𝔸).indicator 1 z) (uco K g + x) := by
      funext x
      rw [uco_mul_unipotentGL2]
    have hinv := lintegral_add_left_eq_self (μ := μ)
      (fun z : 𝔸 => (μ (B : Set 𝔸))⁻¹ * (B : Set 𝔸).indicator 1 z) (uco K g)
    rw [hfun, hinv]
    rw [lintegral_const_mul _ ((measurable_one.indicator hBm)), lintegral_indicator_one hBm]
    exact ENNReal.inv_mul_cancel hB0 hBtop

end Bruhat

end AutomorphicForm.BruhatUnipotent
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm.BruhatUnipotent"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm.BruhatUnipotent"

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    ∃ w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞, Measurable w ∧
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1 := by
  haveI := hμ
  exact AutomorphicForm.BruhatUnipotent.exists_bruhat μ

end S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one (solution)
