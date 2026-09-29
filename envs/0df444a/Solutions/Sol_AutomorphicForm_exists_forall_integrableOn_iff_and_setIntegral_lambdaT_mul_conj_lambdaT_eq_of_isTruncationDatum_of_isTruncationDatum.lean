-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5495bceb-c10d-5bf9-8f7c-8ea08a77b54f

import Mathlib
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Pointwise ENNReal ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace R4TruncTransfer

variable {K : Type} [Field K] [NumberField K]

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

attribute [local instance] isHaar

theorem countable_numberField : Countable K :=
  (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl : Countable (GL (Fin 2) K) := by
  haveI := countable_numberField (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) K → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 K) K).range := by
  haveI := countable_gl (K := K)
  rw [MonoidHom.range_eq_map]
  have h : ((⊤ : Subgroup (GL (Fin 2) K)).map (globalPoints (𝓞 K) K) : Set (AdelicGL2 (𝓞 K) K)) =
      globalPoints (𝓞 K) K '' ((⊤ : Subgroup (GL (Fin 2) K)) : Set (GL (Fin 2) K)) := Subgroup.coe_map _ _
  have hc : (((⊤ : Subgroup (GL (Fin 2) K)).map (globalPoints (𝓞 K) K) : Set (AdelicGL2 (𝓞 K) K))).Countable := by
    rw [h]; exact (Set.countable_univ.mono (Set.subset_univ _)).image _
  exact hc.to_subtype

abbrev slab (K : Type) [Field K] [NumberField K] (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det K).measurable measurableSet_Icc

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    globalPoints (𝓞 K) K γ * g ∈ slab K α β ↔ g ∈ slab K α β := by
  simp only [Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) := by
  refine ⟨fun γ A hA => ?_⟩
  obtain ⟨γ, hγ⟩ := γ
  obtain ⟨γ₀, rfl⟩ := hγ
  have hpre : (fun x : AdelicGL2 (𝓞 K) K =>
      (⟨globalPoints (𝓞 K) K γ₀, ⟨γ₀, rfl⟩⟩ : (globalPoints (𝓞 K) K).range) • x) ⁻¹' A =
      (fun x => globalPoints (𝓞 K) K γ₀ * x) ⁻¹' A := rfl
  rw [hpre, Measure.restrict_apply (measurableSet_preimage (measurable_const_mul _) hA),
    Measure.restrict_apply hA]
  have hset : (fun x => globalPoints (𝓞 K) K γ₀ * x) ⁻¹' A ∩ slab K α β =
      (fun x => globalPoints (𝓞 K) K γ₀ * x) ⁻¹' (A ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset]
  exact measure_preimage_mul _ _ _

theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] {μ : Measure X} {s E : Set X}
    (hs : NullMeasurableSet s (μ.restrict E)) (hsE : s ⊆ E) (hE : MeasurableSet E) : NullMeasurableSet s μ := by
  obtain ⟨t, hts, htm, hteq⟩ := hs.exists_measurable_superset_ae_eq
  have h1 : (μ.restrict E) (t \ s) = 0 := (ae_eq_set.1 hteq).1
  rw [Measure.restrict_apply' hE] at h1
  refine (htm.inter hE).nullMeasurableSet.congr ?_
  rw [ae_eq_set]
  constructor
  · have : (t ∩ E) \ s = (t \ s) ∩ E := by
      ext x; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
    rw [this]; exact h1
  · have : s \ (t ∩ E) = ∅ := Set.diff_eq_empty.2 fun x hx => ⟨hts hx, hsE hx⟩
    rw [this]; exact measure_empty

theorem pow_le_adelicHeight_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : 0 ≤ c)
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ centreCutSiegelSet K c u d₁ d₂) :
    c ^ (∑ w : InfinitePlace K, w.mult) ≤ adelicHeight K g := by
  have h := centreCutSiegelSet_subset_integralWindowedSiegelSet (F := K) (u := u) (d₁ := d₁)
    (d₂ := d₂) hc hg
  obtain ⟨hK, hfloor, -⟩ := h
  rw [adelicHeight_eq_archHeight_of_mem hK]
  exact hfloor

theorem exists_forall_mem_borelSubgroup_of_lt (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 K) K)) (hTc : IsCompact Tc)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet K c u d₁ d₂) :
    ∃ T₀ : ℝ, ∀ g ∈ Φ₀, ∀ γ : GL (Fin 2) K,
      T₀ < adelicHeight K (globalPoints (𝓞 K) K γ * g) → γ ∈ borelSubgroup K := by
  obtain ⟨κ, C, hκ, hκC⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact K Tc hTc
  set h₀ : ℝ := κ * c ^ (∑ w : InfinitePlace K, w.mult) with hh₀
  have hcpow : 0 < c ^ (∑ w : InfinitePlace K, w.mult) := pow_pos hc _
  have hh₀pos : 0 < h₀ := mul_pos hκ hcpow
  have hfloor : ∀ g ∈ Φ₀, h₀ ≤ adelicHeight K g := by
    intro g hg
    have hg' := hΦ₀S hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg'
    obtain ⟨y, hy, x, hx, rfl⟩ := hg'
    have h1 : c ^ (∑ w : InfinitePlace K, w.mult) ≤ adelicHeight K x :=
      pow_le_adelicHeight_of_mem_centreCutSiegelSet hc.le hx
    have h2 : κ * adelicHeight K x ≤ adelicHeight K (x * y) := (hκC x y hy).1
    calc h₀ = κ * c ^ (∑ w : InfinitePlace K, w.mult) := rfl
      _ ≤ κ * adelicHeight K x := mul_le_mul_of_nonneg_left h1 hκ.le
      _ ≤ adelicHeight K (x * y) := h2
  refine ⟨h₀⁻¹, fun g hg γ hlt => ?_⟩
  by_contra hγ
  have h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by rwa [mem_borelSubgroup_iff] at hγ
  have hprod := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ h10 g
  have hHg : 0 < adelicHeight K g := adelicHeight_pos g
  have hle : adelicHeight K (globalPoints (𝓞 K) K γ * g) ≤ (adelicHeight K g)⁻¹ := by
    rw [← one_div, le_div_iff₀ hHg]
    exact hprod
  have hle' : adelicHeight K (globalPoints (𝓞 K) K γ * g) ≤ h₀⁻¹ :=
    hle.trans ((inv_le_inv₀ hHg hh₀pos).mpr (hfloor g hg))
  linarith

section Arthur

variable (K)

abbrev boxMeasure : Measure (AdeleRing (𝓞 K) K) := ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)

abbrev cT (f : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  constantTerm (boxMeasure K) (fun x => unipotentGL2 x) f

abbrev Λn (T : ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  lambdaT (boxMeasure K) (fun x => unipotentGL2 x) (adelicHeight K) T f

variable {K}

def High (V : Set (AdelicGL2 (𝓞 K) K)) (T : ℝ) (g : AdelicGL2 (𝓞 K) K) : Prop :=
  ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ V ∧ T < adelicHeight K (globalPoints (𝓞 K) K γ * g)

open Classical in

def arthur (V : Set (AdelicGL2 (𝓞 K) K)) (T : ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if h : High V T g then f g - cT K f (globalPoints (𝓞 K) K (Classical.choose h) * g) else f g

def BorelHigh (V : Set (AdelicGL2 (𝓞 K) K)) (T : ℝ) : Prop :=
  ∀ y ∈ V, ∀ γ : GL (Fin 2) K, T < adelicHeight K (globalPoints (𝓞 K) K γ * y) → γ ∈ borelSubgroup K

theorem high_mul_iff (V : Set (AdelicGL2 (𝓞 K) K)) (T : ℝ) (δ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    High V T (globalPoints (𝓞 K) K δ * g) ↔ High V T g := by
  constructor
  · rintro ⟨γ, hV, hT⟩
    refine ⟨γ * δ, ?_, ?_⟩ <;> rw [map_mul, mul_assoc]
    · exact hV
    · exact hT
  · rintro ⟨γ, hV, hT⟩
    refine ⟨γ * δ⁻¹, ?_, ?_⟩ <;> rw [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    · exact hV
    · exact hT

theorem mem_borel_of_two_high {V : Set (AdelicGL2 (𝓞 K) K)} {T : ℝ} (hB : BorelHigh V T)
    {g : AdelicGL2 (𝓞 K) K} {γ₀ γ₁ : GL (Fin 2) K}
    (h₀V : globalPoints (𝓞 K) K γ₀ * g ∈ V)
    (h₁T : T < adelicHeight K (globalPoints (𝓞 K) K γ₁ * g)) :
    γ₁ * γ₀⁻¹ ∈ borelSubgroup K := by
  refine hB _ h₀V (γ₁ * γ₀⁻¹) ?_
  rwa [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]

theorem arthur_globalPoints_mul {V : Set (AdelicGL2 (𝓞 K) K)} {T : ℝ} (hB : BorelHigh V T)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g)
    (δ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    arthur V T f (globalPoints (𝓞 K) K δ * g) = arthur V T f g := by
  have hfB : ∀ γ ∈ borelSubgroup K, ∀ h : AdelicGL2 (𝓞 K) K, f (globalPoints (𝓞 K) K γ * h) = f h :=
    fun γ _ h => hf γ h
  by_cases hg : High V T g
  · have hg' : High V T (globalPoints (𝓞 K) K δ * g) := (high_mul_iff V T δ g).2 hg
    unfold arthur
    rw [dif_pos hg', dif_pos hg, hf δ g]
    congr 1

    set γ₀ := Classical.choose hg with hγ₀
    set γ₁ := Classical.choose hg' with hγ₁
    have h₀ := Classical.choose_spec hg
    have h₁ := Classical.choose_spec hg'
    rw [← hγ₀] at h₀
    rw [← hγ₁] at h₁

    have h₁' : T < adelicHeight K (globalPoints (𝓞 K) K (γ₁ * δ) * g) := by
      rw [map_mul, mul_assoc]; exact h₁.2
    have hρ : γ₁ * δ * γ₀⁻¹ ∈ borelSubgroup K := mem_borel_of_two_high hB h₀.1 h₁'
    have hrew : globalPoints (𝓞 K) K γ₁ * (globalPoints (𝓞 K) K δ * g)
        = globalPoints (𝓞 K) K (γ₁ * δ * γ₀⁻¹) * (globalPoints (𝓞 K) K γ₀ * g) := by
      simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    rw [hrew]
    exact AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup K hfB hρ _
  · have hg' : ¬ High V T (globalPoints (𝓞 K) K δ * g) := fun h => hg ((high_mul_iff V T δ g).1 h)
    unfold arthur
    rw [dif_neg hg', dif_neg hg, hf δ g]

theorem arthur_eq_lambdaT_of_mem {V : Set (AdelicGL2 (𝓞 K) K)} {T : ℝ} (hB : BorelHigh V T)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g)
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ V) :
    arthur V T f g = Λn K T f g := by
  have hfB : ∀ γ ∈ borelSubgroup K, ∀ h : AdelicGL2 (𝓞 K) K, f (globalPoints (𝓞 K) K γ * h) = f h :=
    fun γ _ h => hf γ h
  by_cases hH : T < adelicHeight K g
  · have hhigh : High V T g := ⟨1, by rw [map_one, one_mul]; exact hg, by rw [map_one, one_mul]; exact hH⟩
    unfold arthur
    dsimp only [Λn, cT]
    rw [dif_pos hhigh, lambdaT_apply_of_lt _ _ hH]
    congr 1
    set γ₀ := Classical.choose hhigh with hγ₀
    have h₀ := Classical.choose_spec hhigh
    rw [← hγ₀] at h₀
    have hγ₀B : γ₀ ∈ borelSubgroup K := hB g hg γ₀ h₀.2
    exact AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup K hfB hγ₀B g
  · have hnot : ¬ High V T g := by
      rintro ⟨γ, -, hT⟩
      have hγB : γ ∈ borelSubgroup K := hB g hg γ hT
      rw [NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup K hγB g] at hT
      exact hH hT
    unfold arthur
    dsimp only [Λn]
    rw [dif_neg hnot, lambdaT_apply_of_le _ _ (not_lt.1 hH)]

end Arthur

theorem main (α β : ℝ)
    (d d' : (ℝ × ℝ × ℝ × ℝ) × Set (AdelicGL2 (𝓞 K) K) × Set (AdelicGL2 (𝓞 K) K))
    (hd : IsTruncationDatum K α β d) (hd' : IsTruncationDatum K α β d') :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ),
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), a (globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), b (globalPoints (𝓞 K) K γ * g) = b g) →
        (IntegrableOn (fun g => Λn K T a g * conj (Λn K T b g)) d.2.2 (adelicGLHaar (Fin 2) (𝓞 K) K) ↔
          IntegrableOn (fun g => Λn K T a g * conj (Λn K T b g)) d'.2.2 (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
        ∫ g in d.2.2, Λn K T a g * conj (Λn K T b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          = ∫ g in d'.2.2, Λn K T a g * conj (Λn K T b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨hc, hTc, hΦS, hΦs, hΦ⟩ := hd
  obtain ⟨hc', hTc', hΦS', hΦs', hΦ'⟩ := hd'
  obtain ⟨T₁, hT₁⟩ := exists_forall_mem_borelSubgroup_of_lt _ _ _ _ hc _ hTc _ hΦS
  obtain ⟨T₂, hT₂⟩ := exists_forall_mem_borelSubgroup_of_lt _ _ _ _ hc' _ hTc' _ hΦS'
  refine ⟨max T₁ T₂, fun T hT a b ha hb => ?_⟩

  set Φ₀ : Set (AdelicGL2 (𝓞 K) K) := d.2.2 with hΦ₀def
  set Φ₀' : Set (AdelicGL2 (𝓞 K) K) := d'.2.2 with hΦ₀'def
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set V : Set (AdelicGL2 (𝓞 K) K) := Φ₀ ∪ Φ₀' with hV

  have hB : BorelHigh V T := by
    rintro y (hy | hy) γ hlt
    · exact hT₁ y hy γ (lt_of_le_of_lt ((le_max_left _ _).trans hT) hlt)
    · exact hT₂ y hy γ (lt_of_le_of_lt ((le_max_right _ _).trans hT) hlt)

  set f : AdelicGL2 (𝓞 K) K → ℂ := fun g => Λn K T a g * conj (Λn K T b g) with hf
  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => arthur V T a g * conj (arthur V T b g) with hF
  have hFinv : ∀ (γ : (globalPoints (𝓞 K) K).range) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x := by
    rintro ⟨_, γ, rfl⟩ x
    show F (globalPoints (𝓞 K) K γ * x) = F x
    simp only [hF, arthur_globalPoints_mul hB ha, arthur_globalPoints_mul hB hb]
  have hFf : ∀ g ∈ V, F g = f g := by
    intro g hg
    simp only [hF, hf, arthur_eq_lambdaT_of_mem hB ha hg, arthur_eq_lambdaT_of_mem hB hb hg]

  have hslab_m : MeasurableSet (slab K α β) := measurableSet_slab α β
  have hΦ₀n : NullMeasurableSet Φ₀ μ := nullMeasurableSet_of_restrict hΦ.nullMeasurableSet hΦs hslab_m
  have hΦ₀'n : NullMeasurableSet Φ₀' μ := nullMeasurableSet_of_restrict hΦ'.nullMeasurableSet hΦs' hslab_m
  have hae : ∀ᵐ x ∂μ.restrict Φ₀, F x = f x :=
    (ae_restrict_iff'₀ hΦ₀n).2 (Filter.Eventually.of_forall fun x hx => hFf x (Or.inl hx))
  have hae' : ∀ᵐ x ∂μ.restrict Φ₀', F x = f x :=
    (ae_restrict_iff'₀ hΦ₀'n).2 (Filter.Eventually.of_forall fun x hx => hFf x (Or.inr hx))

  haveI := smulInvariantMeasure_restrict_slab (K := K) α β
  have hI : IntegrableOn F Φ₀ μ ↔ IntegrableOn F Φ₀' μ := by
    have h := IsFundamentalDomain.integrableOn_iff (f := F) hΦ hΦ' hFinv
    rwa [IntegrableOn, IntegrableOn, Measure.restrict_restrict_of_subset hΦs,
      Measure.restrict_restrict_of_subset hΦs'] at h
  have hE : ∫ x in Φ₀, F x ∂μ = ∫ x in Φ₀', F x ∂μ := by
    have h := IsFundamentalDomain.setIntegral_eq (f := F) hΦ hΦ' hFinv
    rwa [Measure.restrict_restrict_of_subset hΦs, Measure.restrict_restrict_of_subset hΦs'] at h
  refine ⟨?_, ?_⟩
  · calc IntegrableOn f Φ₀ μ ↔ IntegrableOn F Φ₀ μ :=
          ⟨fun h => h.congr_fun_ae (hae.mono fun x hx => hx.symm), fun h => h.congr_fun_ae hae⟩
      _ ↔ IntegrableOn F Φ₀' μ := hI
      _ ↔ IntegrableOn f Φ₀' μ :=
          ⟨fun h => h.congr_fun_ae hae', fun h => h.congr_fun_ae (hae'.mono fun x hx => hx.symm)⟩
  · calc ∫ x in Φ₀, f x ∂μ = ∫ x in Φ₀, F x ∂μ := (integral_congr_ae hae).symm
      _ = ∫ x in Φ₀', F x ∂μ := hE
      _ = ∫ x in Φ₀', f x ∂μ := integral_congr_ae hae'

end R4TruncTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum.R4TruncTransfer"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum.R4TruncTransfer"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ)
    (d d' : (ℝ × ℝ × ℝ × ℝ) × Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) × Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hd : AutomorphicForm.IsTruncationDatum F α β d) (hd' : AutomorphicForm.IsTruncationDatum F α β d') :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ),
        (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F),
          a (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = a g) →
        (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F),
          b (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = b g) →
        (IntegrableOn
            (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
              conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g))
            d.2.2 (adelicGLHaar (Fin 2) (𝓞 F) F) ↔
          IntegrableOn
            (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
              conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g))
            d'.2.2 (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
        ∫ g in d.2.2,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g)
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          = ∫ g in d'.2.2,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g)
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
  R4TruncTransfer.main α β d d' hd hd'

end S_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum (solution)
