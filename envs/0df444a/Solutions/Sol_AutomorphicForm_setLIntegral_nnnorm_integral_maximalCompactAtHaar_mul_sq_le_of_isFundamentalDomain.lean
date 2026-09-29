-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0647d10d-1ba0-5f38-bc4c-ebb3a30d2339

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

noncomputable section

namespace Ws23
namespace JensenMass

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable (K : Type) [Field K] [NumberField K]

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

scoped instance instRightInvμ : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

variable {K}

theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

theorem normDet_eq_one_of_mem {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAt K ∅) :
    ideleNorm K (Matrix.GeneralLinearGroup.det k) = 1 := by
  have hk' : k ∈ adelicMaximalCompact K := (mem_maximalCompactAt_iff.1 hk).1
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K k (glFin_mem_finiteIntegralGL2 hk')]
  refine Finset.prod_eq_one fun w _ => ?_
  have h1 : NumberField.AdelicVolume.archDetNorm w k = 1 := (isRowIsometry_archComponent hk' w).1
  rw [h1, one_pow]

theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

theorem smulInvariant_restrict (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict S) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ S = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, hS γ x]
  rw [hset, measure_preimage_mul]

theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem fd_preimage (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    (f : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (hf : MeasurePreserving f (μ K) (μ K))
    (hcomm : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), f (γ • x) = γ • f x) :
    IsFundamentalDomain (Γ K) (f ⁻¹' Φ₀) ((μ K).restrict (f ⁻¹' slab K α β)) :=
  hFD.preimage_of_equiv (hf.restrict_preimage (slab_measurable α β)).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun γ x => hcomm γ x)

theorem mp_mul_right (z : AdelicGL2 (𝓞 K) K) : MeasurePreserving (· * z) (μ K) (μ K) :=
  measurePreserving_mul_right (μ K) z

theorem comm_right (y : AdelicGL2 (𝓞 K) K) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    (γ • x) * y⁻¹ = γ • (x * y⁻¹) := by
  simp only [Γ_smul, mul_assoc]

theorem preimage_right_eq (y : AdelicGL2 (𝓞 K) K) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    (fun x => x * y) ⁻¹' ((· * y⁻¹) ⁻¹' Φ₀) = Φ₀ := by
  ext x
  simp [mul_inv_cancel_right]

theorem emb_right (y : AdelicGL2 (𝓞 K) K) : MeasurableEmbedding (fun x : AdelicGL2 (𝓞 K) K => x * y) :=
  (MeasurableEquiv.mulRight y).measurableEmbedding

theorem preimage_slab_eq_of_normDet_eq_one (α β : ℝ) {y : AdelicGL2 (𝓞 K) K}
    (hy : ideleNorm K (Matrix.GeneralLinearGroup.det y) = 1) : (· * y⁻¹) ⁻¹' slab K α β = slab K α β := by
  ext x
  show ideleNorm K (Matrix.GeneralLinearGroup.det (x * y⁻¹)) ∈ Set.Icc α β ↔
    ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
  rw [normDet_mul, map_inv]
  have hinv : ideleNorm K (Matrix.GeneralLinearGroup.det y)⁻¹ = 1 := by
    have h := ideleNorm_mul (F := K) (Matrix.GeneralLinearGroup.det y) (Matrix.GeneralLinearGroup.det y)⁻¹
    rw [mul_inv_cancel, hy, one_mul] at h

    have h1 : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
      have h' := ideleNorm_mul (F := K) 1 1
      rw [mul_one] at h'
      exact (mul_right_cancel₀ (ideleNorm_pos (F := K) 1).ne' (h'.symm.trans (one_mul _).symm))
    rw [← h, h1]
  rw [hinv, mul_one]

theorem setLIntegral_translate_eq (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) {y : AdelicGL2 (𝓞 K) K}
    (hy : ideleNorm K (Matrix.GeneralLinearGroup.det y) = 1)
    (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), G (globalPoints (𝓞 K) K γ * x) = G x) :
    ∫⁻ x in Φ₀, G (x * y) ∂(μ K) = ∫⁻ x in Φ₀, G x ∂(μ K) := by
  haveI := countable_Γ (K := K)
  have hS' := preimage_slab_eq_of_normDet_eq_one α β hy
  have hFD₁ : IsFundamentalDomain (Γ K) ((· * y⁻¹) ⁻¹' Φ₀) ((μ K).restrict (slab K α β)) := by
    have h := fd_preimage α β Φ₀ hFD _ (mp_mul_right y⁻¹) (comm_right y)
    rwa [hS'] at h
  have hsub₁ : (· * y⁻¹) ⁻¹' Φ₀ ⊆ slab K α β := by
    rw [← hS']; exact Set.preimage_mono hΦ₀
  haveI hinv : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) :=
    smulInvariant_restrict _ fun γ x => slab_Γ_stable α β γ x
  have hGΓ : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), G (γ • x) = G x := fun γ x => by
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hΓ]
  have hr₁ : ∫⁻ x in (· * y⁻¹) ⁻¹' Φ₀, G x ∂((μ K).restrict (slab K α β)) = ∫⁻ x in (· * y⁻¹) ⁻¹' Φ₀, G x ∂(μ K) := by
    rw [Measure.restrict_restrict₀ hFD₁.nullMeasurableSet, Set.inter_eq_left.mpr hsub₁]
  have hr₀ : ∫⁻ x in Φ₀, G x ∂((μ K).restrict (slab K α β)) = ∫⁻ x in Φ₀, G x ∂(μ K) := by
    rw [Measure.restrict_restrict₀ hFD.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀]
  calc ∫⁻ x in Φ₀, G (x * y) ∂(μ K)
      = ∫⁻ x in (· * y⁻¹) ⁻¹' Φ₀, G x ∂(μ K) := by
        conv_lhs => rw [← preimage_right_eq y Φ₀]
        exact (mp_mul_right y).setLIntegral_comp_preimage_emb (emb_right y) G _
    _ = ∫⁻ x in (· * y⁻¹) ⁻¹' Φ₀, G x ∂((μ K).restrict (slab K α β)) := hr₁.symm
    _ = ∫⁻ x in Φ₀, G x ∂((μ K).restrict (slab K α β)) := hFD₁.setLIntegral_eq hFD G hGΓ
    _ = ∫⁻ x in Φ₀, G x ∂(μ K) := hr₀

section Riemann

variable (K)

abbrev Kc : Type := ↥(maximalCompactAt K ∅)

abbrev μK : Measure (Kc K) := maximalCompactAtHaar K ∅

def coords (k : Kc K) : ∀ w : InfinitePlace K, (Fin 2 → Fin 2 → w.Completion) × (Fin 2 → Fin 2 → w.Completion) :=
  fun w => (fun i j => ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j,
    fun i j => (((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)))⁻¹ : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j)

variable {K}

theorem continuous_coords : Continuous (coords K) := by
  refine continuous_pi fun w => Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((Units.continuous_val.comp ((continuous_archComponent K w).comp ((continuous_glArch (𝓞 K) K).comp
      continuous_subtype_val))).matrix_elem i j)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((Units.continuous_val.comp (continuous_inv.comp ((continuous_archComponent K w).comp
      ((continuous_glArch (𝓞 K) K).comp continuous_subtype_val)))).matrix_elem i j)

theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 K) K}
    (hA : glArch (𝓞 K) K a = glArch (𝓞 K) K b) (hF : glFin (𝓞 K) K a = glFin (𝓞 K) K b) : a = b := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) hA
    simpa only [glArch_apply] using this
  · have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) hF
    simpa only [glFin_apply] using this

theorem glFin_eq_one_of_mem {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAt K ∅) : glFin (𝓞 K) K k = 1 := by
  have h := (mem_maximalCompactAt_iff.1 hk).2
  apply Units.ext
  ext i j v
  have hv := congrArg (fun m : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) =>
    (m : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) i j) (h v (Finset.notMem_empty v))
  simp only [finComponent_apply] at hv
  rw [hv, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem injective_coords : Function.Injective (coords K) := by
  intro a b h
  apply Subtype.ext
  refine eq_of_glArch_eq_of_glFin_eq ?_ (by rw [glFin_eq_one_of_mem a.2, glFin_eq_one_of_mem b.2])
  apply Units.ext
  ext i j
  funext w
  have hw := congrArg (fun c => (c w).1 i j) h
  simpa only [coords, archComponent_apply] using hw

theorem isClosedEmbedding_coords : Topology.IsClosedEmbedding (coords K) :=
  continuous_coords.isClosedEmbedding injective_coords

@[reducible] def metricKc : MetricSpace (Kc K) :=
  (MetricSpace.induced (coords K) injective_coords inferInstance).replaceTopology
    isClosedEmbedding_coords.isInducing.eq_induced

theorem exists_partition (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (E : Fin N → Set (Kc K)) (c : Fin N → Kc K),
      (∀ i, MeasurableSet (E i)) ∧ Pairwise (Function.onFun Disjoint E) ∧ (⋃ i, E i) = Set.univ ∧
      ∀ i, ∀ k ∈ E i, @dist (Kc K) (metricKc (K := K)).toDist k (c i) < ε := by
  letI : MetricSpace (Kc K) := metricKc
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set (Kc K))) hε
  obtain ⟨N, e⟩ : ∃ N : ℕ, Nonempty (Fin N ≃ t) := ⟨htf.toFinset.card, ⟨(htf.toFinset.equivFin.symm.trans (Equiv.subtypeEquivRight
    (fun x => by simp))) ⟩⟩
  obtain ⟨e⟩ := e
  let B : ℕ → Set (Kc K) := fun n => if h : n < N then Metric.ball ((e ⟨n, h⟩ : t) : Kc K) ε else ∅
  refine ⟨N, fun i => disjointed B i, fun i => ((e i : t) : Kc K), fun i => ?_, ?_, ?_, ?_⟩
  · refine MeasurableSet.disjointed (fun n => ?_) i
    by_cases h : n < N
    · simp only [B, dif_pos h]; exact Metric.isOpen_ball.measurableSet
    · simp only [B, dif_neg h]; exact MeasurableSet.empty
  · intro i j hij
    exact disjoint_disjointed B (Fin.val_injective.ne hij)
  · apply Set.eq_univ_of_forall
    intro k
    have hk := hcov (Set.mem_univ k)
    simp only [Set.mem_iUnion] at hk
    obtain ⟨x, hx, hkx⟩ := hk
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hkB : k ∈ B i := by
      simp only [B, dif_pos i.2, hi]
      exact hkx
    have hkU : k ∈ ⋃ n, B n := Set.mem_iUnion.2 ⟨i, hkB⟩
    rw [← iUnion_disjointed] at hkU
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hkU
    have hnN : n < N := by
      by_contra hnN
      have : disjointed B n ⊆ B n := disjointed_subset B n
      have := this hn
      simp only [B, dif_neg hnN] at this
      exact this
    exact Set.mem_iUnion.2 ⟨⟨n, hnN⟩, hn⟩
  · intro i k hk
    have hk' : k ∈ B i := disjointed_subset B i hk
    simp only [B, dif_pos i.2] at hk'
    exact hk'

def partN (m : ℕ) : ℕ := (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose
def partE (m : ℕ) : Fin (partN (K := K) m) → Set (Kc K) :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose
def partC (m : ℕ) : Fin (partN (K := K) m) → Kc K :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose_spec.choose
theorem partE_spec (m : ℕ) :
    (∀ i, MeasurableSet (partE (K := K) m i)) ∧ Pairwise (Function.onFun Disjoint (partE (K := K) m)) ∧
      (⋃ i, partE (K := K) m i) = Set.univ ∧
      ∀ i, ∀ k ∈ partE (K := K) m i, @dist (Kc K) (metricKc (K := K)).toDist k (partC m i) < 1 / ((m : ℝ) + 1) :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose_spec.choose_spec

def riemannSum (m : ℕ) (h : Kc K → ℂ) : ℂ := ∑ i, ((μK K (partE m i)).toReal : ℂ) * h (partC m i)

theorem tendsto_riemannSum (h : Kc K → ℂ) (hh : Continuous h) :
    Filter.Tendsto (fun m => riemannSum m h) Filter.atTop (nhds (∫ k, h k ∂(μK K))) := by
  letI : MetricSpace (Kc K) := metricKc
  rw [Metric.tendsto_atTop]
  intro η hη

  have huc : UniformContinuous h := CompactSpace.uniformContinuous_of_continuous hh
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuous_iff.1 huc (η / 2) (half_pos hη)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  refine ⟨M, fun m hm => ?_⟩
  have hmesh : 1 / ((m : ℝ) + 1) < δ := by
    have hMpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hMpos]
    have : 1 / δ < (m : ℝ) + 1 := hM.trans_le (by exact_mod_cast Nat.le_succ_of_le hm)
    rw [div_lt_iff₀ hδ] at this
    linarith
  obtain ⟨hmeas, hdisj, hcov, hsmall⟩ := partE_spec (K := K) m
  have hint : Integrable h (μK K) := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h) |>.mono_measure le_rfl

  have hsplit : ∫ k, h k ∂(μK K) = ∑ i, ∫ k in partE m i, h k ∂(μK K) := by
    rw [← MeasureTheory.setIntegral_univ, ← hcov, MeasureTheory.integral_iUnion hmeas hdisj hint.integrableOn, tsum_fintype]

  have hconst : ∀ i, ((μK K (partE m i)).toReal : ℂ) * h (partC m i) = ∫ k in partE m i, h (partC m i) ∂(μK K) := by
    intro i
    rw [MeasureTheory.setIntegral_const, Complex.real_smul]
    rfl
  rw [dist_eq_norm, riemannSum, hsplit, ← Finset.sum_sub_distrib]
  calc ‖∑ i, (((μK K (partE m i)).toReal : ℂ) * h (partC m i) - ∫ k in partE m i, h k ∂(μK K))‖
      ≤ ∑ i, ‖((μK K (partE m i)).toReal : ℂ) * h (partC m i) - ∫ k in partE m i, h k ∂(μK K)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (η / 2) * (μK K (partE m i)).toReal := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hconst, ← MeasureTheory.integral_sub (MeasureTheory.integrable_const _) hint.integrableOn]
        have hle : ∀ k ∈ partE m i, ‖h (partC m i) - h k‖ ≤ η / 2 := fun k hk => by
          rw [← dist_eq_norm]
          exact (hδc (by rw [dist_comm]; exact (hsmall i k hk).trans hmesh)).le
        exact MeasureTheory.norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hle
    _ = (η / 2) * ∑ i, (μK K (partE m i)).toReal := by rw [Finset.mul_sum]
    _ = (η / 2) * 1 := by
        congr 1
        have hU : μK K Set.univ = ∑ i, μK K (partE m i) := by
          rw [← hcov, ← measure_biUnion_finset (fun i _ j _ hij => hdisj hij) (fun i _ => hmeas i)]
          simp
        rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), ← hU, measure_univ, ENNReal.toReal_one]
    _ < η := by linarith

end Riemann

section Assembly

def avgSum (κ : Kc K → ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) (m : ℕ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  riemannSum m fun k => (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K))

theorem avgSum_eq (κ : Kc K → ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) (m : ℕ) (x : AdelicGL2 (𝓞 K) K) :
    avgSum κ f m x = ∑ i, (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) * f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)) := by
  simp only [avgSum, riemannSum, Complex.ofReal_mul, mul_assoc]

theorem continuous_avgSum (κ : Kc K → ℝ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (m : ℕ) :
    Continuous (avgSum κ f m) := by
  have e : avgSum κ f m = fun x => ∑ i, (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) *
      f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)) := funext (avgSum_eq κ f m)
  rw [e]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hf.comp (continuous_mul_const _))

theorem tendsto_avgSum {κ : Kc K → ℝ} (hκc : Continuous κ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (x : AdelicGL2 (𝓞 K) K) :
    Filter.Tendsto (fun m => avgSum κ f m x) Filter.atTop
      (nhds (∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K))) :=
  tendsto_riemannSum _ ((Complex.continuous_ofReal.comp hκc).mul (hf.comp (continuous_const_mul x |>.comp continuous_subtype_val)))

theorem tendsto_sum_weights {κ : Kc K → ℝ} (hκc : Continuous κ) (hκ1 : ∫ k, κ k ∂(μK K) = 1) :
    Filter.Tendsto (fun m => ∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun m => riemannSum m fun k => (κ k : ℂ)) Filter.atTop (nhds (∫ k, (κ k : ℂ) ∂(μK K))) :=
    tendsto_riemannSum (K := K) (fun k => (κ k : ℂ)) (Complex.continuous_ofReal.comp hκc)
  have hint : Integrable (fun k => (κ k : ℂ)) (μK K) :=
    (Complex.continuous_ofReal.comp hκc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre : (∫ k, (κ k : ℂ) ∂(μK K)).re = 1 := by
    rw [← hκ1]
    have := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at this
    exact this.symm
  have h' := (Complex.continuous_re.tendsto _).comp h
  rw [hre] at h'
  refine h'.congr fun m => ?_
  simp only [Function.comp_apply, riemannSum, Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem weights_nonneg {κ : Kc K → ℝ} (hκ0 : ∀ k, 0 ≤ κ k) (m : ℕ) (i : Fin (partN (K := K) m)) :
    0 ≤ (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) :=
  mul_nonneg ENNReal.toReal_nonneg (hκ0 _)

theorem lintegral_avgSum_le (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    {κ : Kc K → ℝ} (hκ0 : ∀ k, 0 ≤ κ k) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfinv : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * x) = f x) (m : ℕ) :
    ∫⁻ x in Φ₀, (‖avgSum κ f m x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) ≤
      ENNReal.ofReal ((∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) ^ 2) *
        ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
  set ν : Measure (AdelicGL2 (𝓞 K) K) := (μ K).restrict Φ₀ with hν

  have hL2 : ∀ g : AdelicGL2 (𝓞 K) K → ℂ, ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂ν = (eLpNorm g 2 ν) ^ 2 := by
    intro g
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ENNReal.toReal_ofNat, one_div,
      ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) = 2 by norm_num, inv_mul_cancel₀ (by norm_num),
      ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num]
    rfl

  have htr : ∀ i, eLpNorm (fun x => f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K))) 2 ν = eLpNorm f 2 ν := by
    intro i
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    congr 1
    exact setLIntegral_translate_eq α β Φ₀ hΦ₀ hFD (normDet_eq_one_of_mem (partC m i).2) (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      fun γ x => by show ‖f (_ * x)‖ₑ ^ _ = ‖f x‖ₑ ^ _; rw [hfinv]

  have hmeas : ∀ i, AEStronglyMeasurable (fun x => (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) *
      f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K))) ν := fun i =>
    (continuous_const.mul (hf.comp (continuous_mul_const _))).aestronglyMeasurable
  have hmink : eLpNorm (avgSum κ f m) 2 ν ≤ ∑ i, ENNReal.ofReal ((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) * eLpNorm f 2 ν := by
    have e : avgSum κ f m = ∑ i, fun x => (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) *
        f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)) := by
      funext x; rw [avgSum_eq, Finset.sum_apply]
    rw [e]
    refine (eLpNorm_sum_le (fun i _ => hmeas i) one_le_two).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [show (fun x => (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) * f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K))) =
      (((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i) : ℝ) : ℂ) • fun x => f (x * ((partC (K := K) m i : Kc K) : AdelicGL2 (𝓞 K) K)) from rfl,
      eLpNorm_const_smul, htr i, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (weights_nonneg hκ0 m i)]

  rw [hν] at hL2
  rw [hL2, hL2]
  calc eLpNorm (avgSum κ f m) 2 ((μ K).restrict Φ₀) ^ 2
      ≤ (∑ i, ENNReal.ofReal ((μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) * eLpNorm f 2 ((μ K).restrict Φ₀)) ^ 2 :=
        pow_le_pow_left' hmink 2
    _ = ENNReal.ofReal ((∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) ^ 2) * eLpNorm f 2 ((μ K).restrict Φ₀) ^ 2 := by
        rw [← Finset.sum_mul, mul_pow, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => weights_nonneg hκ0 m i),
          ENNReal.ofReal_pow (Finset.sum_nonneg fun i _ => weights_nonneg hκ0 m i)]

theorem main (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (κ : Kc K → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(μK K) = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfinv : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * x) = f x) :
    ∫⁻ x in Φ₀, (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)‖₊ : ℝ≥0∞) ^ 2 ∂(μ K)
      ≤ ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
  set C : ℝ≥0∞ := ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) with hC
  by_cases hCtop : C = ⊤
  · rw [hCtop]; exact le_top

  have hpt : ∀ x, Filter.Tendsto (fun m => (‖avgSum κ f m x‖₊ : ℝ≥0∞) ^ 2) Filter.atTop
      (nhds ((‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)‖₊ : ℝ≥0∞) ^ 2)) := fun x =>
    ((ENNReal.continuous_pow 2).tendsto _).comp (ENNReal.tendsto_coe.2 (tendsto_avgSum hκc hf x).nnnorm)

  have hfatou : ∫⁻ x in Φ₀, (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) ≤
      Filter.liminf (fun m => ∫⁻ x in Φ₀, (‖avgSum κ f m x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K)) Filter.atTop := by
    have e : (fun x => (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)‖₊ : ℝ≥0∞) ^ 2) =
        fun x => Filter.liminf (fun m => (‖avgSum κ f m x‖₊ : ℝ≥0∞) ^ 2) Filter.atTop :=
      funext fun x => ((hpt x).liminf_eq).symm
    rw [e]
    exact lintegral_liminf_le fun m =>
      ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp (continuous_nnnorm.comp (continuous_avgSum κ hf m)))).measurable
  refine hfatou.trans ?_

  have hbound : ∀ m, ∫⁻ x in Φ₀, (‖avgSum κ f m x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) ≤
      ENNReal.ofReal ((∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) ^ 2) * C := fun m =>
    lintegral_avgSum_le α β Φ₀ hΦ₀s hΦ₀ hκ0 hf hfinv m
  have hlim : Filter.Tendsto (fun m => ENNReal.ofReal ((∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) ^ 2) * C)
      Filter.atTop (nhds C) := by
    have h1 : Filter.Tendsto (fun m => ENNReal.ofReal ((∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) ^ 2))
        Filter.atTop (nhds 1) := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.tendsto_ofReal ?_
      have := (tendsto_sum_weights hκc hκ1).pow 2
      rwa [one_pow] at this
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hCtop)
    rwa [one_mul] at this
  calc Filter.liminf (fun m => ∫⁻ x in Φ₀, (‖avgSum κ f m x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K)) Filter.atTop
      ≤ Filter.liminf (fun m => ENNReal.ofReal ((∑ i, (μK K (partE (K := K) m i)).toReal * κ (partC (K := K) m i)) ^ 2) * C) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
    _ = C := hlim.liminf_eq

end Assembly

end Ws23.JensenMass
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain.Ws23 P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain.Ws23.JensenMass"
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain.Ws23"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain.Ws23 P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain.Ws23.JensenMass"

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(maximalCompactAtHaar K ∅) = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfinv : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * x) = f x) :
    ∫⁻ x in Φ₀, (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  Ws23.JensenMass.main α β Φ₀ hΦ₀ hΦ₀s κ hκc hκ0 hκ1 f hf hfinv

end S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain (solution)
