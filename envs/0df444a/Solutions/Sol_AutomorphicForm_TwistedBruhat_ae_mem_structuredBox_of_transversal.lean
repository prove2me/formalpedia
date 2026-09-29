-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.ae_mem_structuredBox_of_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f840cc4a-34b4-5761-bb49-2c696c4b6eca

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_HeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

noncomputable section

namespace R1S83TAE

open Filter Topology AutomorphicForm.TransversalMeasure
open scoped TensorProduct.RightActions NumberField.LiesOver

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel NumberField.Idele.ideleBorel
  M4aHerbrand.ArchSemilocal.extLiesOver

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped instance borelSpace_idele : BorelSpace (AdeleRing (𝓞 L) L)ˣ := NumberField.Idele.borelSpace_ideleBorel L

scoped instance borelSpace_semiLocalUnits (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩

scoped instance borelSpace_archUnits (v : InfinitePlace K) : BorelSpace (∀ w : v.Extension L, w.1.Completion)ˣ := ⟨rfl⟩

theorem continuous_semiLocalIdele (v : HeightOneSpectrum (𝓞 K)) : Continuous (semiLocalIdele K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (Continuous.units_map _ (AutomorphicForm.continuous_semiLocalEval K L v)).comp
    (Continuous.units_map _ continuous_snd)

theorem continuous_archSemiLocalIdele (v : InfinitePlace K) : Continuous (archSemiLocalIdele K L v) :=
  (Continuous.units_map _ (continuous_pi fun w => continuous_apply w.1)).comp
    (Continuous.units_map _ continuous_fst)

theorem continuous_norm_semiLocal (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) := by
  classical
  let b := Module.Free.chooseBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  have h1 : Continuous (Algebra.leftMulMatrix b : L ⊗[K] v.adicCompletion K → Matrix _ _ (v.adicCompletion K)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) =
      fun s => (Algebra.leftMulMatrix b s).det := funext fun s => Algebra.norm_eq_matrix_det b s
  rw [h2]
  exact h1.matrix_det

theorem isOpen_setOf_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen {y : v.adicCompletion K | Valued.v y = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have h := Valued.locally_const (R := v.adicCompletion K) (x := y) (by rw [hy]; exact one_ne_zero)
  rw [hy] at h
  exact h

theorem measurableSet_normOneUnits (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSet (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  have h : (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      (fun u : (L ⊗[K] v.adicCompletion K)ˣ => Algebra.norm (v.adicCompletion K) (u : L ⊗[K] v.adicCompletion K)) ⁻¹'
        {y : v.adicCompletion K | Valued.v y = 1} := by
    ext u
    simp only [SetLike.mem_coe, normOneUnits, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
    rfl
  rw [h]
  exact ((isOpen_setOf_valued_eq_one K v).preimage
    ((continuous_norm_semiLocal K L v).comp Units.continuous_val)).measurableSet

set_option maxSynthPendingDepth 3 in
set_option synthInstance.maxHeartbeats 320000 in
set_option maxHeartbeats 3200000 in

theorem continuous_norm_arch (v : InfinitePlace K) :
    Continuous (Algebra.norm v.Completion : (∀ w : v.Extension L, w.1.Completion) → v.Completion) := by
  classical
  letI : NontriviallyNormedField v.Completion := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => M4aHerbrand.ArchSemilocal.finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion := fun w => Module.Free.of_divisionRing _ _
  haveI : Module.Free v.Completion (∀ w : v.Extension L, w.1.Completion) := Module.Free.pi _ _
  haveI : Module.Finite v.Completion (∀ w : v.Extension L, w.1.Completion) := Module.Finite.pi
  let b := Module.Free.chooseBasis v.Completion (∀ w : v.Extension L, w.1.Completion)
  have h1 : Continuous (Algebra.leftMulMatrix b : (∀ w : v.Extension L, w.1.Completion) → Matrix _ _ v.Completion) :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  have h2 : (Algebra.norm v.Completion : (∀ w : v.Extension L, w.1.Completion) → v.Completion) =
      fun s => (Algebra.leftMulMatrix b s).det := funext fun s => Algebra.norm_eq_matrix_det b s
  rw [h2]
  exact h1.matrix_det

set_option maxSynthPendingDepth 3 in
set_option synthInstance.maxHeartbeats 320000 in
theorem isClosed_archNormOneUnits (v : InfinitePlace K) :
    IsClosed (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ) := by
  have h : (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ) =
      (fun u : (∀ w : v.Extension L, w.1.Completion)ˣ =>
        ‖Algebra.norm v.Completion (u : ∀ w : v.Extension L, w.1.Completion)‖) ⁻¹' {1} := by
    ext u
    simp only [SetLike.mem_coe, archNormOneUnits, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [h]
  exact isClosed_singleton.preimage
    (continuous_norm.comp ((continuous_norm_arch K L v).comp Units.continuous_val))

theorem measurableSet_archNormOneUnits (v : InfinitePlace K) :
    MeasurableSet (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ) :=
  (isClosed_archNormOneUnits K L v).measurableSet

theorem isClosed_integralUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  have hS : IsClosed (AutomorphicForm.semiLocalIntegers K L v) := (AutomorphicForm.isCompact_semiLocalIntegers K L v).isClosed
  have h : (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      (Units.val ⁻¹' AutomorphicForm.semiLocalIntegers K L v) ∩
        ((fun u : (L ⊗[K] v.adicCompletion K)ˣ => ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) ⁻¹'
          AutomorphicForm.semiLocalIntegers K L v) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage]
    show (u : L ⊗[K] v.adicCompletion K) ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range ∧
        ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range ↔ _
    simp only [AlgHom.mem_range, AutomorphicForm.semiLocalIntegers, Set.mem_range]
  rw [h]
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

theorem semiLocalHomeomorph_semiLocalEval (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L)
    (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (AutomorphicForm.semiLocalEval K L v a) w = a w.1 := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a)) w = a w.1
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem val_semiLocalIdele_mem_semiLocalIntegers_iff (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 L) L)ˣ) :
    ((semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), (t : AdeleRing (𝓞 L) L).2 w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  have : AutomorphicForm.semiLocalHomeomorph K L v
      ((semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) w =
      (t : AdeleRing (𝓞 L) L).2 w.1 := semiLocalHomeomorph_semiLocalEval K L v _ w
  rw [this, SetLike.mem_coe]

theorem semiLocalIdele_mem_integralUnits_iff (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 L) L)ˣ) :
    semiLocalIdele K L v t ∈ integralUnits K L v ↔
      ∀ w : v.Extension (𝓞 L), (t : AdeleRing (𝓞 L) L).2 w.1 ∈ w.1.adicCompletionIntegers L ∧
        ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w.1 ∈ w.1.adicCompletionIntegers L := by
  have h0 : semiLocalIdele K L v t ∈ integralUnits K L v ↔
      ((semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          AutomorphicForm.semiLocalIntegers K L v ∧
        (((semiLocalIdele K L v t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          AutomorphicForm.semiLocalIntegers K L v := by
    show ((semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range ∧
        (((semiLocalIdele K L v t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range ↔ _
    simp only [AlgHom.mem_range, AutomorphicForm.semiLocalIntegers, Set.mem_range]
  rw [h0, ← map_inv, val_semiLocalIdele_mem_semiLocalIntegers_iff, val_semiLocalIdele_mem_semiLocalIntegers_iff,
    ← forall_and]

theorem finite_setOf_not_mem_integralUnits (t : (AdeleRing (𝓞 L) L)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | semiLocalIdele K L v t ∉ integralUnits K L v}.Finite := by
  set W : Set (HeightOneSpectrum (𝓞 L)) :=
    {w | (t : AdeleRing (𝓞 L) L).2 w ∉ w.adicCompletionIntegers L} ∪
      {w | ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w ∉ w.adicCompletionIntegers L} with hW
  have hWf : W.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact (Filter.eventually_cofinite.mp ((t : AdeleRing (𝓞 L) L).2).2)
    · exact (Filter.eventually_cofinite.mp (((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2).2)
  refine (hWf.image fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, semiLocalIdele_mem_integralUnits_iff, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  refine ⟨w.1, ?_, w.2⟩
  rcases not_and_or.mp hw with h | h
  · exact Or.inl h
  · exact Or.inr h

def G (Sf : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 L) L)ˣ :=
  {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → semiLocalIdele K L v t ∈ integralUnits K L v}

theorem isClosed_G (Sf : Finset (HeightOneSpectrum (𝓞 K))) : IsClosed (G K L Sf) := by
  have : G K L Sf = ⋂ v ∈ (↑Sf : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
      semiLocalIdele K L v ⁻¹' (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
    ext t
    simp only [G, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe,
      SetLike.mem_coe]
  rw [this]
  exact isClosed_biInter fun v _ => (isClosed_integralUnits K L v).preimage (continuous_semiLocalIdele K L v)

theorem measurableSet_G (Sf : Finset (HeightOneSpectrum (𝓞 K))) : MeasurableSet (G K L Sf) :=
  (isClosed_G K L Sf).measurableSet

theorem measure_eq_zero_of_lintegral_eq_zero {X : Type*} [MeasurableSpace X] (μ : Measure X) (P : Set X)
    (hP : MeasurableSet P) (F : X → ℝ≥0∞) (hF : ∀ t ∈ P, F t = 1) (hint : ∫⁻ t, F t ∂μ = 0) : μ P = 0 := by
  have hle : ∫⁻ t, P.indicator 1 t ∂μ ≤ ∫⁻ t, F t ∂μ := by
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ P
    · rw [Set.indicator_of_mem ht, hF t ht, Pi.one_apply]
    · rw [Set.indicator_of_notMem ht]
      exact zero_le
  rw [lintegral_indicator_one hP, hint] at hle
  exact nonpos_iff_eq_zero.mp hle

section Pieces

variable (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → semiLocalIdele K L v t ∈ integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v))
    (j : Fin n)

include hfac3 in

theorem null_of_factorisation (Sf : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sτ ⊆ Sf)
    (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
    (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞)
    (hf : ∀ v ∈ Sf, Measurable (f v)) (hg : ∀ v, Measurable (g v))
    (P : Set (AdeleRing (𝓞 L) L)ˣ) (hPm : MeasurableSet P)
    (hP : ∀ t ∈ P ∩ G K L Sf,
      (∏ v : InfinitePlace K, g v (archSemiLocalIdele K L v t)) * (∏ v ∈ Sf, f v (semiLocalIdele K L v t)) = 1)
    (hzero : (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v) = 0) :
    τ j (P ∩ G K L Sf) = 0 := by
  have hint := hfac3 j Sf hSf f g hf hg
  rw [hzero] at hint
  refine measure_eq_zero_of_lintegral_eq_zero (τ j) _ (hPm.inter (measurableSet_G K L Sf)) _ (fun t ht => ?_) hint
  have hG : t ∈ {t : (AdeleRing (𝓞 L) L)ˣ |
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → semiLocalIdele K L v t ∈ integralUnits K L v} := ht.2
  rw [hP t ht, Set.indicator_of_mem hG, one_mul]

include harch hfac3 in

theorem null_arch (Sf : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sτ ⊆ Sf) (v₀ : InfinitePlace K) :
    τ j ({t | archSemiLocalIdele K L v₀ t ∉ archNormOneUnits K L v₀} ∩ G K L Sf) = 0 := by
  classical
  have hNm : MeasurableSet (archNormOneUnits K L v₀ : Set (∀ w : v₀.Extension L, w.1.Completion)ˣ) :=
    measurableSet_archNormOneUnits K L v₀
  let g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞ :=
    fun v => if v = v₀ then ((archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ)ᶜ).indicator 1 else 1
  let f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞ := fun _ => 1
  have hg : ∀ v, Measurable (g v) := by
    intro v
    by_cases hv : v = v₀
    · subst hv
      simp only [g, if_true]
      exact measurable_one.indicator (measurableSet_archNormOneUnits K L v).compl
    · simp only [g, if_neg hv]
      exact measurable_const
  have hf : ∀ v ∈ Sf, Measurable (f v) := fun v _ => measurable_const
  have hPm : MeasurableSet {t : (AdeleRing (𝓞 L) L)ˣ | archSemiLocalIdele K L v₀ t ∉ archNormOneUnits K L v₀} :=
    (hNm.compl).preimage (continuous_archSemiLocalIdele K L v₀).measurable
  refine null_of_factorisation K L Sτ n τ τfin τarch hfac3 j Sf hSf f g hf hg _ hPm (fun t ht => ?_) ?_
  · have h1 : (∏ v : InfinitePlace K, g v (archSemiLocalIdele K L v t)) = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      by_cases hv : v = v₀
      · subst hv
        have : archSemiLocalIdele K L v t ∈ (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ)ᶜ := ht.1
        simp only [g, if_true, Set.indicator_of_mem this, Pi.one_apply]
      · simp only [g, if_neg hv, Pi.one_apply]
    have h2 : (∏ v ∈ Sf, f v (semiLocalIdele K L v t)) = 1 := Finset.prod_eq_one fun v _ => rfl
    rw [h1, h2, one_mul]
  · have h0 : ∫⁻ x, g v₀ x ∂(τarch j v₀) = 0 := by
      simp only [g, if_true]
      rw [lintegral_indicator_one hNm.compl]
      obtain ⟨μN, -, hμ⟩ := harch j v₀
      rw [hμ, Measure.map_apply measurable_subtype_coe hNm.compl]
      have : (Subtype.val ⁻¹' (archNormOneUnits K L v₀ : Set (∀ w : v₀.Extension L, w.1.Completion)ˣ)ᶜ :
          Set (archNormOneUnits K L v₀)) = ∅ := by
        ext ⟨x, hx⟩
        simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false,
          not_not]
        exact hx
      rw [this, measure_empty]
    rw [Finset.prod_eq_zero (Finset.mem_univ v₀) h0, zero_mul]

include hbad hfac3 in

theorem null_bad (Sf : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sτ ⊆ Sf) (v₀ : HeightOneSpectrum (𝓞 K))
    (hv₀ : v₀ ∈ Sτ) :
    τ j ({t | (πs j v₀)⁻¹ * semiLocalIdele K L v₀ t ∉ normOneUnits K L v₀} ∩ G K L Sf) = 0 := by
  classical
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), IsTopologicalRing (L ⊗[K] v.adicCompletion K) :=
    fun v => isTopologicalRing_tensor K L (v.adicCompletion K)
  have hEm : ∀ v : HeightOneSpectrum (𝓞 K),
      MeasurableSet {x : (L ⊗[K] v.adicCompletion K)ˣ | (πs j v)⁻¹ * x ∉ normOneUnits K L v} := by
    intro v
    have : {x : (L ⊗[K] v.adicCompletion K)ˣ | (πs j v)⁻¹ * x ∉ normOneUnits K L v} =
        (fun x => (πs j v)⁻¹ * x) ⁻¹' (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [this]
    exact ((measurableSet_normOneUnits K L v).compl).preimage (continuous_const.mul continuous_id).measurable
  let f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞ :=
    fun v => if v = v₀ then {x : (L ⊗[K] v.adicCompletion K)ˣ | (πs j v)⁻¹ * x ∉ normOneUnits K L v}.indicator 1
      else 1
  let g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞ := fun _ => 1
  have hf : ∀ v ∈ Sf, Measurable (f v) := by
    intro v _
    by_cases hv : v = v₀
    · subst hv
      simp only [f, if_true]
      exact measurable_one.indicator (hEm v)
    · simp only [f, if_neg hv]
      exact measurable_const
  have hg : ∀ v, Measurable (g v) := fun v => measurable_const
  have hPm : MeasurableSet {t : (AdeleRing (𝓞 L) L)ˣ | (πs j v₀)⁻¹ * semiLocalIdele K L v₀ t ∉ normOneUnits K L v₀} :=
    (hEm v₀).preimage (continuous_semiLocalIdele K L v₀).measurable
  refine null_of_factorisation K L Sτ n τ τfin τarch hfac3 j Sf hSf f g hf hg _ hPm (fun t ht => ?_) ?_
  · have h1 : (∏ v : InfinitePlace K, g v (archSemiLocalIdele K L v t)) = 1 := Finset.prod_eq_one fun v _ => rfl
    have h2 : (∏ v ∈ Sf, f v (semiLocalIdele K L v t)) = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      by_cases hv : v = v₀
      · subst hv
        have : semiLocalIdele K L v t ∈ {x : (L ⊗[K] v.adicCompletion K)ˣ | (πs j v)⁻¹ * x ∉ normOneUnits K L v} :=
          ht.1
        simp only [f, if_true, Set.indicator_of_mem this, Pi.one_apply]
      · simp only [f, if_neg hv, Pi.one_apply]
    rw [h1, h2, one_mul]
  · have h0 : ∫⁻ x, f v₀ x ∂(τfin j v₀) = 0 := by
      simp only [f, if_true]
      rw [lintegral_indicator_one (hEm v₀)]
      obtain ⟨μN, -, hμ⟩ := hbad j v₀ hv₀
      have hmul : Measurable fun x : (L ⊗[K] v₀.adicCompletion K)ˣ => πs j v₀ * x :=
        (continuous_const.mul continuous_id).measurable
      have hpre : MeasurableSet ((fun x : (L ⊗[K] v₀.adicCompletion K)ˣ => πs j v₀ * x) ⁻¹'
          {x : (L ⊗[K] v₀.adicCompletion K)ˣ | (πs j v₀)⁻¹ * x ∉ normOneUnits K L v₀}) := (hEm v₀).preimage hmul
      rw [hμ, Measure.map_apply hmul (hEm v₀), Measure.map_apply measurable_subtype_coe hpre]
      have : (Subtype.val ⁻¹' ((fun x : (L ⊗[K] v₀.adicCompletion K)ˣ => πs j v₀ * x) ⁻¹'
          {x : (L ⊗[K] v₀.adicCompletion K)ˣ | (πs j v₀)⁻¹ * x ∉ normOneUnits K L v₀}) :
            Set (normOneUnits K L v₀)) = ∅ := by
        ext ⟨x, hx⟩
        simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel_left, Set.mem_empty_iff_false, iff_false,
          not_not]
        exact hx
      rw [this, measure_empty]
    rw [Finset.prod_eq_zero (hSf hv₀) h0, mul_zero]

include hgood' hfac3 in

theorem null_good (Sf : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sτ ⊆ Sf) (v₀ : HeightOneSpectrum (𝓞 K))
    (hv₀ : v₀ ∈ Sf) (hv₀' : v₀ ∉ Sτ) :
    τ j ({t | semiLocalIdele K L v₀ t ∉ integralUnits K L v₀} ∩ G K L Sf) = 0 := by
  classical
  have hUm : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSet (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) :=
    fun v => (isClosed_integralUnits K L v).measurableSet
  let f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞ :=
    fun v => if v = v₀ then ((integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ).indicator 1 else 1
  let g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞ := fun _ => 1
  have hf : ∀ v ∈ Sf, Measurable (f v) := by
    intro v _
    by_cases hv : v = v₀
    · subst hv
      simp only [f, if_true]
      exact measurable_one.indicator (hUm v).compl
    · simp only [f, if_neg hv]
      exact measurable_const
  have hg : ∀ v, Measurable (g v) := fun v => measurable_const
  have hPm : MeasurableSet {t : (AdeleRing (𝓞 L) L)ˣ | semiLocalIdele K L v₀ t ∉ integralUnits K L v₀} :=
    ((hUm v₀).compl).preimage (continuous_semiLocalIdele K L v₀).measurable
  refine null_of_factorisation K L Sτ n τ τfin τarch hfac3 j Sf hSf f g hf hg _ hPm (fun t ht => ?_) ?_
  · have h1 : (∏ v : InfinitePlace K, g v (archSemiLocalIdele K L v t)) = 1 := Finset.prod_eq_one fun v _ => rfl
    have h2 : (∏ v ∈ Sf, f v (semiLocalIdele K L v t)) = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      by_cases hv : v = v₀
      · subst hv
        have : semiLocalIdele K L v t ∈ (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ := ht.1
        simp only [f, if_true, Set.indicator_of_mem this, Pi.one_apply]
      · simp only [f, if_neg hv, Pi.one_apply]
    rw [h1, h2, one_mul]
  · have h0 : ∫⁻ x, f v₀ x ∂(τfin j v₀) = 0 := by
      simp only [f, if_true]
      rw [lintegral_indicator_one (hUm v₀).compl]
      exact (hgood' j v₀ hv₀').1
    rw [Finset.prod_eq_zero hv₀ h0, mul_zero]

include hgood' hbad harch hfac3 in

theorem measure_compl_box_eq_zero :
    τ j {t : (AdeleRing (𝓞 L) L)ˣ | ¬ ((∀ v : InfinitePlace K, archSemiLocalIdele K L v t ∈ archNormOneUnits K L v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ → (πs j v)⁻¹ * semiLocalIdele K L v t ∈ normOneUnits K L v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ → semiLocalIdele K L v t ∈ integralUnits K L v))} = 0 := by
  classical

  let Z : Finset (HeightOneSpectrum (𝓞 K)) → Set (AdeleRing (𝓞 L) L)ˣ := fun Sf =>
    ((⋃ v : InfinitePlace K, {t | archSemiLocalIdele K L v t ∉ archNormOneUnits K L v} ∩ G K L Sf) ∪
      (⋃ v ∈ Sτ, {t | (πs j v)⁻¹ * semiLocalIdele K L v t ∉ normOneUnits K L v} ∩ G K L Sf)) ∪
      (⋃ v ∈ Sf, ⋃ (_ : v ∉ Sτ), {t | semiLocalIdele K L v t ∉ integralUnits K L v} ∩ G K L Sf)
  have hZ : ∀ Sf, Sτ ⊆ Sf → τ j (Z Sf) = 0 := by
    intro Sf hSf
    refine measure_union_null (measure_union_null ?_ ?_) ?_
    · exact measure_iUnion_null fun v => null_arch K L Sτ n τ τfin τarch harch hfac3 j Sf hSf v
    · exact measure_biUnion_null_iff (Sτ.countable_toSet) |>.mpr fun v hv =>
        null_bad K L Sτ n τ τfin τarch πs hbad hfac3 j Sf hSf v hv
    · refine measure_biUnion_null_iff (Sf.countable_toSet) |>.mpr fun v hv => ?_
      exact measure_iUnion_null fun hv' => null_good K L Sτ n τ τfin τarch hgood' hfac3 j Sf hSf v hv hv'

  refine measure_mono_null (t := ⋃ Sf : Finset (HeightOneSpectrum (𝓞 K)), ⋃ (_ : Sτ ⊆ Sf), Z Sf) ?_ ?_
  · intro t ht
    simp only [Set.mem_setOf_eq] at ht
    have hfin := finite_setOf_not_mem_integralUnits K L t
    set Sf : Finset (HeightOneSpectrum (𝓞 K)) := Sτ ∪ hfin.toFinset with hSf_def
    have hSf : Sτ ⊆ Sf := Finset.subset_union_left
    have hG : t ∈ G K L Sf := by
      intro v hv
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h))
    refine Set.mem_iUnion.mpr ⟨Sf, Set.mem_iUnion.mpr ⟨hSf, ?_⟩⟩
    by_cases h1 : ∀ v : InfinitePlace K, archSemiLocalIdele K L v t ∈ archNormOneUnits K L v
    · by_cases h2 : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ → (πs j v)⁻¹ * semiLocalIdele K L v t ∈ normOneUnits K L v
      · have h3 : ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ → semiLocalIdele K L v t ∈ integralUnits K L v :=
          fun h3 => ht ⟨h1, h2, h3⟩
        push Not at h3
        obtain ⟨v, hv, hv'⟩ := h3
        have hvSf : v ∈ Sf := Finset.mem_union_right _ (hfin.mem_toFinset.mpr hv')
        refine Or.inr (Set.mem_iUnion₂.mpr ⟨v, hvSf, Set.mem_iUnion.mpr ⟨hv, hv', hG⟩⟩)
      · push Not at h2
        obtain ⟨v, hv, hv'⟩ := h2
        exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨v, hv, hv', hG⟩))
    · push Not at h1
      obtain ⟨v, hv⟩ := h1
      exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨v, hv, hG⟩))
  · exact measure_iUnion_null fun Sf => measure_iUnion_null fun hSf => hZ Sf hSf

end Pieces

end R1S83TAE
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal.R1S83TAE"

end
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal.R1S83TAE"

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hgood : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v))
    (j : Fin n) :
    ∀ᵐ t ∂(τ j),
      (∀ v : InfinitePlace K,
          AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.archNormOneUnits K L v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ →
          (πs j v)⁻¹ * AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
            AutomorphicForm.TransversalMeasure.normOneUnits K L v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ →
          AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v) := by
  rw [MeasureTheory.ae_iff]
  exact R1S83TAE.measure_compl_box_eq_zero K L Sτ n τ τfin τarch πs hgood' hbad harch hfac3 j

end S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal (solution)
