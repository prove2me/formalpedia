-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:30:41.673711+00:00
-- url     : https://prove2.me/theorems/6659682c-aea6-48c6-a347-d4b2fcd5689e
-- title:
--   Disintegration
-- statement:
--   Definitions and structural lemmas for Disintegration, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Theorems.Thm_ZhangYeungImport_MeasureTheory_lintegral_eq_zero_of_ae_zero

set_option autoImplicit true
@[expose] public section
@[expose] public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
namespace Kernel
section condKernel
variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]
variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
end condKernel
end Kernel
section condDistrib
variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
variable [Countable T]
variable [Nonempty T]
section Independence
variable {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {W : Ω → V}
end Independence
end condDistrib
end ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
noncomputable def FiniteKernelSupport (κ : Kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0
noncomputable def AEFiniteKernelSupport (κ : Kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.aefiniteKernelSupport
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    (μ : Measure T) :
    AEFiniteKernelSupport κ μ :=
  ae_of_all μ hκ
@[simp] lemma finiteKernelSupport_zero : FiniteKernelSupport (0 : Kernel T S) :=
  fun t ↦ ⟨∅, by simp⟩
@[simp] lemma aefiniteKernelSupport_zero {μ} : AEFiniteKernelSupport (0 : Kernel T S) μ :=
  finiteKernelSupport_zero.aefiniteKernelSupport _
section
variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}
noncomputable
def _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.mk
    {μ} {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    Kernel T S := by
  classical
  exact (fun _ : AEFiniteKernelSupport κ μ =>
    if hS : Nonempty S then
      κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0})
        (by rw [Set.ofPred_exists]; measurability)
        (.const _ <| .dirac hS.some)
    else 0) hκ
@[simp] lemma _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.mk_zero
    {h : AEFiniteKernelSupport (0 : Kernel T S) μ} : h.mk = 0 := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp [AEFiniteKernelSupport.mk]
  ext x
  by_cases hx : x ∈ {t | ∃ A : Finset S, (0 : Kernel T S) t Aᶜ = 0} <;>
    simp [AEFiniteKernelSupport.mk, Kernel.piecewise, hS]
@[simp] lemma _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.mk_eq_zero_of_isEmpty
    [IsEmpty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = 0 := by
  simp [AEFiniteKernelSupport.mk]
open Classical in
lemma _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.mk_eq
    [hS : Nonempty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0})
      (by rw [Set.ofPred_exists]; measurability) (.const _ <| .dirac hS.some) := by
  simp [AEFiniteKernelSupport.mk, hS]
instance _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.isMarkovKernel_mk
    {κ : Kernel T S} [IsMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsMarkovKernel hκ.mk := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨fun x ↦ (IsEmpty.false x).elim⟩
  inhabit T
  have : Nonempty S := (κ default).nonempty_of_neZero
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance
instance _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.isZeroOrMarkovKernel_mk
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsZeroOrMarkovKernel hκ.mk := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp_all
  · infer_instance
instance _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.isSFiniteKernel_mk
    {κ : Kernel T S} [IsSFiniteKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsSFiniteKernel hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [AEFiniteKernelSupport.mk_eq_zero_of_isEmpty]; infer_instance
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance
end
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.map [MeasurableSingletonClass U]
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ) (f : S → U) :
    FiniteKernelSupport (map κ f) := by
  by_cases hf : Measurable f
  · intro t
    rcases hκ t with ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s
      simp only [Finset.coe_image, Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_image, SetLike.mem_coe, not_exists, not_and]
      contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]
lemma _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.map
    [MeasurableSingletonClass U] {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) {f : S → U} :
    AEFiniteKernelSupport (Kernel.map κ f) μ := by
  by_cases hf : Measurable f
  · filter_upwards [hκ] with t ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s
      simp only [Finset.coe_image, Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_image, SetLike.mem_coe, not_exists, not_and]
      contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.comap
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    {f : U → T} (hf : Measurable f) :
    FiniteKernelSupport (comap κ f hf) := by
  intro u
  rcases hκ (f u) with ⟨A, hA⟩
  use A
  rwa [Kernel.comap_apply]
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.fst [MeasurableSingletonClass S]
   {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (fst κ) := by
  rw [fst_eq]
  apply hκ.map
lemma _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.fst
    [MeasurableSingletonClass S] {κ : Kernel T (S × U)} {μ :
  Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (fst κ) μ := by
  rw [fst_eq]
  apply hκ.map
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.snd [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (snd κ) := by
  rw [snd_eq]
  apply hκ.map
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.swapRight
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (swapRight κ) := by
  rw [swapRight_eq]
  apply hκ.map
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ×ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases hη t with ⟨B, hB⟩
  use A ×ˢ B
  rw [Kernel.prod_apply' _ _ _ (by measurability)]
  apply lintegral_eq_zero_of_ae_zero hA _ (by measurability)
  simp_all
lemma _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η] {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    AEFiniteKernelSupport (κ ×ₖ η) μ := by
  filter_upwards [hκ, hη] with x ⟨A, hκA⟩ ⟨B, hηB⟩
  use A ×ˢ B
  rw [Finset.coe_product, Set.compl_prod_eq_union, prod_apply, measure_union_null_iff,
    Measure.prod_prod, Measure.prod_prod, hκA, hηB, zero_mul, mul_zero, and_self]
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.prodMkRight
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkRight U κ) :=
  hκ.comap _
lemma _root_.ProbabilityTheory.Kernel.FiniteKernelSupport.prodMkLeft
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkLeft U κ) :=
  hκ.comap _
end ProbabilityTheory.Kernel


