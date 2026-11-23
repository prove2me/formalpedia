-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:28.138019+00:00
-- url     : https://prove2.me/theorems/a4a4ae59-50a5-4a5b-80f8-3ec36609389b
-- title:
--   Is Hilbert Schmidt Of Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Is Hilbert Schmidt Of Finite Dimensional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
namespace GlobalTheory.OpTrace
section Hilbert
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}
variable (H) in

def stdIndex : Set H := (exists_hilbertBasis ℂ H).choose
variable (H) in

def stdBasis : HilbertBasis (stdIndex H) ℂ H := (exists_hilbertBasis ℂ H).choose_spec.choose
def IsHilbertSchmidt (T : H →L[ℂ] K) : Prop :=
  Summable fun i => ‖T (stdBasis H i)‖ ^ 2
def hsNormSq (T : H →L[ℂ] K) : ℝ := ∑' i, ‖T (stdBasis H i)‖ ^ 2
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (n : ℕ) (B C : Fin n → (H →L[ℂ] H)),
    (∀ i, IsHilbertSchmidt (B i)) ∧ (∀ i, IsHilbertSchmidt (C i)) ∧ T = ∑ i, B i ∘L C i
def trace (T : H →L[ℂ] H) : ℂ := ∑' i, ⟪stdBasis H i, T (stdBasis H i)⟫_ℂ
def HasTrace (T : H →L[ℂ] H) (c : ℂ) : Prop := IsTraceClass T ∧ trace T = c
omit [CompleteSpace H] in

theorem hasSum_norm_inner_sq (e : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖⟪e i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (e.repr x)
  simpa [e.repr_apply_apply] using h
omit [CompleteSpace H] [CompleteSpace K] in

theorem summable_matrix (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K) {T : H →L[ℂ] K}
    (h : Summable fun i => ‖T (e i)‖ ^ 2) :
    Summable fun p : ι × κ => ‖⟪f p.2, T (e p.1)⟫_ℂ‖ ^ 2 := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  refine ⟨fun i => (hasSum_norm_inner_sq f (T (e i))).summable, ?_⟩
  simpa only [(hasSum_norm_inner_sq f _).tsum_eq] using h
theorem hasSum_adjoint (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K) {T : H →L[ℂ] K} {s : ℝ}
    (h : HasSum (fun i => ‖T (e i)‖ ^ 2) s) : HasSum (fun j => ‖adjoint T (f j)‖ ^ 2) s := by
  have hF := (summable_matrix e f h.summable).hasSum
  have hs := h.unique (hF.prod_fiberwise fun i => hasSum_norm_inner_sq f (T (e i)))
  rw [← hs, ← (Equiv.prodComm κ ι).hasSum_iff] at hF
  refine hF.prod_fiberwise fun j => ?_
  have := hasSum_norm_inner_sq e (adjoint T (f j))
  simp only [adjoint_inner_right] at this
  simpa [Function.comp_def, norm_inner_symm (T _)] using this
theorem hasSum_basis (e : HilbertBasis ι ℂ H) (e' : HilbertBasis κ ℂ H) {T : H →L[ℂ] K} {s : ℝ}
    (h : HasSum (fun i => ‖T (e i)‖ ^ 2) s) : HasSum (fun j => ‖T (e' j)‖ ^ 2) s := by
  simpa using hasSum_adjoint (stdBasis K) e' (hasSum_adjoint e (stdBasis K) h)
theorem isHilbertSchmidt_iff (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] K} :
    IsHilbertSchmidt T ↔ Summable fun i => ‖T (e i)‖ ^ 2 :=
  ⟨fun h => (hasSum_basis _ e h.hasSum).summable, fun h => (hasSum_basis e _ h.hasSum).summable⟩
theorem IsHilbertSchmidt.hasSum {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ‖T (e i)‖ ^ 2) (hsNormSq T) :=
  hasSum_basis _ e (Summable.hasSum h)
theorem IsHilbertSchmidt.adjoint {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) :
    IsHilbertSchmidt (adjoint T) :=
  (hasSum_adjoint _ _ (Summable.hasSum h)).summable
omit [CompleteSpace K] [CompleteSpace L] in

theorem IsHilbertSchmidt.of_norm_le {T : H →L[ℂ] K} {S : H →L[ℂ] L} (h : IsHilbertSchmidt T)
    (c : ℝ) (hS : ∀ x, ‖S x‖ ≤ c * ‖T x‖) : IsHilbertSchmidt S := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_) (Summable.mul_left (c ^ 2) h)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hS _) 2
omit [CompleteSpace K] [CompleteSpace L] in

theorem IsHilbertSchmidt.comp_left {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (A : K →L[ℂ] L) :
    IsHilbertSchmidt (A ∘L T) :=
  h.of_norm_le ‖A‖ fun x => A.le_opNorm _
theorem IsHilbertSchmidt.comp_right {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (A : L →L[ℂ] H) :
    IsHilbertSchmidt (T ∘L A) := by
  simpa using (h.adjoint.comp_left (ContinuousLinearMap.adjoint A)).adjoint
omit [CompleteSpace K] in

theorem IsHilbertSchmidt.add {S T : H →L[ℂ] K} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
    ((Summable.add hS hT).mul_left 2)
  have h1 := norm_add_le (S (stdBasis H i)) (T (stdBasis H i))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [add_apply]
  nlinarith [sq_nonneg (‖S (stdBasis H i)‖ - ‖T (stdBasis H i)‖)]
omit [CompleteSpace K] in

theorem isHilbertSchmidt_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] K) :
    IsHilbertSchmidt T := by
  have : Finite (stdIndex H) := (stdBasis H).orthonormal.linearIndependent.finite
  exact Summable.of_finite
theorem exists_hasSum_comp (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K)
    {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    ∃ s : ℂ, HasSum (fun i => ⟪e i, B (C (e i))⟫_ℂ) s ∧ HasSum (fun j => ⟪f j, C (B (f j))⟫_ℂ) s := by
  have h1 := summable_matrix e f ((isHilbertSchmidt_iff e).1 hC)
  have h2 := (Equiv.prodComm ι κ).summable_iff.2 (summable_matrix f e ((isHilbertSchmidt_iff f).1 hB))
  have hF : Summable fun p : ι × κ => ⟪e p.1, B (f p.2)⟫_ℂ * ⟪f p.2, C (e p.1)⟫_ℂ := by
    refine Summable.of_norm_bounded (h1.add h2) fun p => ?_
    simp only [Function.comp_def, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, norm_mul]
    nlinarith [sq_nonneg (‖⟪e p.1, B (f p.2)⟫_ℂ‖ - ‖⟪f p.2, C (e p.1)⟫_ℂ‖),
      mul_nonneg (norm_nonneg ⟪e p.1, B (f p.2)⟫_ℂ) (norm_nonneg ⟪f p.2, C (e p.1)⟫_ℂ)]
  refine ⟨_, hF.hasSum.prod_fiberwise fun i => ?_,
    ((Equiv.prodComm κ ι).hasSum_iff.2 hF.hasSum).prod_fiberwise fun j => ?_⟩
  · simpa only [adjoint_inner_left] using f.hasSum_inner_mul_inner (adjoint B (e i)) (C (e i))
  · have := e.hasSum_inner_mul_inner (adjoint C (f j)) (B (f j))
    simp only [adjoint_inner_left] at this
    simpa [Function.comp_def, mul_comm] using this
theorem hasSum_trace_comp (e : HilbertBasis ι ℂ H)
    {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    HasSum (fun i => ⟪e i, (B ∘L C) (e i)⟫_ℂ) (trace (B ∘L C)) := by
  obtain ⟨s, h1, h2⟩ := exists_hasSum_comp e (stdBasis K) hB hC
  obtain ⟨t, h3, h4⟩ := exists_hasSum_comp (stdBasis H) (stdBasis K) hB hC
  have : trace (B ∘L C) = s := h3.tsum_eq.trans (h4.unique h2)
  rw [this]; exact h1
theorem IsTraceClass.hasSum_trace {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪e i, T (e i)⟫_ℂ) (trace T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have key : ∀ {κ : Type _} (f : HilbertBasis κ ℂ H),
      HasSum (fun i => ⟪f i, (∑ k, B k ∘L C k) (f i)⟫_ℂ) (∑ k, trace (B k ∘L C k)) := fun f => by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun k (_ : k ∈ Finset.univ) => hasSum_trace_comp f (hB k) (hC k)
  have h2 : HasSum (fun i => ⟪e i, (∑ k, B k ∘L C k) (e i)⟫_ℂ) (∑ k, trace (B k ∘L C k)) := by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun k (_ : k ∈ Finset.univ) => hasSum_trace_comp e (hB k) (hC k)
  rw [show trace (∑ k, B k ∘L C k) = _ from (key (stdBasis H)).tsum_eq]
  exact h2
omit [CompleteSpace L] in

theorem exists_comp_eq_of_norm_le {C : H →L[ℂ] K} {A : H →L[ℂ] L} (h : ∀ x, ‖C x‖ ≤ ‖A x‖)
    [CompleteSpace L] : ∃ U : L →L[ℂ] K, U ∘L A = C := by
  let M : Submodule ℂ L := (LinearMap.range (A : H →ₗ[ℂ] L)).topologicalClosure
  have hM : ∀ x, A x ∈ M := fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩
  let a : H →ₗ[ℂ] M := (A : H →ₗ[ℂ] L).codRestrict M hM
  have hd : DenseRange a := by
    rw [DenseRange, Subtype.dense_iff]
    intro y hy
    refine closure_mono ?_ (show y ∈ closure (LinearMap.range (A : H →ₗ[ℂ] L) : Set L) from hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨a x, ⟨x, rfl⟩, rfl⟩
  refine ⟨(C : H →ₗ[ℂ] K).extendOfNorm a ∘L M.orthogonalProjection, ?_⟩
  ext x
  have h1 : M.orthogonalProjection (A x) = a x :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (a x)
  rw [comp_apply, comp_apply, h1]
  exact LinearMap.extendOfNorm_eq hd ⟨1, fun y => by simpa [a] using h y⟩ x
theorem norm_sqrt_apply (C : H →L[ℂ] K) (x : H) :
    ‖(CFC.sqrt (adjoint C ∘L C) : H →L[ℂ] H) x‖ = ‖C x‖ := by
  have hp : (0 : H →L[ℂ] H) ≤ adjoint C ∘L C :=
    (nonneg_iff_isPositive _).2 (isPositive_adjoint_comp_self C)
  set A : H →L[ℂ] H := CFC.sqrt (adjoint C ∘L C)
  have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have h2 : A * A = adjoint C ∘L C := CFC.sqrt_mul_sqrt_self _ hp
  have h3 : ⟪A x, A x⟫_ℂ = ⟪C x, C x⟫_ℂ := by
    rw [← adjoint_inner_right, hA.adjoint_eq, ← adjoint_inner_right C]
    exact congrArg (fun S : H →L[ℂ] H => ⟪x, S x⟫_ℂ) h2
  rw [@norm_eq_sqrt_re_inner ℂ, h3, ← @norm_eq_sqrt_re_inner ℂ]
theorem IsHilbertSchmidt.isTraceClass_comp {B : K →L[ℂ] H} {C : H →L[ℂ] K}
    (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) : IsTraceClass (B ∘L C) := by
  obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (norm_sqrt_apply C x).ge
  refine ⟨1, fun _ => B ∘L U, fun _ => CFC.sqrt (ContinuousLinearMap.adjoint C ∘L C),
    fun _ => hB.comp_right U,
    fun _ => hC.of_norm_le 1 fun x => by rw [norm_sqrt_apply, one_mul], ?_⟩
  rw [Fin.sum_univ_one, comp_assoc, hU]
theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsTraceClass (adjoint T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  exact ⟨n, fun i => ContinuousLinearMap.adjoint (C i), fun i => ContinuousLinearMap.adjoint (B i),
    fun i => (hC i).adjoint, fun i => (hB i).adjoint, by simp [map_sum]⟩
@[simp] theorem trace_zero : trace (0 : H →L[ℂ] H) = 0 := by simp [trace]
theorem trace_smul (c : ℂ) (T : H →L[ℂ] H) : trace (c • T) = c * trace T := by
  simp [trace, inner_smul_right, tsum_mul_left]
theorem isTraceClass_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    IsTraceClass T := by
  simpa using (isHilbertSchmidt_of_finiteDimensional T).isTraceClass_comp
    (isHilbertSchmidt_of_finiteDimensional (ContinuousLinearMap.id ℂ H))
theorem trace_eq_linearMap_trace [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    trace T = LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  let b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b,
    ← ((isTraceClass_of_finiteDimensional T).hasSum_trace b.toHilbertBasis).tsum_eq, tsum_fintype]
  simp
example (n : ℕ) : HasTrace (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) n :=
  ⟨isTraceClass_of_finiteDimensional _, by simp [trace_eq_linearMap_trace]⟩
example : trace (Complex.I • ContinuousLinearMap.id ℂ ℂ) = Complex.I := by
  simp [trace_smul, trace_eq_linearMap_trace]
end Hilbert
section Unitary
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure IsUnitaryRep (π : G →* (H →L[ℂ] H)) : Prop where

  norm_apply : ∀ g v, ‖π g v‖ = ‖v‖

  continuous_apply : ∀ v, Continuous fun g => π g v
def charRep (χ : G →* Circle) : G →* (ℂ →L[ℂ] ℂ) where
  toFun g := (χ g : ℂ) • ContinuousLinearMap.id ℂ ℂ
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]
variable [MeasurableSpace G]
def IsRepOp (π : G →* (H →L[ℂ] H)) (μ : Measure G) (f : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ v, Integrable (fun g => f g • π g v) μ ∧ T v = ∫ g, f g • π g v ∂μ
open Classical in

def repOp (π : G →* (H →L[ℂ] H)) (μ : Measure G) (f : G → ℂ) : H →L[ℂ] H :=
  if h : ∃ T, IsRepOp π μ f T then h.choose else 0
def repTrace (π : G →* (H →L[ℂ] H)) (μ : Measure G) (f : G → ℂ) : ℂ := trace (repOp π μ f)
variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}
variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
end Unitary
section FiniteRank
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def finRankTrace (T : V →ₗ[ℂ] V) : ℂ :=
  LinearMap.trace ℂ (LinearMap.range T) (T.restrict fun x _ => LinearMap.mem_range_self T x)
end FiniteRank
section LocallyConstant
variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace X]
def lcIntegral (μ : Measure X) (F : X → V) : V := ∑ᶠ w, (μ.real (F ⁻¹' {w}) : ℂ) • w
variable [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
end LocallyConstant
section Smooth
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
def leftStabilizer (f : G → ℂ) : Subgroup G where
  carrier := {k | ∀ g, f (k * g) = f g}
  one_mem' := fun g => by rw [one_mul]
  mul_mem' := fun ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left]
variable [MeasurableSpace G]
open Classical in

def smoothOp (ρ : Representation ℂ G V) (μ : Measure G) (f : G → ℂ) : V →ₗ[ℂ] V :=
  if h : ∃ T : V →ₗ[ℂ] V, ∀ v, T v = lcIntegral μ fun g => f g • ρ g v then h.choose else 0
def smoothTrace (ρ : Representation ℂ G V) (μ : Measure G) (f : G → ℂ) : ℂ :=
  finRankTrace (smoothOp ρ μ f)
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
end Smooth
end GlobalTheory.OpTrace


