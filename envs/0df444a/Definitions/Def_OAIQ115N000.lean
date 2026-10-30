-- Prove2me | Definitions.Def_OAIQ115N000
-- name    : OAIQ115N000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:21:47.260566+00:00
-- url     : https://prove2.me/theorems/f7a7d969-3902-4bb6-87b1-88e0277c94e3
-- title:
--   Definitions bundle OAIQ115N000 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 29 definitions, 2 inductive types or structures, 4 instances and 33 theorems. The definitions and types are `OAI.NaimarkZFC.AtomicFockSpace`, `OAI.NaimarkZFC.AtomicLetters`, `OAI.NaimarkZFC.AtomicTraceData`, `OAI.NaimarkZFC.CenteredColumn`, `OAI.NaimarkZFC.CenteredColumnIndex`, `OAI.NaimarkZFC.ColumnIndex`, `OAI.NaimarkZFC.FactorBlockSpace`, `OAI.NaimarkZFC.FockBlockIndex`, `OAI.NaimarkZFC.FockIndex`, `OAI.NaimarkZFC.FockTail`, `OAI.NaimarkZFC.IsTracialPositive`, `OAI.NaimarkZFC.ReducedPath`, `OAI.NaimarkZFC.TraceColumn`, `OAI.NaimarkZFC.centeredRow`, `OAI.NaimarkZFC.columnUnit`, `OAI.NaimarkZFC.columnVacuum`, `OAI.NaimarkZFC.fockBlockEquiv`, `OAI.NaimarkZFC.fockJoin`, `OAI.NaimarkZFC.fockSplit`, `OAI.NaimarkZFC.gnsRight`, `OAI.NaimarkZFC.gnsRightStarAlgHom`, `OAI.NaimarkZFC.hilbertChoiceBasis`, `OAI.NaimarkZFC.hilbertChoiceSet`, `OAI.NaimarkZFC.projectionRow`, `OAI.NaimarkZFC.restrictRepresentation`, `OAI.NaimarkZFC.rightMulMapPreGNS`, `OAI.NaimarkZFC.traceColumnRepresentation`, `OAI.NaimarkZFC.traceVacuum`, `OAI.NaimarkZFC.tracialColumnBasis`, `OAI.NaimarkZFC.vacuumRowBasis`, `OAI.NaimarkZFC.vacuumRowFamily`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N004`, `OAIQ115N005` and `OAIQ115N006`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ115_Naimark.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def IsTracialPositive (τ : A →ₚ[ℂ] ℂ) : Prop :=
  ∀ a b, τ (a * b) = τ (b * a)

theorem preGNS_norm_star (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_star]
  rw [hτ a (star a)]

def rightMulMapPreGNS (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    τ.PreGNS →L[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ a ∘ₗ τ.ofPreGNS.toLinearMap).mkContinuous
    ‖a‖ fun x => by
      change ‖τ.toPreGNS (τ.ofPreGNS x * a)‖ ≤ ‖a‖ * ‖x‖
      calc
        _ = ‖τ.toPreGNS (star (τ.ofPreGNS x * a))‖ := (preGNS_norm_star τ hτ _).symm
        _ = ‖τ.leftMulMapPreGNS (star a) (τ.toPreGNS (star (τ.ofPreGNS x)))‖ := by
          simp [star_mul]
        _ ≤ ‖star a‖ * ‖τ.toPreGNS (star (τ.ofPreGNS x))‖ := by
          apply le_trans ((τ.leftMulMapPreGNS (star a)).le_opNorm _)
          gcongr
          exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
        _ = _ := by rw [norm_star, preGNS_norm_star τ hτ, τ.toPreGNS_ofPreGNS]

@[simp] theorem rightMulMapPreGNS_apply (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (a : A) (x : τ.PreGNS) :
    rightMulMapPreGNS τ hτ a x = τ.toPreGNS (τ.ofPreGNS x * a) := rfl

def gnsRight (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) : τ.GNS →L[ℂ] τ.GNS :=
  (rightMulMapPreGNS τ hτ a).completion

@[simp] theorem gnsRight_coe (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a b : A) :
    gnsRight τ hτ a (τ.toPreGNS b : τ.GNS) = (τ.toPreGNS (b * a) : τ.GNS) := by
  simp [gnsRight]

@[simp] theorem gnsLeft_coe (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    τ.gnsStarAlgHom a (τ.toPreGNS b : τ.GNS) = (τ.toPreGNS (a * b) : τ.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.gnsNonUnitalStarAlgHom,
    ContinuousLinearMap.completion_apply_coe, PositiveLinearMap.leftMulMapPreGNS]

theorem gnsLeft_commute_right (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a b : A) :
    Commute (τ.gnsStarAlgHom a) (gnsRight τ hτ b) := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective x
    simp [mul_assoc]

theorem gnsRight_star (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    gnsRight τ hτ (star a) = star (gnsRight τ hτ a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
    obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective y
    simp only [gnsRight_coe, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_mul, star_star]
    rw [mul_assoc, hτ a (star b * c), mul_assoc]

theorem gnsRight_mul (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a b : A) :
    gnsRight τ hτ (a * b) = gnsRight τ hτ b * gnsRight τ hτ a := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective x
    simp [mul_assoc]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsRightStarAlgHom (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) :
    Aᵐᵒᵖ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) where
  toFun a := gnsRight τ hτ a.unop
  map_zero' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
      simp [Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective x
      simp [mul_add, Completion.coe_add]
  map_one' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
      simp
  map_mul' a b := gnsRight_mul τ hτ b.unop a.unop
  commutes' c := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
      simp [Algebra.algebraMap_eq_smul_one, Completion.coe_smul]
  map_star' a := gnsRight_star τ hτ a.unop

@[simp] theorem gnsRightStarAlgHom_apply (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (a : A) : gnsRightStarAlgHom τ hτ (MulOpposite.op a) = gnsRight τ hτ a := rfl

def traceVacuum (τ : A →ₚ[ℂ] ℂ) : τ.GNS := (τ.toPreGNS 1 : τ.GNS)

@[simp] theorem traceVacuum_left (τ : A →ₚ[ℂ] ℂ) (a : A) :
    τ.gnsStarAlgHom a (traceVacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [traceVacuum]

@[simp] theorem traceVacuum_right (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    gnsRight τ hτ a (traceVacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [traceVacuum]

open Filter
open scoped Topology

theorem tendsto_zero_of_dense_contractives {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] {ι β : Type*} (l : Filter ι) (T : ι → H →L[ℂ] H)
    (hT : ∀ i, ‖T i‖ ≤ 1) (v : β → H) (hv : DenseRange v)
    (hlim : ∀ b, Tendsto (fun i => T i (v b)) l (𝓝 0)) (x : H) :
    Tendsto (fun i => T i x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, hb⟩ := hv.exists_dist_lt x (half_pos hε)
  have he := (Metric.tendsto_nhds.mp (hlim b)) (ε/2) (half_pos hε)
  filter_upwards [he] with i hi
  rw [dist_zero_right] at hi ⊢
  have hxb : ‖T i (x-v b)‖ < ε/2 := by
    calc
      _ ≤ ‖T i‖ * ‖x-v b‖ := (T i).le_opNorm _
      _ ≤ 1 * ‖x-v b‖ := mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _)
      _ < ε/2 := by simpa only [one_mul, dist_eq_norm] using hb
  have heq : T i x = T i (x-v b) + T i (v b) := by rw [map_sub]; abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gns_projection_norm (τ : A →ₚ[ℂ] ℂ) (q : A) (hq : IsStarProjection q) :
    ‖(τ.toPreGNS q : τ.GNS)‖ = Real.sqrt (τ q).re := by
  rw [Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, hq.isSelfAdjoint.star_eq,
    hq.isIdempotentElem.eq]

theorem trace_projection_strong_zero (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    {ι : Type*} (l : Filter ι) (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hlim : Tendsto (fun i => (τ (p i)).re) l (𝓝 0)) (x : τ.GNS) :
    Tendsto (fun i => τ.gnsStarAlgHom (p i) x) l (𝓝 0) := by
  have hvac : Tendsto (fun i => (τ.toPreGNS (p i) : τ.GNS)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [gns_projection_norm τ _ (hp _)]
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  apply tendsto_zero_of_dense_contractives l (fun i => τ.gnsStarAlgHom (p i))
    (fun i => (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (p i)).trans ((hp i).norm_le _))
    (fun a : A => (τ.toPreGNS a : τ.GNS))
    (Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _))
    _ x
  intro a
  have h := (gnsRight τ hτ a).continuous.continuousAt.tendsto.comp hvac
  simpa [Function.comp_def] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictRepresentation {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H) [CompleteSpace M]
    (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M) : A →⋆ₐ[ℂ] (M →L[ℂ] M) where
  toFun a := (π a).restrict (hinv a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp
  commutes' c := by
    ext x
    change (π (algebraMap ℂ A c)) (x : H) = c • (x : H)
    exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (π.commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    change inner ℂ (π (star a) (x : H)) (y : H) = inner ℂ (x : H) (π a (y : H))
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] theorem restrictRepresentation_apply {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H) [CompleteSpace M]
    (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M) (a : A) (x : M) :
    (restrictRepresentation π M hinv a x : H) = π a (x : H) := rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsRight_projection (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : A) (hq : IsStarProjection q) : IsStarProjection (gnsRight τ hτ q) := by
  refine ⟨?_, ?_⟩
  · change gnsRight τ hτ q * gnsRight τ hτ q = gnsRight τ hτ q
    rw [← gnsRight_mul, hq.isIdempotentElem.eq]
  · change star (gnsRight τ hτ q) = gnsRight τ hτ q
    rw [← gnsRight_star, hq.isSelfAdjoint.star_eq]

def TraceColumn (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : Submodule ℂ τ.GNS :=
  (gnsRight τ hτ q.1).range

instance traceColumnComplete (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : CompleteSpace (TraceColumn τ hτ q) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (gnsRight_projection τ hτ q.1 q.2).isIdempotentElem).completeSpace_coe

theorem traceColumn_invariant (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) (x : τ.GNS)
    (hx : x ∈ TraceColumn τ hτ q) : τ.gnsStarAlgHom a x ∈ TraceColumn τ hτ q := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨τ.gnsStarAlgHom a y,
    (congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => T y) (gnsLeft_commute_right τ hτ a q.1).eq).symm⟩

def traceColumnRepresentation (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) :
    A →⋆ₐ[ℂ] (TraceColumn τ hτ q →L[ℂ] TraceColumn τ hτ q) :=
  restrictRepresentation τ.gnsStarAlgHom (TraceColumn τ hτ q) (traceColumn_invariant τ hτ q)

def columnVacuum (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : TraceColumn τ hτ q :=
  ⟨(τ.toPreGNS q.1 : τ.GNS), traceVacuum τ, traceVacuum_right τ hτ q.1⟩

@[simp] theorem columnVacuum_norm (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) :
    ‖columnVacuum τ hτ q‖ = Real.sqrt (τ q.1).re :=
  gns_projection_norm τ q.1 q.2

def columnUnit (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : TraceColumn τ hτ q :=
  ((Real.sqrt (τ q.1).re)⁻¹ : ℂ) • columnVacuum τ hτ q

theorem columnUnit_norm (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (ht : 0 < (τ q.1).re) :
    ‖columnUnit τ hτ q‖ = 1 := by
  rw [columnUnit, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    columnVacuum_norm, inv_mul_cancel₀ (Real.sqrt_pos.mpr ht).ne']

@[simp] theorem columnVacuum_action (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) :
    (traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q) : τ.GNS) =
      (τ.toPreGNS (a * q.1) : τ.GNS) := by
  exact gnsLeft_coe τ a q.1

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem finiteAtomSum_projection (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0) (s : Finset V) :
    IsStarProjection (∑ l ∈ s, (e l).1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply (e a).property.add ih
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro b hb
    exact horth a b (fun h => ha (h ▸ hb))

theorem traceAtoms_jointKernel (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (x : τ.GNS) (hx : ∀ l, τ.gnsStarAlgHom (e l).1 x = 0) : x = 0 := by
  classical
  let p : Finset V → A := fun s => 1 - ∑ l ∈ s, (e l).1
  have hp : ∀ s, IsStarProjection (p s) := fun s => (finiteAtomSum_projection e horth s).one_sub
  have hlim : Tendsto (fun s => (τ (p s)).re) atTop (𝓝 0) := by
    simpa only [p, map_sub, map_sum, Complex.sub_re, Complex.re_sum, sub_self] using
      (tendsto_const_nhds (x := (τ 1).re) (f := (atTop : Filter (Finset V)))).sub hmass
  have hstrong := trace_projection_strong_zero τ hτ atTop p hp hlim x
  have he (s : Finset V) : τ.gnsStarAlgHom (p s) x = x := by
    simp only [p, map_sub, map_one, map_sum, sub_apply,
      one_apply_eq_self, sum_apply, hx, Finset.sum_const_zero,
      sub_zero]
  simp only [he] at hstrong
  exact tendsto_nhds_unique tendsto_const_nhds hstrong

theorem columnAtoms_jointKernel (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re) (r : V)
    (x : TraceColumn τ hτ (e r))
    (hx : ∀ l, traceColumnRepresentation τ hτ (e r) (e l).1 x = 0) : x = 0 := by
  apply Subtype.ext
  apply traceAtoms_jointKernel τ hτ e horth hmass (x : τ.GNS)
  intro l
  exact congrArg Subtype.val (hx l)

theorem columnUnit_ownRow (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {a : A // IsStarProjection a}) :
    traceColumnRepresentation τ hτ q q.1 (columnUnit τ hτ q) = columnUnit τ hτ q := by
  rw [columnUnit, map_smul]
  congr 1
  apply Subtype.ext
  rw [columnVacuum_action, q.property.isIdempotentElem.eq]
  rfl

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def centeredRow (M : V → Submodule ℂ H) (ξ : H) (l : V) : Submodule ℂ H :=
  M l ⊓ (ℂ ∙ ξ)ᗮ

instance centeredRowComplete (M : V → Submodule ℂ H) [∀ l, CompleteSpace (M l)]
    (ξ : H) (l : V) : CompleteSpace (centeredRow M ξ l) := by
  have hm : IsClosed (M l : Set H) :=
    (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (M l))).isClosed
  exact (hm.inter (Submodule.isClosed_orthogonal _)).completeSpace_coe

def vacuumRowFamily (M : V → Submodule ℂ H) (ξ : H) {J : V → Type*}
    (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) : Option (Σ l, J l) → H
  | none => ξ
  | some ⟨l,j⟩ => b l j

omit [CompleteSpace H] in
theorem vacuumRowFamily_orthonormal (M : V → Submodule ℂ H) (ξ : H)
    (hξ : ‖ξ‖ = 1) (horth : ∀ l k, l ≠ k → ∀ x ∈ M l, ∀ y ∈ M k, inner ℂ x y = 0)
    {J : V → Type*} (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) :
    Orthonormal ℂ (vacuumRowFamily M ξ b) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro (_ | ⟨l,j⟩)
    · exact hξ
    · exact (b l).orthonormal.1 j
  · rintro (_ | ⟨l,j⟩) (_ | ⟨k,t⟩) hne
    · exact False.elim (hne rfl)
    · exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b k t).property.2)
    · exact (Submodule.mem_orthogonal_singleton_iff_inner_left.mp (b l j).property.2)
    · by_cases hlk : l = k
      · subst k
        have hjt : j ≠ t := fun h => hne (by subst t; rfl)
        exact (b l).orthonormal.2 hjt
      · exact horth l k hlk (b l j) (b l j).property.1 (b k t) (b k t).property.1

omit [CompleteSpace H] in

theorem orthogonal_of_basis_inner_zero (M : Submodule ℂ H) [CompleteSpace M]
    {J : Type*} (b : HilbertBasis J ℂ M) (x : H)
    (hx : ∀ j, inner ℂ (b j : H) x = 0) : x ∈ Mᗮ := by
  have hp : M.orthogonalProjectionOnto x = 0 := by
    apply b.repr.injective
    ext j
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact hx j
  apply (M.mem_orthogonal x).mpr
  intro y hy
  have hi := M.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨y, hy⟩ x
  rw [hp, inner_zero_right] at hi
  exact hi.symm

def vacuumRowBasis (M : V → Submodule ℂ H) [∀ l, CompleteSpace (M l)]
    (ξ : H) (r : V) (hξ : ‖ξ‖ = 1) (hmem : ξ ∈ M r)
    (horth : ∀ l k, l ≠ k → ∀ x ∈ M l, ∀ y ∈ M k, inner ℂ x y = 0)
    (htotal : ∀ x : H, (∀ l, ∀ y ∈ M l, inner ℂ y x = 0) → x = 0)
    {J : V → Type*} (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) :
    HilbertBasis (Option (Σ l, J l)) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (vacuumRowFamily_orthonormal M ξ hξ horth b) (by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    have hf : ∀ j, inner ℂ (vacuumRowFamily M ξ b j) x = 0 := fun j =>
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨j, rfl⟩)
    have hv : inner ℂ ξ x = 0 := hf none
    have hc (l : V) : x ∈ (centeredRow M ξ l)ᗮ :=
      orthogonal_of_basis_inner_zero _ (b l) x (fun j => hf (some ⟨l,j⟩))
    apply htotal x
    intro l y hy
    by_cases hlr : l = r
    · subst l
      have hnorm : inner ℂ ξ ξ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hξ]; norm_num
      have hyc : y - (inner ℂ ξ y) • ξ ∈ centeredRow M ξ r := by
        refine ⟨(M r).sub_mem hy ((M r).smul_mem _ hmem), ?_⟩
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [inner_sub_right,
          inner_smul_right, hnorm, mul_one, sub_self]
      have hh := (Submodule.mem_orthogonal _ _).mp (hc r) _ hyc
      simpa only [inner_sub_left, inner_smul_left, hv, mul_zero, sub_zero] using hh
    · have hyc : y ∈ centeredRow M ξ l := by
        refine ⟨hy, ?_⟩
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        exact horth r l (Ne.symm hlr) ξ hmem y hy
      exact (Submodule.mem_orthogonal _ _).mp (hc l) y hyc)

@[simp] theorem vacuumRowBasis_apply (M : V → Submodule ℂ H) [∀ l, CompleteSpace (M l)]
    (ξ : H) (r : V) (hξ : ‖ξ‖ = 1) (hmem : ξ ∈ M r)
    (horth : ∀ l k, l ≠ k → ∀ x ∈ M l, ∀ y ∈ M k, inner ℂ x y = 0)
    (htotal : ∀ x : H, (∀ l, ∀ y ∈ M l, inner ℂ y x = 0) → x = 0)
    {J : V → Type*} (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) (j) :
    vacuumRowBasis M ξ r hξ hmem horth htotal b j = vacuumRowFamily M ξ b j := by
  simp [vacuumRowBasis]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def projectionRow (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a}) (l : V) : Submodule ℂ H :=
  (π (e l).1).range

instance projectionRowComplete (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a}) (l : V) :
    CompleteSpace (projectionRow π e l) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    ((e l).property.map π).isIdempotentElem).completeSpace_coe

theorem projectionRow_orthogonal (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (l k : V) (hlk : l ≠ k) (x : H) (hx : x ∈ projectionRow π e l)
    (y : H) (hy : y ∈ projectionRow π e k) : inner ℂ x y = 0 := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  have hs : (π (e l).1).adjoint = π (e l).1 := by
    change star (π (e l).1) = π (e l).1
    rw [← map_star, (e l).property.isSelfAdjoint.star_eq]
  change inner ℂ (π (e l).1 u) (π (e k).1 v) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, hs]
  have hm : π (e l).1 (π (e k).1 v) = 0 := by
    change (π (e l).1 * π (e k).1) v = 0
    rw [← map_mul, horth l k hlk, map_zero, zero_apply]
  rw [hm, inner_zero_right]

theorem projectionRow_total (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a})
    (hker : ∀ x : H, (∀ l, π (e l).1 x = 0) → x = 0)
    (x : H) (hx : ∀ l, ∀ y ∈ projectionRow π e l, inner ℂ y x = 0) : x = 0 := by
  apply hker x
  intro l
  have hs : (π (e l).1).adjoint = π (e l).1 := ((e l).property.map π).isSelfAdjoint.star_eq
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← ContinuousLinearMap.adjoint_inner_right, hs]
  have he : π (e l).1 (π (e l).1 x) = π (e l).1 x :=
    congrArg (fun T : H →L[ℂ] H => T x) ((e l).property.map π).isIdempotentElem.eq
  rw [he]
  exact inner_eq_zero_symm.mpr (hx l (π (e l).1 x) ⟨x,rfl⟩)

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertChoiceSet : Set H := (exists_hilbertBasis ℂ H).choose

def hilbertChoiceBasis : HilbertBasis (hilbertChoiceSet H) ℂ H :=
  (exists_hilbertBasis ℂ H).choose_spec.choose

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def CenteredColumn (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a}) (l r : V) :
    Submodule ℂ (TraceColumn τ hτ (e r)) :=
  centeredRow (projectionRow (traceColumnRepresentation τ hτ (e r)) e)
    (columnUnit τ hτ (e r)) l

instance centeredColumnComplete (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a}) (l r : V) :
    CompleteSpace (CenteredColumn τ hτ e l r) := by
  unfold CenteredColumn
  infer_instance

abbrev CenteredColumnIndex (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a}) (l r : V) :=
  hilbertChoiceSet (CenteredColumn τ hτ e l r)

def tracialColumnBasis (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) :
    HilbertBasis (Option (Σ l, CenteredColumnIndex τ hτ e l r)) ℂ (TraceColumn τ hτ (e r)) :=
  vacuumRowBasis (projectionRow (traceColumnRepresentation τ hτ (e r)) e)
    (columnUnit τ hτ (e r)) r (columnUnit_norm τ hτ (e r) (hpos r))
    ⟨columnUnit τ hτ (e r), columnUnit_ownRow τ hτ (e r)⟩
    (projectionRow_orthogonal _ e horth)
    (projectionRow_total _ e (columnAtoms_jointKernel τ hτ e horth hmass r))
    (fun l => hilbertChoiceBasis (CenteredColumn τ hτ e l r))

@[simp] theorem tracialColumnBasis_none (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) :
    tracialColumnBasis τ hτ e horth hmass hpos r none = columnUnit τ hτ (e r) := by
  simp [tracialColumnBasis, vacuumRowBasis, vacuumRowFamily]

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

section
universe u v w

variable {I : Type u} {V : Type v} (L : I → V → V → Type w)

inductive ReducedPath : Option I → V → Type (max u v w)
  | nil (r : V) : ReducedPath none r
  | cons (i : I) (l r : V) (a : L i l r) (j : Option I)
      (tail : ReducedPath j r) (hn : some i ≠ j) : ReducedPath (some i) l

abbrev FockIndex := Σ j : Option I, Σ l : V, ReducedPath L j l

abbrev FockTail (i : I) := {x : FockIndex L // x.1 ≠ some i}

abbrev ColumnIndex (i : I) (r : V) := Option (Σ l : V, L i l r)

abbrev FockBlockIndex (i : I) := Σ t : FockTail L i, ColumnIndex L i t.1.2.1

def fockJoin (i : I) : FockBlockIndex L i → FockIndex L
  | ⟨t, none⟩ => t.1
  | ⟨t, some ⟨l, a⟩⟩ =>
    ⟨some i, l, ReducedPath.cons i l t.1.2.1 a t.1.1 t.1.2.2 (Ne.symm t.2)⟩

def fockSplit [DecidableEq I] (i : I) : FockIndex L → FockBlockIndex L i
  | ⟨none, l, ReducedPath.nil _⟩ => ⟨⟨⟨none, l, .nil l⟩, by simp⟩, none⟩
  | ⟨some k, l, ReducedPath.cons _ _ r a j tail hn⟩ =>
    if hki : k = i then
      hki ▸ ⟨⟨⟨j, r, tail⟩, Ne.symm hn⟩, some ⟨l, a⟩⟩
    else
      ⟨⟨⟨some k, l, .cons k l r a j tail hn⟩, by simpa using hki⟩, none⟩

@[simp] theorem fockJoin_split [DecidableEq I] (i : I) (x : FockIndex L) :
    fockJoin L i (fockSplit L i x) = x := by
  rcases x with ⟨j, l, x⟩
  cases x with
  | nil l => rfl
  | cons k l r a j tail hn =>
    by_cases hki : k = i
    · subst k; simp [fockSplit, fockJoin]
    · simp [fockSplit, hki, fockJoin]

@[simp] theorem fockSplit_join [DecidableEq I] (i : I) (x : FockBlockIndex L i) :
    fockSplit L i (fockJoin L i x) = x := by
  rcases x with ⟨⟨⟨j, r, t⟩, ht⟩, c⟩
  cases c with
  | none =>
    cases t with
    | nil r => rfl
    | cons k l r a j tail hn =>
      have hki : k ≠ i := by simpa using ht
      simp [fockJoin, fockSplit, hki]
  | some c =>
    rcases c with ⟨l, a⟩
    simp [fockJoin, fockSplit]

def fockBlockEquiv [DecidableEq I] (i : I) : FockBlockIndex L i ≃ FockIndex L where
  toFun := fockJoin L i
  invFun := fockSplit L i
  left_inv := fockSplit_join L i
  right_inv := fockJoin_split L i

end

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

abbrev AtomicFockSpace := ℓ²(FockIndex L, ℂ)
abbrev FactorBlockSpace (i : I) :=
  lp (fun t : FockTail L i => ℓ²(ColumnIndex L i t.1.2.1, ℂ)) 2

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {V J : Type*}

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section
open scoped InnerProductSpace lp

structure AtomicTraceData (A V : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  trace : A →ₚ[ℂ] ℂ
  tracial : IsTracialPositive trace
  normalized : trace 1 = 1
  faithful : ∀ a, trace (star a * a) = 0 → a = 0
  atom : V → {e : A // IsStarProjection e}
  orthogonal : ∀ l k, l ≠ k → (atom l).1 * (atom k).1 = 0
  positive : ∀ r, 0 < (trace (atom r).1).re
  mass : HasSum (fun r => (trace (atom r).1).re) (trace 1).re

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

abbrev AtomicLetters (i : I) (l r : V) : Type _ :=
  CenteredColumnIndex (d i).trace (d i).tracial (d i).atom l r

end

open Filter Topology
open scoped lp

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end


