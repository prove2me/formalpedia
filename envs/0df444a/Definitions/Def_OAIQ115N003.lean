-- Prove2me | Definitions.Def_OAIQ115N003
-- name    : OAIQ115N003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:22:18.595676+00:00
-- url     : https://prove2.me/theorems/455530b1-c973-4ca5-a820-681347cb5496
-- title:
--   Definitions bundle OAIQ115N003 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 209 declarations of OpenAI's Lean: 34 definitions, 1 inductive type or structure, 13 instances and 161 theorems. The definitions and types are `OAI.NaimarkZFC.ChronologicalStage.instDecidableEqOrdinal`, `OAI.NaimarkZFC.ConstructionIndex`, `OAI.NaimarkZFC.KOS.Close`, `OAI.NaimarkZFC.KOS.ProjectionChain`, `OAI.NaimarkZFC.KOS.ProjectionChain.average`, `OAI.NaimarkZFC.KOS.ProjectionChain.block`, `OAI.NaimarkZFC.KOS.basisColumn`, `OAI.NaimarkZFC.KOS.columnMap`, `OAI.NaimarkZFC.KOS.compactPreimageIdeal`, `OAI.NaimarkZFC.KOS.gramResidual`, `OAI.NaimarkZFC.KOS.krylovChain`, `OAI.NaimarkZFC.KOS.krylovSet`, `OAI.NaimarkZFC.KOS.krylovSpace`, `OAI.NaimarkZFC.KOS.matrixOperator`, `OAI.NaimarkZFC.KOS.matrixRow`, `OAI.NaimarkZFC.KOS.matrixScalar`, `OAI.NaimarkZFC.KOS.orbitTests`, `OAI.NaimarkZFC.KOS.projectionCutoff`, `OAI.NaimarkZFC.KOS.rowAverage`, `OAI.NaimarkZFC.KOS.rowDefectTest`, `OAI.NaimarkZFC.KOS.rowFrameTests`, `OAI.NaimarkZFC.KOS.scalarGram`, `OAI.NaimarkZFC.KOS.tests`, `OAI.NaimarkZFC.KOS.upperCutoff`, `OAI.NaimarkZFC.autLimitEquiv`, `OAI.NaimarkZFC.autLimitHom`, `OAI.NaimarkZFC.autPointwiseLimit`, `OAI.NaimarkZFC.constructionCardinal`, `OAI.NaimarkZFC.dependencyClosure`, `OAI.NaimarkZFC.dependencyStep`, `OAI.NaimarkZFC.fullImageEquiv`, `OAI.NaimarkZFC.fullTopEquiv`, `OAI.NaimarkZFC.instDecidableEqOrdinal_solutions`, `OAI.NaimarkZFC.instDecidableEqOrdinal_solutions_1`, `OAI.NaimarkZFC.ordinalMajorant`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Basic.lean), [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Operators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Operators.lean), [`Naimark_Recursion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Recursion.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ115N006`.
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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem intertwiner_adjoint_comp_commute
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (T : H →L[ℂ] K)
    (hT : ∀ a : A, T.comp (π a) = (ρ a).comp T) (a : A) :
    Commute (T.adjoint.comp T) (π a) := by
  have hstar := congrArg ContinuousLinearMap.adjoint (hT (star a))
  simp only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] at hstar
  change (T.adjoint.comp T).comp (π a) = (π a).comp (T.adjoint.comp T)
  rw [ContinuousLinearMap.comp_assoc, hT, ← ContinuousLinearMap.comp_assoc, ← hstar,
    ContinuousLinearMap.comp_assoc]

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_bounded_selfAdjoint_operator_vector (d w : H)
    (hd : 1 ≤ ‖d‖) (hd' : ‖d‖ ≤ 2) (hw : (⟪d,w⟫_ℂ).im = 0) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ T d = w ∧ ‖T‖ ≤ 12*‖w‖ := by
  let r : ℝ := ‖d‖^2
  let c : ℝ := (⟪d,w⟫_ℂ).re
  have hr : 0 < r := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hd)
  have hr1 : 1 ≤ r := by dsimp [r]; nlinarith
  have hri : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr)
  have hri1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hc : |c| ≤ 2*‖w‖ := (Complex.abs_re_le_norm _).trans
    ((norm_inner_le_norm d w).trans (mul_le_mul_of_nonneg_right hd' (norm_nonneg _)))
  have hcr : |c/r| ≤ 2*‖w‖ := by
    rw [abs_div,abs_of_pos hr,div_eq_mul_inv]
    calc
      |c| *r⁻¹ ≤ |c| *1 := mul_le_mul_of_nonneg_left hri1 (abs_nonneg _)
      _ ≤ 2*‖w‖ := by simpa using hc
  have hdd : ⟪d,d⟫_ℂ = (r:ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; exact (Complex.ofReal_pow ‖d‖ 2).symm
  have hdw : ⟪d,w⟫_ℂ = (c:ℂ) := Complex.ext rfl hw
  have hwd : ⟪w,d⟫_ℂ = (c:ℂ) := by rw [← inner_conj_symm,hdw]; simp
  let T : H →L[ℂ] H := r⁻¹ • (InnerProductSpace.rankOne ℂ w d +
    InnerProductSpace.rankOne ℂ d w - (c/r) • InnerProductSpace.rankOne ℂ d d)
  refine ⟨T,?_,?_,?_⟩
  · change star T = T
    simp only [T,star_smul,star_trivial,star_sub,star_add,
      ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne]
    rw [add_comm]
  · simp only [T,smul_apply,sub_apply,add_apply,InnerProductSpace.rankOne_apply,
      hdd,hwd,Complex.coe_smul,smul_smul,div_mul_cancel₀ c hr.ne',
      add_sub_cancel_right,inv_mul_cancel₀ hr.ne',one_smul]
  · have hwdn : ‖w‖*‖d‖ ≤ 2*‖w‖ := by nlinarith [norm_nonneg w]
    have hdwn : ‖d‖*‖w‖ ≤ 2*‖w‖ := by nlinarith [norm_nonneg w]
    have hcdd : |c/r| *(‖d‖*‖d‖) ≤ 8*‖w‖ := by
      have hddn : ‖d‖*‖d‖ ≤ 4 := by nlinarith [norm_nonneg d]
      calc
        _ ≤ (2*‖w‖)*4 := mul_le_mul hcr hddn (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
        _ = _ := by ring
    calc
      ‖T‖ = r⁻¹ * ‖InnerProductSpace.rankOne ℂ w d +
        InnerProductSpace.rankOne ℂ d w - (c/r) • InnerProductSpace.rankOne ℂ d d‖ := by
          simp only [T,norm_smul,Real.norm_eq_abs,abs_of_nonneg hri]
      _ ≤ r⁻¹ * (‖InnerProductSpace.rankOne ℂ w d‖ +
        ‖InnerProductSpace.rankOne ℂ d w‖ + ‖(c/r) • InnerProductSpace.rankOne ℂ d d‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ r⁻¹ * (12*‖w‖) := by
          gcongr
          simp only [InnerProductSpace.norm_rankOne,norm_smul,Real.norm_eq_abs]
          linarith
      _ ≤ 12*‖w‖ := by nlinarith [norm_nonneg w]

end

open UniformSpace
open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
variable {A ι : Type*} [CStarAlgebra A]

theorem countable_submonoidClosure (s : Set A) (hs : s.Countable) :
    (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  rw [Submonoid.closure_eq_mrange,MonoidHom.coe_mrange]
  exact Set.countable_range _

theorem separable_submonoidClosure (s : Set A) (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (Submonoid.closure s : Set A) := by
  obtain ⟨d,hd,hsd⟩ := hs
  have hm : Submonoid.closure s ≤ (Submonoid.closure d).topologicalClosure := by
    apply Submonoid.closure_le.mpr
    exact hsd.trans (closure_mono (Submonoid.subset_closure))
  exact ((countable_submonoidClosure d hd).isSeparable.closure).mono hm

theorem separable_starAdjoin (s : Set A) (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have hstar : TopologicalSpace.IsSeparable (star s) := by
    simpa only [Set.image_star] using hs.image continuous_star
  have h := (separable_submonoidClosure (s ∪ star s) (hs.union hstar)).span (R := ℂ)
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rwa [StarAlgebra.adjoin_eq_span]

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

section
variable {ι : Type*}

def dependencyStep (I : ι → Set ι) (S : Set ι) : Set ι := S ∪ ⋃ j ∈ S, I j

def dependencyClosure (I : ι → Set ι) (S : Set ι) : Set ι :=
  ⋃ n : ℕ, (dependencyStep I)^[n] S

theorem subset_dependencyClosure (I : ι → Set ι) (S : Set ι) : S ⊆ dependencyClosure I S := by
  intro j hj
  exact Set.mem_iUnion.mpr ⟨0,hj⟩

theorem dependencyStep_countable (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    {S : Set ι} (hS : S.Countable) : (dependencyStep I S).Countable :=
  hS.union (hS.biUnion (fun j _ => hI j))

theorem dependencyClosure_countable (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    {S : Set ι} (hS : S.Countable) : (dependencyClosure I S).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dependencyStep_countable I hI ih

end

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

section

universe u
open Set Cardinal Ordinal

abbrev constructionCardinal : Cardinal.{u} := Order.succ 𝔠

end

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra InnerProductSpace

open Filter Topology
open scoped CStarAlgebra

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
section

theorem isometry_cauchy_on_dense {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : ℕ → X → Y) (hf : ∀ n, Isometry (f n))
    (s : Set X) (hs : Dense s) (hc : ∀ x ∈ s, CauchySeq (fun n => f n x))
    (x : X) : CauchySeq (fun n => f n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp (hs x) (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hc y hy) (ε/3) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have h₁ := (hf m).dist_eq x y
  have h₂ := (hf n).dist_eq y x
  have ht := dist_triangle4 (f m x) (f m y) (f n y) (f n x)
  rw [h₁,h₂,dist_comm y x] at ht
  have hmid := hN m hm n hn
  linarith

variable {A : Type*} [CStarAlgebra A]
  (α : ℕ → A ≃⋆ₐ[ℂ] A)
  (hc : ∀ a, CauchySeq (fun n => α n a))

def autPointwiseLimit (a : A) : A :=
  Classical.choose (cauchySeq_tendsto_of_complete (hc a))

theorem tendsto_autPointwiseLimit (a : A) :
    Tendsto (fun n => α n a) atTop (𝓝 (autPointwiseLimit α hc a)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hc a))

theorem autPointwiseLimit_isometry : Isometry (autPointwiseLimit α hc) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  apply tendsto_nhds_unique ((tendsto_autPointwiseLimit α hc a).dist
    (tendsto_autPointwiseLimit α hc b))
  simpa only [fun n => (StarAlgEquiv.isometry (α n)).dist_eq a b] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => dist a b) atTop (𝓝 (dist a b)))

def autLimitHom : A →⋆ₐ[ℂ] A where
  toFun := autPointwiseLimit α hc
  map_zero' := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc 0)
    (by simpa only [map_zero] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (0:A)) atTop (𝓝 0)))
  map_one' := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc 1)
    (by simpa only [map_one] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (1:A)) atTop (𝓝 1)))
  map_add' a b := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (a+b))
    (by simpa only [map_add] using ((tendsto_autPointwiseLimit α hc a).add (tendsto_autPointwiseLimit α hc b)))
  map_mul' a b := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (a*b))
    (by simpa only [map_mul] using ((tendsto_autPointwiseLimit α hc a).mul (tendsto_autPointwiseLimit α hc b)))
  commutes' z := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (algebraMap ℂ A z))
    (by simpa only [AlgHomClass.commutes] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => algebraMap ℂ A z) atTop (𝓝 (algebraMap ℂ A z))))
  map_star' a := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (star a))
    (by simpa only [map_star] using (tendsto_autPointwiseLimit α hc a).star)

theorem autLimitHom_surjective (hi : ∀ a, CauchySeq (fun n => (α n).symm a)) :
    Function.Surjective (autLimitHom α hc) := by
  intro a
  let b := autPointwiseLimit (fun n => (α n).symm) hi a
  refine ⟨b,?_⟩
  have hleft := (tendsto_autPointwiseLimit α hc b).dist
    (tendsto_const_nhds (x := a))
  have hright := (tendsto_const_nhds (x := b)).dist
    (tendsto_autPointwiseLimit (fun n => (α n).symm) hi a)
  have he (n : ℕ) : dist (α n b) a = dist b ((α n).symm a) := by
    rw [← (StarAlgEquiv.isometry (α n)).dist_eq b ((α n).symm a),(α n).apply_symm_apply]
  have hz : dist (autPointwiseLimit α hc b) a = 0 := by
    have hh := tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall
      (fun n => (he n).symm)))
    simpa only [show autPointwiseLimit (fun n => (α n).symm) hi a = b from rfl,dist_self] using hh
  exact dist_eq_zero.mp hz

def autLimitEquiv (hi : ∀ a, CauchySeq (fun n => (α n).symm a)) : A ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofBijective (autLimitHom α hc)
    ⟨(autPointwiseLimit_isometry α hc).injective,autLimitHom_surjective α hc hi⟩

end

open Filter Topology

section

universe u
open Set Cardinal Ordinal

def ordinalMajorant (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  max (f o) (⨆ x : o.ToType, ordinalMajorant f (x : Ordinal) + 1)
termination_by o
decreasing_by exact x.toOrd.property

end

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open Filter Topology
open scoped InnerProductSpace

open Topology

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace
namespace KOS

def projectionCutoff (t : ℝ) : ℝ := t^2 / (t^2 + (t-1)^2)

lemma projectionCutoff_den_pos (t : ℝ) : 0 < t^2 + (t-1)^2 := by
  nlinarith [sq_nonneg (t-1/2)]

lemma continuous_projectionCutoff : Continuous projectionCutoff := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (projectionCutoff_den_pos t).ne'

lemma projectionCutoff_nonneg (t : ℝ) : 0 ≤ projectionCutoff t :=
  div_nonneg (sq_nonneg _) (projectionCutoff_den_pos t).le

lemma projectionCutoff_le_one (t : ℝ) : projectionCutoff t ≤ 1 := by
  unfold projectionCutoff
  rw [div_le_one (projectionCutoff_den_pos t)]
  nlinarith [sq_nonneg (t-1)]

end KOS

open scoped InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

omit completeSpaceH in
theorem difference_span_coefficients [CompleteSpace H] {ι : Type*} [Fintype ι] (b w : ι → H)
    (hb : Orthonormal ℂ b) (ho : ∀ i j, ⟪b i,w j⟫_ℂ = 0)
    {v : H} (hv : v ∈ Submodule.span ℂ (Set.range fun i => b i-w i)) :
    v = ∑ i, ⟪b i,v⟫_ℂ • (b i-w i) := by
  rw [← Fintype.range_linearCombination ℂ] at hv
  obtain ⟨c,hc⟩ := hv
  change (∑ i, c i • (b i-w i)) = v at hc
  have hi (j : ι) : ⟪b j,v⟫_ℂ = c j := by
    rw [← hc]
    simp only [smul_sub,Finset.sum_sub_distrib,inner_sub_right]
    rw [hb.inner_right_fintype]
    simp only [inner_sum,inner_smul_right,ho,mul_zero,Finset.sum_const_zero,sub_zero]
  calc
    v = ∑ i, c i • (b i-w i) := hc.symm
    _ = _ := by simp only [hi]

omit completeSpaceH in
theorem gram_combination_error [CompleteSpace H] {ι : Type*} [Fintype ι] (x y : ι → H)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ)
    (c d : ι → ℂ) :
    ‖⟪∑ i, c i • x i, ∑ j, d j • x j⟫_ℂ -
      ⟪∑ i, c i • y i, ∑ j, d j • y j⟫_ℂ‖ ≤
      δ * (∑ i, ‖c i‖) * (∑ j, ‖d j‖) := by
  have he : ⟪∑ i, c i • x i, ∑ j, d j • x j⟫_ℂ -
      ⟪∑ i, c i • y i, ∑ j, d j • y j⟫_ℂ =
      ∑ i, ∑ j, (starRingEnd ℂ (c i) * d j) * (⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ) := by
    simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,
      Finset.mul_sum,← Finset.sum_sub_distrib,mul_sub,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, ‖∑ j, (starRingEnd ℂ (c i) * d j) * (⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, δ * ‖c i‖ * ‖d j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_mul,RCLike.norm_conj]
      calc
        _ = ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ * (‖c i‖ * ‖d j‖) := mul_comm _ _
        _ ≤ δ * (‖c i‖ * ‖d j‖) :=
          mul_le_mul (hgram i j) le_rfl (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hδ
        _ = _ := by ring
    _ = _ := by simp only [← Finset.mul_sum,← Finset.sum_mul]

theorem gram_zero_combination_bound {ι : Type*} [Fintype ι] (x y : ι → H)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ)
    (c : ι → ℂ) (hc : ∑ i, c i • x i = 0) :
    ‖∑ i, c i • y i‖ ≤ Real.sqrt δ * (∑ i, ‖c i‖) := by
  have hb := gram_combination_error x y δ hδ hgram c c
  rw [hc,inner_zero_left,zero_sub,norm_neg,inner_self_eq_norm_sq_to_K,
    norm_pow,RCLike.norm_coe_norm] at hb
  have hs : 0 ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hpos : 0 ≤ Real.sqrt δ * ∑ i, ‖c i‖ := mul_nonneg (Real.sqrt_nonneg _) hs
  apply (sq_le_sq₀ (norm_nonneg _) hpos).mp
  rw [mul_pow,Real.sq_sqrt hδ]
  nlinarith only [hb]

omit completeSpaceH in
theorem finite_orthonormal_coordinates [CompleteSpace H] {ι : Type*} [Fintype ι] (x : ι → H) :
    ∃ (m : ℕ) (b : Fin m → H) (c : Fin m → ι → ℂ) (d : ι → Fin m → ℂ),
      Orthonormal ℂ b ∧ (∀ j, ∑ i, c j i • x i = b j) ∧
      (∀ i, ∑ j, d i j • b j = x i) := by
  classical
  let M := Submodule.span ℂ (Set.range x)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let B := stdOrthonormalBasis ℂ M
  let b := fun j => (B j : H)
  have hb : Orthonormal ℂ b := B.orthonormal.comp_linearIsometry M.subtypeₗᵢ
  have hc (j) : ∃ c : ι → ℂ, ∑ i, c i • x i = b j := by
    have hj := (B j).property
    change (b j) ∈ Submodule.span ℂ (Set.range x) at hj
    rw [← Fintype.range_linearCombination ℂ] at hj
    exact hj
  choose c hc using hc
  let d := fun i j => ⟪b j,x i⟫_ℂ
  refine ⟨_,b,c,d,hb,hc,?_⟩
  intro i
  have he := congrArg (fun (v : M) => (v:H))
    (B.sum_repr' ⟨x i,Submodule.subset_span (Set.mem_range_self i)⟩)
  simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_mk,Submodule.coe_inner,d,b] using he

omit completeSpaceH in
theorem gram_cross_zero [CompleteSpace H] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → H) (y : κ → H) (ho : ∀ i j, ⟪x i,y j⟫_ℂ = 0)
    (c : ι → ℂ) (d : κ → ℂ) :
    ⟪∑ i, c i • x i, ∑ j, d j • y j⟫_ℂ = 0 := by
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,ho,mul_zero,
    Finset.sum_const_zero]

def gramResidual {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (c : κ → ι → ℂ) (d : ι → κ → ℂ) (i : ι) : ι → ℂ :=
  Pi.single i 1 - ∑ j, d i j • c j

omit completeSpaceH in
lemma gramResidual_apply [CompleteSpace H] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (x : ι → H) (c : κ → ι → ℂ) (d : ι → κ → ℂ) (i : ι) :
    ∑ l, gramResidual c d i l • x l = x i - ∑ j, d i j • (∑ l, c j l • x l) := by
  change Fintype.linearCombination ℂ x (gramResidual c d i) = _
  rw [gramResidual,map_sub,Fintype.linearCombination_apply_single,one_smul,map_sum]
  simp only [map_smul,Fintype.linearCombination_apply]

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma unitary_commutator_product (v w : unitary A) (b : A) :
    ‖b * ((v:A)*(w:A))-((v:A)*(w:A))*b‖ ≤
      2*‖b‖*‖(v:A)-1‖ + ‖b*(w:A)-(w:A)*b‖ := by
  have he : b * ((v:A)*(w:A))-((v:A)*(w:A))*b =
      (b*(v:A)-(v:A)*b)*(w:A)+(v:A)*(b*(w:A)-(w:A)*b) := by noncomm_ring
  have hv : b*(v:A)-(v:A)*b = b*((v:A)-1)-((v:A)-1)*b := by noncomm_ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,hv]
  have hn := (norm_sub_le (b*((v:A)-1)) (((v:A)-1)*b)).trans
    (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  nlinarith

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

def rowAverage (x : ι → A) (a : A) : A := ∑ i, x i*a*star (x i)

lemma rowAverage_selfAdjoint (x : ι → A) (a : A) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (rowAverage x a) := by
  change star (∑ i, x i*a*star (x i)) = _
  simp only [star_sum,star_mul,star_star,ha.star_eq,mul_assoc,rowAverage]

lemma rowAverage_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (x : ι → A) (a : A) (v : H) :
    π (rowAverage x a) v = ∑ i, π (x i) (π a (π (star (x i)) v)) := by
  simp only [rowAverage,map_sum,sum_apply,map_mul,mul_apply_eq_comp]

lemma rowAverage_small (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (x : ι → A) (a : A) (v : H) (ε : ℝ)
    (he : ∀ i, ‖π a (π (star (x i)) v)‖ ≤ ε) :
    ‖π (rowAverage x a) v‖ ≤ (∑ i, ‖x i‖)*ε := by
  rw [rowAverage_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact ((π (x i)).le_opNorm _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π _) (he i) (norm_nonneg _) (norm_nonneg _))

end KOS

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [fintypeι : Fintype ι]

def rowDefectTest (x : ι → A) : A :=
  star (rowAverage x 1-1)*(rowAverage x 1-1)

def rowFrameTests (x : ι → A) : Finset A := by
  classical
  exact (Finset.univ.image (fun ij : ι × ι => x ij.1*star (x ij.2))) ∪ {rowDefectTest x}

lemma gram_mem_rowFrameTests (x : ι → A) (i j : ι) :
    x i*star (x j) ∈ rowFrameTests x := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)

lemma defect_mem_rowFrameTests (x : ι → A) : rowDefectTest x ∈ rowFrameTests x := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma unitary_commutator_star (u : unitary A) (b : A) :
    ‖b*star (u:A)-star (u:A)*b‖ = ‖b*(u:A)-(u:A)*b‖ := by
  have he : b*star (u:A)-star (u:A)*b =
      -(star (u:A)*(b*(u:A)-(u:A)*b)*star (u:A)) := by
    rw [mul_sub,sub_mul]
    simp only [← mul_assoc,u.property.1,one_mul]
    simp only [mul_assoc,u.property.2,mul_one]
    abel
  rw [he,norm_neg]
  change ‖(star u:A)*(b*(u:A)-(u:A)*b)*(star u:A)‖ = _
  calc
    _ = ‖(star u:A)*(b*(u:A)-(u:A)*b)‖ :=
      CStarRing.norm_mul_coe_unitary _ (star u)
    _ = _ := CStarRing.norm_coe_unitary_mul (star u) _

lemma unitary_commutator_sum (u v : unitary A) (b : A) :
    ‖b*((u*v:A))-(u*v:A)*b‖ ≤
      ‖b*(u:A)-(u:A)*b‖ + ‖b*(v:A)-(v:A)*b‖ := by
  have he : b*((u:A)*(v:A))-((u:A)*(v:A))*b =
      (b*(u:A)-(u:A)*b)*(v:A)+(u:A)*(b*(v:A)-(v:A)*b) := by noncomm_ring
  rw [he]
  simpa only [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul] using norm_add_le
    ((b*(u:A)-(u:A)*b)*(v:A)) ((u:A)*(b*(v:A)-(v:A)*b))

end KOS

open scoped InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def upperCutoff (s t : ℝ) : ℝ := max (t-s) 0

lemma continuous_upperCutoff (s : ℝ) : Continuous (upperCutoff s) := by
  unfold upperCutoff
  fun_prop

omit [CompleteSpace H] in
lemma isCompactOperator_of_finiteDimensional_range (T : H →L[ℂ] H)
    [FiniteDimensional ℂ T.range] : IsCompactOperator T := by
  let S : H →L[ℂ] T.range := T.codRestrict T.range (fun v => ⟨v,rfl⟩)
  have hS : IsCompactOperator S := isCompactOperator_of_locallyCompactSpace_dom S
  exact hS.clm_comp T.range.subtypeL

end KOS

open scoped InnerProductSpace CStarAlgebra
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compactPreimageIdeal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a | IsCompactOperator (π a)}
    (by change IsCompactOperator (π 0); simpa only [map_zero,FunLike.coe_zero] using (isCompactOperator_zero : IsCompactOperator (0:H →L[ℂ] H)))
    (fun {a b} ha hb => by change IsCompactOperator (π (a+b)); simpa only [map_add,FunLike.coe_add] using ha.add hb)
    (fun {a} ha => by change IsCompactOperator (π (-a)); simpa only [map_neg,FunLike.coe_neg] using ha.neg)
    (fun {a b} hb => by change IsCompactOperator (π (a*b)); simpa only [map_mul,ContinuousLinearMap.mul_def,ContinuousLinearMap.coe_comp] using hb.clm_comp (π a))
    (fun {a b} ha => by change IsCompactOperator (π (a*b)); simpa only [map_mul,ContinuousLinearMap.mul_def,ContinuousLinearMap.coe_comp] using ha.comp_clm (π b))

lemma compactPreimageIdeal_isClosed (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (compactPreimageIdeal π : Set A) := by
  have h : IsClosed {T : H →L[ℂ] H | IsCompactOperator T} :=
    isClosed_setOfPred_isCompactOperator
  simpa only [compactPreimageIdeal,TwoSidedIdeal.coe_mk',Set.preimage_ofPred_eq] using
    h.preimage (map_continuous π)

lemma mem_compactPreimageIdeal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    a ∈ compactPreimageIdeal π ↔ IsCompactOperator (π a) := by
  simp only [compactPreimageIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Homogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Filter Topology
open scoped InnerProductSpace
namespace KOS

section

variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def Close (F : Finset A) (ε : ℝ) (f g : A →L[ℂ] ℂ) : Prop :=
  ∀ a ∈ F, dist (f a) (g a) < ε

omit partialOrderA starOrderedRingA in
theorem Close.symm [PartialOrder A] [StarOrderedRing A] {F : Finset A} {ε : ℝ} {f g : A →L[ℂ] ℂ}
    (h : Close F ε f g) : Close F ε g f := by
  intro a ha
  rw [dist_comm]
  exact h a ha

end

section
open Filter Topology
variable {A : Type*} [cStarAlgebraA : CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def tests (q : ℕ → A) (n : ℕ) : Finset A := by
  classical
  exact (Finset.range (n+1)).image q

omit cStarAlgebraA partialOrderA starOrderedRingA in
theorem mem_tests [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (q : ℕ → A) {k n : ℕ} (hk : k ≤ n) : q k ∈ tests q n := by
  classical
  exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_of_le hk),rfl⟩

def orbitTests (q : ℕ → A) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) : Finset A := by
  classical
  exact tests q n ∪ (tests q n).image α.symm

theorem step_control (q : ℕ → A) (α θ : A ≃⋆ₐ[ℂ] A) (n : ℕ) (ε : ℝ)
    (hθ : ∀ a ∈ orbitTests q α n, dist (θ a) a < ε) {k : ℕ} (hk : k ≤ n) :
    dist (α (q k)) ((θ.trans α) (q k)) < ε ∧
      dist (α.symm (q k)) ((θ.trans α).symm (q k)) < ε := by
  classical
  have hq := mem_tests q hk
  constructor
  · change dist (α (q k)) (α (θ (q k))) < ε
    rw [(StarAlgEquiv.isometry α).dist_eq,dist_comm]
    exact hθ _ (Finset.mem_union_left _ hq)
  · change dist (α.symm (q k)) (θ.symm (α.symm (q k))) < ε
    rw [← (StarAlgEquiv.isometry θ).dist_eq (α.symm (q k))
      (θ.symm (α.symm (q k))), θ.apply_symm_apply]
    apply hθ
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q k,hq,rfl⟩)

end

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma norm_inverse_inner_displacement [PartialOrder A] [StarOrderedRing A] (u : unitary A) (a : A) :
    dist ((Unitary.conjStarAlgAut ℂ A u).symm a) a = ‖a*(u:A)-(u:A)*a‖ := by
  rw [dist_eq_norm,Unitary.conjStarAlgAut_symm_apply]
  have he : star (u:A)*a*(u:A)-a = star (u:A)*(a*(u:A)-(u:A)*a) := by
    rw [mul_sub,← mul_assoc (star (u:A)) (u:A),u.property.1,one_mul,mul_assoc]
  rw [he]
  exact CStarRing.norm_coe_unitary_mul (star u) _

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]

lemma rowAverage_congruence (x : ι → A) (b a : A) :
    rowAverage (fun i => b*x i) a = b*rowAverage x a*star b := by
  simp only [rowAverage,star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]

lemma near_congruence_norm (b y : A) (d : ℝ) (hd : ‖b-1‖ ≤ d) (hd1 : d ≤ 1) :
    ‖b*y*star b-y‖ ≤ 3*d*‖y‖ := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hb : ‖b‖ ≤ 1+d := by
    have h := norm_add_le (1:A) (b-1)
    rw [add_sub_cancel] at h
    have h1 : ‖(1:A)‖ ≤ 1 := by
      nontriviality A
      simp
    linarith
  have he : b*y*star b-y = (b-1)*y*star b+y*star (b-1) := by
    simp only [star_sub,star_one]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(b-1)*y*star b‖+‖y*star (b-1)‖ := norm_add_le _ _
    _ ≤ (d*‖y‖)*(1+d)+‖y‖*d := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
          (by simpa using hb) (norm_nonneg _) (by positivity))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [norm_star] using hd) (norm_nonneg _))
    _ ≤ 3*d*‖y‖ := by nlinarith [mul_nonneg (mul_nonneg hd0 (norm_nonneg y)) (sub_nonneg.mpr hd1)]

end KOS

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Operators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped BigOperators InnerProductSpace ComplexOrder
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {ι : Type*} [fintypeι : Fintype ι] [decidableEqι : DecidableEq ι]

def matrixRow (r : ι) (x : ι → A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (fun i j => if i=r then x j else 0)

omit partialOrderA starOrderedRingA fintypeι in
@[simp] lemma matrixRow_apply [PartialOrder A] [StarOrderedRing A] [Fintype ι] (r : ι) (x : ι → A) (i j : ι) :
    matrixRow r x i j = if i=r then x j else 0 := rfl

omit partialOrderA starOrderedRingA in
lemma matrixRow_gram [PartialOrder A] [StarOrderedRing A] (r : ι) (x : ι → A) (i j : ι) :
    (star (matrixRow r x)*matrixRow r x) i j = star (x i)*x j := by
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply,matrixRow_apply]
  simp only [apply_ite star,star_zero,ite_mul,mul_ite,zero_mul,mul_zero]
  simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

def columnMap (v : ι → H) : EuclideanSpace ℂ ι →L[ℂ] H :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

omit decidableEqι completeSpaceH in
@[simp] lemma columnMap_apply [DecidableEq ι] [CompleteSpace H] (v : ι → H) (z : EuclideanSpace ℂ ι) :
    columnMap v z = ∑ i, z i • v i := by simp [columnMap]

@[simp] lemma columnMap_single (v : ι → H) (i : ι) :
    columnMap v (EuclideanSpace.single i 1) = v i := by
  simp [columnMap_apply,PiLp.single_apply,ite_smul]

lemma columnMap_adjoint_apply (v : ι → H) (y : H) (i : ι) :
    (columnMap v).adjoint y i = ⟪v i,y⟫_ℂ := by
  have h := (columnMap v).adjoint_inner_right (EuclideanSpace.single i 1) y
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul,columnMap_single] using h

def matrixOperator : CStarMatrix ι ι ℂ ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM

lemma matrixOperator_apply (M : CStarMatrix ι ι ℂ) (z : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator M z i = ∑ j, M i j*z j := rfl

def scalarGram (v : ι → H) : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun i j => ⟪v i,v j⟫_ℂ)

lemma scalarGram_operator (v : ι → H) :
    matrixOperator (scalarGram v) = (columnMap v).adjoint.comp (columnMap v) := by
  ext z i
  rw [matrixOperator_apply,ContinuousLinearMap.comp_apply,columnMap_adjoint_apply,columnMap_apply]
  change (∑ j, ⟪v i, v j⟫_ℂ * z j) = ⟪v i, ∑ j, z j • v j⟫_ℂ
  simp only [inner_sum,inner_smul_right,mul_comm]

lemma scalarGram_norm (v : ι → H) : ‖scalarGram v‖=‖columnMap v‖^2 := by
  rw [← StarAlgEquiv.norm_map (matrixOperator (ι:=ι)) (scalarGram v),scalarGram_operator,
    ContinuousLinearMap.norm_adjoint_comp_self,pow_two]

def matrixScalar : CStarMatrix ι ι ℂ →⋆ₙₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ A).toNonUnitalStarAlgHom

omit partialOrderA starOrderedRingA decidableEqι in
@[simp] lemma matrixScalar_apply [PartialOrder A] [StarOrderedRing A] [DecidableEq ι] (M : CStarMatrix ι ι ℂ) (i j : ι) :
    matrixScalar (A:=A) M i j = M i j • (1:A) := by
  change algebraMap ℂ A (M i j) = _
  exact Algebra.algebraMap_eq_smul_one _

omit decidableEqι in
lemma matrixScalar_norm [DecidableEq ι] (M : CStarMatrix ι ι ℂ) :
    ‖matrixScalar (A:=A) M‖ ≤ ‖M‖ := NonUnitalStarAlgHom.norm_apply_le _ _

omit partialOrderA starOrderedRingA in
lemma norm_lt_of_gram_approx [PartialOrder A] [StarOrderedRing A] (R G Q : A) (k δ : ℝ) (hk : 0 ≤ k) (hδ : 0 < δ)
    (hQ : ‖Q‖ ≤ 1) (hG : ‖G‖ ≤ k^2) (he : ‖star R*R-G*Q‖ < δ^2) :
    ‖R‖ < k+δ := by
  have hn : ‖G*Q‖ ≤ k^2 := by
    calc
      _ ≤ ‖G‖*‖Q‖ := norm_mul_le G Q
      _ ≤ ‖G‖*1 := mul_le_mul_of_nonneg_left hQ (norm_nonneg G)
      _ ≤ k^2 := by simpa using hG
  have hs : ‖R‖^2 ≤ ‖star R*R-G*Q‖+k^2 := by
    calc
      _ = ‖star R*R‖ := by rw [CStarRing.norm_star_mul_self,pow_two]
      _ ≤ ‖star R*R-G*Q‖+‖G*Q‖ := by
        simpa only [sub_add_cancel] using norm_add_le (star R*R-G*Q) (G*Q)
      _ ≤ _ := add_le_add le_rfl hn
  nlinarith [norm_nonneg R]

end KOS

open scoped InnerProductSpace BigOperators
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]
variable {ι : Type*} [Fintype ι]

omit completeSpaceH in
lemma norm_sum_sq_of_orthogonal [CompleteSpace H] (v : ι → H)
    (hv : ∀ i j, i ≠ j → ⟪v i,v j⟫_ℂ = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  have hi : ⟪∑ i, v i,∑ i, v i⟫_ℂ = ∑ i, ⟪v i,v i⟫_ℂ := by
    simp only [sum_inner,inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => hv j i hji) (by simp)
  have hr := congrArg Complex.reCLM hi
  simpa only [map_sum,Complex.reCLM_apply,← RCLike.re_to_complex,inner_self_eq_norm_sq] using hr

lemma projection_inner_zero {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPQ : P*Q=0) (x y : H) :
    ⟪P x,Q y⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint,hP.isSelfAdjoint.star_eq,
    ← mul_apply_eq_comp,hPQ,zero_apply,inner_zero_right]

lemma projection_family_sum_norm_sq_le (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (x : H) :
    ∑ i, ‖P i x‖^2 ≤ ‖x‖^2 := by
  classical
  let y : H := ∑ i, P i x
  have hp (i : ι) : P i y = P i x := by
    simp only [y,map_sum,← mul_apply_eq_comp]
    rw [Finset.sum_eq_single i]
    · rw [(hP i).isIdempotentElem.eq]
    · intro j _ hji
      rw [ho i j hji.symm,zero_apply]
    · simp
  have horth : ⟪y,x-y⟫_ℂ = 0 := by
    simp only [y,sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rw [← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint,(hP i).isSelfAdjoint.star_eq,
      map_sub,hp,sub_self,inner_zero_right]
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y (x-y) horth
  have hy : ‖y‖^2 = ∑ i, ‖P i x‖^2 :=
    norm_sum_sq_of_orthogonal _ (fun i j hij => projection_inner_zero (hP i) (ho i j hij) x x)
  rw [add_sub_cancel] at he
  have he' : ‖x‖^2 = ‖y‖^2 + ‖x-y‖^2 := by nlinarith [he]
  rw [hy] at he'
  nlinarith [sq_nonneg ‖x-y‖]

lemma projection_blocks_norm_le (P Q : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ i, IsStarProjection (Q i))
    (hoP : ∀ i j, i ≠ j → P i*P j=0)
    (hoQ : ∀ i j, i ≠ j → Q i*Q j=0) (b : H →L[ℂ] H) :
    ‖∑ i, Q i*b*P i‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b)
  intro x
  have hv : ∀ i, ‖Q i (b (P i x))‖ ≤ ‖b‖*‖P i x‖ := by
    intro i
    exact ((Q i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (IsStarProjection.norm_le _ (hQ i))
      (norm_nonneg _)).trans (by simpa using b.le_opNorm (P i x)))
  have he : ‖(∑ i, Q i*b*P i) x‖^2 = ∑ i, ‖Q i (b (P i x))‖^2 := by
    simp only [sum_apply,mul_apply_eq_comp]
    exact norm_sum_sq_of_orthogonal _ (fun i j hij =>
      projection_inner_zero (hQ i) (hoQ i j hij) _ _)
  have hs : ‖(∑ i, Q i*b*P i) x‖^2 ≤ (‖b‖*‖x‖)^2 := by
    rw [he]
    calc
      _ ≤ ∑ i, (‖b‖*‖P i x‖)^2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
      _ = ‖b‖^2 * ∑ i, ‖P i x‖^2 := by simp [mul_pow,Finset.mul_sum]
      _ ≤ ‖b‖^2*‖x‖^2 := mul_le_mul_of_nonneg_left
        (projection_family_sum_norm_sq_le P hP hoP x) (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs

end KOS

open scoped BigOperators
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ProjectionChain (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  P : ℕ → H →L[ℂ] H
  projection : ∀ n, IsStarProjection (P n)
  increasing : ∀ i j, i ≤ j → P i*P j=P i

namespace ProjectionChain
variable (J : ProjectionChain H)

def block (n : ℕ) : H →L[ℂ] H := J.P (n+1)-J.P n

lemma reverse_increasing (i j : ℕ) (hij : i ≤ j) : J.P j*J.P i=J.P i := by
  have h := congrArg star (J.increasing i j hij)
  simpa only [star_mul,(J.projection i).isSelfAdjoint.star_eq,
    (J.projection j).isSelfAdjoint.star_eq] using h

lemma block_projection (n : ℕ) : IsStarProjection (J.block n) := by
  constructor
  · change (J.P (n+1)-J.P n)*(J.P (n+1)-J.P n) = J.P (n+1)-J.P n
    rw [sub_mul,mul_sub,mul_sub,(J.projection (n+1)).isIdempotentElem.eq,
      (J.projection n).isIdempotentElem.eq,J.increasing n (n+1) (by omega),
      J.reverse_increasing n (n+1) (by omega)]
    abel
  · exact (J.projection (n+1)).isSelfAdjoint.sub (J.projection n).isSelfAdjoint

lemma blocks_orthogonal (i j : ℕ) (hij : i ≠ j) : J.block i*J.block j=0 := by
  have hlt : ∀ i j : ℕ, i < j → J.block i*J.block j=0 := by
    intro i j h
    dsimp [block]
    rw [sub_mul,mul_sub,mul_sub,J.increasing (i+1) (j+1) (by omega),
      J.increasing (i+1) j (by omega),J.increasing i (j+1) (by omega),
      J.increasing i j (by omega)]
    abel
  rcases lt_or_gt_of_ne hij with h|h
  · exact hlt i j h
  · have he := congrArg star (hlt j i h)
    simpa only [star_mul,star_zero,(J.block_projection i).isSelfAdjoint.star_eq,
      (J.block_projection j).isSelfAdjoint.star_eq] using he

lemma upper_block (b : H →L[ℂ] H) (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n)
    (n : ℕ) :
    J.block (n+1)*b*J.block n = b*J.P (n+1)-J.P (n+1)*b*J.P (n+1) := by
  have hfar : J.P (n+2)*b*J.P n=b*J.P n := by
    calc
      _ = J.P (n+2)*(J.P (n+1)*(b*J.P n)) := by
        simpa only [mul_assoc] using congrArg (fun T => J.P (n+2)*T) (hb n).symm
      _ = J.P (n+1)*(b*J.P n) := by
        rw [← mul_assoc,J.reverse_increasing (n+1) (n+2) (by omega)]
      _ = _ := by rw [← mul_assoc,hb n]
  dsimp [block]
  simp only [sub_mul,mul_sub]
  rw [hb (n+1),hfar,hb n]
  abel

lemma commutator_block (b : H →L[ℂ] H) (hs : IsSelfAdjoint b)
    (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n) (n : ℕ) :
    b*J.P (n+1)-J.P (n+1)*b =
      J.block (n+1)*b*J.block n-star (J.block (n+1)*b*J.block n) := by
  rw [J.upper_block b hb n]
  simp only [star_sub,star_mul,hs.star_eq,(J.projection (n+1)).isSelfAdjoint.star_eq]
  noncomm_ring

def average (N : ℕ) : H →L[ℂ] H := (N:ℝ)⁻¹ • ∑ i : Fin N, J.P (i.val+1)

lemma sum_commutator_norm_le (b : H →L[ℂ] H) (hs : IsSelfAdjoint b)
    (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n) (N : ℕ) :
    ‖b*(∑ i : Fin N, J.P (i.val+1))-(∑ i : Fin N, J.P (i.val+1))*b‖ ≤ 2*‖b‖ := by
  have he : b*(∑ i : Fin N, J.P (i.val+1))-(∑ i : Fin N, J.P (i.val+1))*b =
      (∑ i : Fin N, J.block (i.val+1)*b*J.block i.val) -
      star (∑ i : Fin N, J.block (i.val+1)*b*J.block i.val) := by
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib,star_sum]
    exact Finset.sum_congr rfl (fun i _ => J.commutator_block b hs hb i.val)
  have hu : ‖∑ i : Fin N, J.block (i.val+1)*b*J.block i.val‖ ≤ ‖b‖ := by
    apply projection_blocks_norm_le <;> try exact fun i => J.block_projection _
    · intro i j hij
      exact J.blocks_orthogonal _ _ (fun he => hij (Fin.ext he))
    · intro i j hij
      exact J.blocks_orthogonal _ _ (fun he => hij (Fin.ext (by omega)))
  rw [he]
  exact (norm_sub_le _ _).trans (by rw [norm_star]; linarith)

lemma average_commutator_norm_le (b : H →L[ℂ] H) (hs : IsSelfAdjoint b)
    (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n) (N : ℕ) :
    ‖b*J.average N-J.average N*b‖ ≤ 2*‖b‖/(N:ℝ) := by
  rw [average,mul_smul_comm,smul_mul_assoc,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  exact (mul_le_mul_of_nonneg_left (J.sum_commutator_norm_le b hs hb N)
    (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq (by ring)

end ProjectionChain
end KOS

open scoped BigOperators
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

open Classical in
def krylovSet (F : Finset (H →L[ℂ] H)) (ξ : H) : ℕ → Finset H
  | 0 => {ξ}
  | n+1 => krylovSet F ξ n ∪ F.biUnion (fun b => (krylovSet F ξ n).image b)

def krylovSpace (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (↑(krylovSet F ξ n) : Set H)

instance krylovSpace_finite (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) :
    FiniteDimensional ℂ (krylovSpace F ξ n) :=
  FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _)

omit completeSpaceH in
lemma krylovSpace_mono [CompleteSpace H] (F : Finset (H →L[ℂ] H)) (ξ : H) :
    Monotone (krylovSpace F ξ) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  apply Submodule.span_mono
  exact Finset.coe_subset.mpr (Finset.subset_union_left)

lemma mem_krylovSpace (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) :
    ξ ∈ krylovSpace F ξ n := by
  exact krylovSpace_mono F ξ (Nat.zero_le n) (Submodule.subset_span (by simp [krylovSet]))

omit completeSpaceH in
lemma map_mem_krylovSpace [CompleteSpace H] (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ)
    (b : H →L[ℂ] H) (hb : b ∈ F) {x : H} (hx : x ∈ krylovSpace F ξ n) :
    b x ∈ krylovSpace F ξ (n+1) := by
  classical
  apply Submodule.span_induction (p := fun x _ => b x ∈ krylovSpace F ξ (n+1)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    apply Submodule.subset_span
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩)
  · rw [map_zero]
    exact (krylovSpace F ξ (n+1)).zero_mem
  · intro x y _ _ hx hy
    simpa using (krylovSpace F ξ (n+1)).add_mem hx hy
  · intro a x _ hx
    simpa using (krylovSpace F ξ (n+1)).smul_mem a hx

def krylovChain (F : Finset (H →L[ℂ] H)) (ξ : H) : ProjectionChain H where
  P n := (krylovSpace F ξ n).starProjection
  projection n := isStarProjection_starProjection
  increasing i j hij := by
    exact Submodule.starProjection_comp_starProjection_of_le (krylovSpace_mono F ξ hij)

lemma krylovChain_band (F : Finset (H →L[ℂ] H)) (ξ : H)
    (b : H →L[ℂ] H) (hb : b ∈ F) (n : ℕ) :
    (krylovChain F ξ).P (n+1)*b*(krylovChain F ξ).P n = b*(krylovChain F ξ).P n := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply map_mem_krylovSpace F ξ n b hb
  exact Submodule.starProjection_apply_mem _ _

lemma krylovChain_fixes (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) :
    (krylovChain F ξ).P n ξ = ξ :=
  Submodule.starProjection_eq_self_iff.mpr (mem_krylovSpace F ξ n)

lemma krylovAverage_fixes (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) (hN : 0 < N) :
    (krylovChain F ξ).average N ξ = ξ := by
  simp only [ProjectionChain.average,smul_apply,sum_apply,krylovChain_fixes,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN),one_smul]

lemma krylovAverage_selfAdjoint (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) :
    IsSelfAdjoint ((krylovChain F ξ).average N) := by
  change star ((krylovChain F ξ).average N) = _
  simp only [ProjectionChain.average,star_smul,star_trivial,star_sum,
    fun n => ((krylovChain F ξ).projection n).isSelfAdjoint.star_eq]

lemma krylovAverage_norm (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) :
    ‖(krylovChain F ξ).average N‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl|hN
  · simp [ProjectionChain.average]
  rw [ProjectionChain.average,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hs : ‖∑ i : Fin N, (krylovChain F ξ).P (i.val+1)‖ ≤ (N:ℝ) := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ =>
      IsStarProjection.norm_le _ ((krylovChain F ξ).projection _))).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq
    (inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN))

lemma krylovAverage_mem (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) (x : H) :
    (krylovChain F ξ).average N x ∈ krylovSpace F ξ N := by
  simp only [ProjectionChain.average,smul_apply,sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  exact krylovSpace_mono F ξ (by omega : i.val+1 ≤ N)
    (Submodule.starProjection_apply_mem _ x)

lemma krylovAverage_projection (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) :
    (krylovChain F ξ).average N*(krylovSpace F ξ N).starProjection =
      (krylovChain F ξ).average N := by
  have he : (krylovSpace F ξ N).starProjection*(krylovChain F ξ).average N =
      (krylovChain F ξ).average N := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (krylovAverage_mem F ξ N x)
  have hs := congrArg star he
  simpa only [star_mul,(krylovAverage_selfAdjoint F ξ N).star_eq,
    (isStarProjection_starProjection (U:=krylovSpace F ξ N)).isSelfAdjoint.star_eq] using hs

end KOS

open scoped BigOperators InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [decidableEqι : DecidableEq ι]

lemma columnMap_comp (T : H →L[ℂ] H) (v : ι → H) :
    columnMap (fun i => T (v i)) = T.comp (columnMap v) := by
  ext z
  simp only [columnMap_apply,ContinuousLinearMap.comp_apply,map_sum,map_smul]

lemma columnMap_sub (v w : ι → H) :
    columnMap (fun i => v i-w i) = columnMap v-columnMap w := by
  ext z
  simp only [columnMap_apply,sub_apply,smul_sub,Finset.sum_sub_distrib]

lemma columnMap_matrix (v : ι → H) (B : CStarMatrix ι ι ℂ) :
    columnMap (fun j => ∑ i, B i j • v i) = (columnMap v).comp (matrixOperator B) := by
  ext z
  simp only [columnMap_apply,ContinuousLinearMap.comp_apply,matrixOperator_apply,
    Finset.smul_sum,Finset.sum_smul,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable (M : Submodule ℂ H) [finiteDimensionalM : FiniteDimensional ℂ M] (e : OrthonormalBasis ι ℂ M)

def basisColumn : EuclideanSpace ℂ ι →L[ℂ] H := columnMap (fun i => (e i : H))

omit finiteDimensionalM in
lemma basisColumn_apply [FiniteDimensional ℂ M] (z : EuclideanSpace ℂ ι) : basisColumn M e z = (e.repr.symm z : H) := by
  rw [basisColumn,columnMap_apply]
  have h := congrArg (fun x : M => (x:H)) (e.sum_repr (e.repr.symm z))
  simpa using h

lemma basisColumn_norm : ‖basisColumn M e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [basisColumn_apply]
  change ‖e.repr.symm z‖ ≤ 1*‖z‖
  simp

lemma basisColumn_projection :
    (basisColumn M e).comp (basisColumn M e).adjoint = M.starProjection := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,basisColumn,columnMap_apply,columnMap_adjoint_apply]
  rw [e.starProjection_eq_sum_rankOne]
  simp only [sum_apply,InnerProductSpace.rankOne_apply]

omit decidableEqι finiteDimensionalM in
lemma basisColumn_compression_selfAdjoint [DecidableEq ι] [FiniteDimensional ℂ M] (b : H →L[ℂ] H) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint ((basisColumn M e).adjoint.comp (b.comp (basisColumn M e))) := by
  change star _ = _
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  change (basisColumn M e).adjoint.comp ((star b).comp (basisColumn M e)) = _
  rw [hb.star_eq]

lemma compressedColumn_defect (T b : H →L[ℂ] H) (hTP : T*M.starProjection=T) :
    (b.comp (T.comp (basisColumn M e))) -
      (T.comp (basisColumn M e)).comp ((basisColumn M e).adjoint.comp (b.comp (basisColumn M e))) =
    (b*T-T*b).comp (basisColumn M e) := by
  have hp := basisColumn_projection M e
  have ht : T.comp ((basisColumn M e).comp (basisColumn M e).adjoint)=T := by
    rw [hp]
    exact hTP
  calc
    _ = b.comp (T.comp (basisColumn M e)) -
        (T.comp ((basisColumn M e).comp (basisColumn M e).adjoint)).comp
          (b.comp (basisColumn M e)) := by rfl
    _ = _ := by rw [ht]; rfl

lemma krylov_column_reconstruct (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) (hN : 0<N)
    (e : OrthonormalBasis ι ℂ (krylovSpace F ξ N)) :
    let W := (krylovChain F ξ).average N |>.comp (basisColumn (krylovSpace F ξ N) e)
    W (W.adjoint ξ) = ξ := by
  dsimp only
  rw [ContinuousLinearMap.adjoint_comp]
  have hs : ((krylovChain F ξ).average N).adjoint=(krylovChain F ξ).average N :=
    (krylovAverage_selfAdjoint F ξ N).star_eq
  rw [hs]
  simp only [ContinuousLinearMap.comp_apply,krylovAverage_fixes F ξ N hN]
  have hp := congrArg (fun T : H →L[ℂ] H => T ξ)
    (basisColumn_projection (krylovSpace F ξ N) e)
  rw [ContinuousLinearMap.comp_apply] at hp
  rw [hp,Submodule.starProjection_eq_self_iff.mpr (mem_krylovSpace F ξ N),
    krylovAverage_fixes F ξ N hN]

end KOS

open scoped BigOperators InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_quasicentral_columns (F : Finset (H →L[ℂ] H))
    (hF : ∀ b ∈ F, IsSelfAdjoint b) (ξ : H) (hξ : ‖ξ‖=1)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ (n : ℕ) (_ : 0<n) (w : Fin n → H) (B : (H →L[ℂ] H) → CStarMatrix (Fin n) (Fin n) ℂ),
      ‖columnMap w‖ ≤ 1 ∧ columnMap w ((columnMap w).adjoint ξ)=ξ ∧
      ∀ b ∈ F, IsSelfAdjoint (B b) ∧
        ‖columnMap (fun j => b (w j)-∑ i, B b i j • w i)‖ ≤ δ := by
  classical
  let K : ℝ := ∑ b ∈ F, ‖b‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun b _ => norm_nonneg b)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*K/δ)
  have hN0 : 0<N := by
    have hn : (0:ℝ)<N := (div_nonneg (by positivity) hδ.le).trans_lt hN
    exact_mod_cast hn
  let M := krylovSpace F ξ N
  let e := stdOrthonormalBasis ℂ M
  let L := basisColumn M e
  let T := (krylovChain F ξ).average N
  have hn0 : 0<Module.finrank ℂ M := by
    have hξ0 : ξ ≠ 0 := by intro hz; simp [hz] at hξ
    let : Nontrivial M := nontrivial_of_ne (⟨ξ,mem_krylovSpace F ξ N⟩:M) 0
      (by intro hz; exact hξ0 (congrArg Subtype.val hz))
    exact Module.finrank_pos
  let w := fun i => T (e i : H)
  let B := fun b : H →L[ℂ] H => matrixOperator.symm (L.adjoint.comp (b.comp L))
  have hw : columnMap w=T.comp L := columnMap_comp T _
  refine ⟨Module.finrank ℂ M,hn0,w,B,?_,?_,?_⟩
  · rw [hw]
    have hn := ContinuousLinearMap.opNorm_comp_le T L
    have hT := krylovAverage_norm F ξ N
    have hL := basisColumn_norm M e
    exact hn.trans (by nlinarith [norm_nonneg T,norm_nonneg L])
  · rw [hw]
    exact krylov_column_reconstruct F ξ N hN0 e
  · intro b hb
    have hB : IsSelfAdjoint (B b) :=
      (basisColumn_compression_selfAdjoint M e b (hF b hb)).map matrixOperator.symm
    refine ⟨hB,?_⟩
    have hd : columnMap (fun j => b (w j)-∑ i, B b i j • w i) =
        (b*T-T*b).comp L := by
      rw [columnMap_sub,columnMap_comp,columnMap_matrix,hw]
      change b.comp (T.comp L)-(T.comp L).comp (matrixOperator (matrixOperator.symm _)) = _
      rw [StarAlgEquiv.apply_symm_apply]
      exact compressedColumn_defect M e T b (krylovAverage_projection F ξ N)
    rw [hd]
    calc
      _ ≤ ‖b*T-T*b‖*‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖b*T-T*b‖ := mul_le_of_le_one_right (norm_nonneg _) (basisColumn_norm M e)
      _ ≤ 2*‖b‖/(N:ℝ) := (krylovChain F ξ).average_commutator_norm_le b (hF b hb)
        (krylovChain_band F ξ b hb) N
      _ ≤ δ := by
        have hbK : ‖b‖ ≤ K := Finset.single_le_sum (fun b _ => norm_nonneg b) hb
        have hN' : 2*K < (N:ℝ)*δ := (div_lt_iff₀ hδ).mp hN
        apply (div_le_iff₀ (by exact_mod_cast hN0)).mpr
        nlinarith

end KOS

open scoped BigOperators
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixRow_mul_scalar (r : ι) (x : ι → A) (B : CStarMatrix ι ι ℂ) :
    matrixRow r x*matrixScalar B = matrixRow r (fun j => ∑ i, B i j • x i) := by
  ext i j
  simp only [CStarMatrix.mul_apply,matrixRow_apply,matrixScalar_apply]
  by_cases h : i=r
  · simp [h]
  · simp [h]

omit partialOrderA starOrderedRingA in
lemma commutator_factorization [PartialOrder A] [StarOrderedRing A] (b X C B : A) (hb : IsSelfAdjoint b)
    (hB : IsSelfAdjoint B) (hBC : Commute B C) :
    b*(X*C*star X)-(X*C*star X)*b =
      (b*X-X*B)*C*star X-X*C*star (b*X-X*B) := by
  simp only [star_sub,star_mul,hb.star_eq,hB.star_eq]
  have he := hBC.eq
  noncomm_ring [he]

lemma commutator_factorization_norm (b X C B : A) (hb : IsSelfAdjoint b)
    (hB : IsSelfAdjoint B) (hBC : Commute B C) :
    ‖b*(X*C*star X)-(X*C*star X)*b‖ ≤ 2*‖b*X-X*B‖*‖X‖*‖C‖ := by
  rw [commutator_factorization b X C B hb hB hBC]
  calc
    _ ≤ ‖(b*X-X*B)*C*star X‖+‖X*C*star (b*X-X*B)‖ := norm_sub_le _ _
    _ ≤ (‖b*X-X*B‖*‖C‖)*‖star X‖+(‖X‖*‖C‖)*‖star (b*X-X*B)‖ := by
      exact add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))) ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ = _ := by simp only [norm_star]; ring

end KOS

open scoped InnerProductSpace BigOperators
open Filter Topology

open scoped BigOperators InnerProductSpace
open Filter Topology

open scoped BigOperators InnerProductSpace ComplexStarModule
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit partialOrderA starOrderedRingA in
lemma commutator_real_imaginary_norm [PartialOrder A] [StarOrderedRing A] (b y : A) :
    ‖b*y-y*b‖ ≤ ‖(realPart b:A)*y-y*(realPart b:A)‖ +
      ‖(imaginaryPart b:A)*y-y*(imaginaryPart b:A)‖ := by
  have he : b*y-y*b = ((realPart b:A)*y-y*(realPart b:A)) +
      Complex.I • ((imaginaryPart b:A)*y-y*(imaginaryPart b:A)) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart b]
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub]
    abel
  rw [he]
  simpa only [norm_smul,Complex.norm_I,one_mul] using norm_add_le
    ((realPart b:A)*y-y*(realPart b:A)) (Complex.I • ((imaginaryPart b:A)*y-y*(imaginaryPart b:A)))

omit partialOrderA starOrderedRingA in
lemma commutator_congruence_norm_four [PartialOrder A] [StarOrderedRing A] (F b y : A) (d c : ℝ)
    (hd : ‖b-1‖ ≤ d) (hd1 : d ≤ 1) (hy : ‖y‖ ≤ 4)
    (hc : ‖F*y-y*F‖ ≤ c) :
    ‖F*(b*y*star b)-(b*y*star b)*F‖ ≤ c+24*‖F‖*d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hn : ‖b*y*star b-y‖ ≤ 12*d :=
    (near_congruence_norm b y d hd hd1).trans (by nlinarith)
  have he : F*(b*y*star b)-(b*y*star b)*F =
      (F*y-y*F) + F*(b*y*star b-y)-(b*y*star b-y)*F := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖F*y-y*F‖+‖F*(b*y*star b-y)‖+‖(b*y*star b-y)*F‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c+‖F‖*(12*d)+(12*d)*‖F‖ := by
      apply add_le_add
      · exact add_le_add hc ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    _ = _ := by ring

end KOS

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open Topology
section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

lemma closed_map_isClosed (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) : IsClosed (S.map φ : Set B) :=
  (NonUnitalStarAlgHom.isometry φ.toNonUnitalStarAlgHom hφ).isClosedEmbedding.isClosedMap _
    (show IsClosed (S : Set A) from inferInstance)

end

open Topology

open Topology
section
local instance instDecidableEqOrdinal_solutions : DecidableEq Ordinal.{0} := Classical.decEq _
end

section
local instance instDecidableEqOrdinal_solutions_1 : DecidableEq Ordinal.{0} := Classical.decEq _

end

section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

def fullImageEquiv (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (S : StarSubalgebra ℂ B) (hS : S = φ.range) : A ≃⋆ₐ[ℂ] S :=
  StarAlgEquiv.ofBijective (φ.codRestrict S (fun a => hS ▸ ⟨a,rfl⟩))
    ⟨fun a b h => hφ (congrArg Subtype.val h),by
      intro a
      have ha : (a:B) ∈ φ.range := hS ▸ a.property
      obtain ⟨b,hb⟩ := ha
      exact ⟨b,Subtype.ext hb⟩⟩

def fullTopEquiv (T : StarSubalgebra ℂ B) (hT : T = ⊤) : B ≃⋆ₐ[ℂ] T :=
  StarAlgEquiv.ofBijective ((StarAlgHom.id ℂ B).codRestrict T (fun _ => hT ▸ trivial))
    ⟨fun _ _ h => congrArg Subtype.val h,fun a => ⟨a,Subtype.ext rfl⟩⟩

end

open Topology

open Topology
namespace ChronologicalStage
local instance instDecidableEqOrdinal : DecidableEq Ordinal.{0} := Classical.decEq _

end ChronologicalStage

open CategoryTheory

open CategoryTheory

open CategoryTheory Topology

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory Cardinal Classical

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct

open Cardinal Ordinal

abbrev ConstructionIndex := constructionCardinal.{0}.ord.ToType

lemma construction_ordinal_limit : Order.IsSuccLimit constructionCardinal.{0}.ord :=
  Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_continuum.trans (Order.le_succ _))

instance constructionIndex_nonempty : Nonempty ConstructionIndex :=
  ⟨Ordinal.ToType.mk ⟨0,construction_ordinal_limit.bot_lt⟩⟩

instance constructionIndex_orderBot : OrderBot ConstructionIndex :=
  WellFoundedLT.toOrderBot _

instance constructionIndex_noMax : NoMaxOrder ConstructionIndex where
  exists_gt j := by
    refine ⟨Ordinal.ToType.mk ⟨(j:Ordinal)+1,construction_ordinal_limit.add_one_lt j.toOrd.property⟩,?_⟩
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    change (j:Ordinal) < (Ordinal.ToType.mk ⟨(j:Ordinal)+1,_⟩ : Ordinal)
    simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using lt_add_one (j:Ordinal)

lemma constructionIndex_cardinal : Cardinal.continuum ≤ Cardinal.mk ConstructionIndex := by
  rw [Cardinal.mk_ord_toType]
  exact Order.le_succ _

open CategoryTheory Topology

open CategoryTheory Cardinal

universe u v w

end NaimarkZFC

end

end OAI
end


