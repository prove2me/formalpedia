-- Prove2me | Definitions.Def_OAIQ106D068
-- name    : OAIQ106D068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:30:54.41+00:00
-- url     : https://prove2.me/theorems/491b7a91-69cf-4444-a171-2e8e40e5c834
-- title:
--   Definitions bundle OAIQ106D068 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 664 declarations of OpenAI's Lean: 581 definitions, 1 inductive type or structure, 9 instances and 73 theorems. The definitions and types are `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation51`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation52`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation53`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation54`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation55`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation56`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation57`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation58`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation59`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation6`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation60`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation61`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation62`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation63`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation64`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation65`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation66`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation67`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation7`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation8`, `OAI.MUB6.Certificate.PairTargetSemantics.extraPermutation9`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw0`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw0step0`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw0step1`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw0step2`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw1`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw10`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw100`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw100step0`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw100step1`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw101`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw101step0`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw101step1`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw101step2`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw102`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw102step0`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw102step1`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw102step2`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw103`, `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw103step0` and 542 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Bases_Families`, `MutuallyUnbiased_Completion_Complement`, `MutuallyUnbiased_Completion_Frame`, `MutuallyUnbiased_Completion_JointBasis`, `MutuallyUnbiased_Completion_Kraus`, `MutuallyUnbiased_Completion_OrthogonalPinching`, `MutuallyUnbiased_Completion_ProjectionBasis`, `MutuallyUnbiased_Completion_Superoperator`, `MutuallyUnbiased_Cubic_CubicMultiplicityCore`, `MutuallyUnbiased_Cubic_CubicSupport`, `MutuallyUnbiased_Cubic_CubicSymmetric`, `MutuallyUnbiased_Cubic_FiveCycle`, `MutuallyUnbiased_Cubic_NormalizedCodes`, `MutuallyUnbiased_Matrix_Definitions`, `MutuallyUnbiased_Moments_EqualityPatterns`, `MutuallyUnbiased_Moments_MomentContraction`, `MutuallyUnbiased_Moments_PartitionExpansion`, `MutuallyUnbiased_Moments_Sampling`, `MutuallyUnbiased_Moments_SmallPartitions`, `MutuallyUnbiased_PairMoments_PairCharges`, `MutuallyUnbiased_PairTargets_ExtraCanonical0`, `MutuallyUnbiased_PairTargets_ExtraCanonical1`, `MutuallyUnbiased_PairTargets_ExtraCanonical2`, `MutuallyUnbiased_PairTargets_ExtraCanonical3`, `MutuallyUnbiased_PairTargets_ExtraCanonical4`, `MutuallyUnbiased_PairTargets_ExtraCanonical5`, `MutuallyUnbiased_PairTargets_ExtraCanonical6`, `MutuallyUnbiased_PairTargets_ExtraCanonical7`, `MutuallyUnbiased_PairTargets_ExtraCanonical8`, `MutuallyUnbiased_PairTargets_ExtraPermutations`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D140` and `OAIQ106D141`; the statements `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical110`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical111`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical112`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical113`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical114`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical115`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical116`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical117`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical118`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical119`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical120`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical121`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical122`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical123`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical125`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical126`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical35`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical36`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical4`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical5`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical56`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical57`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical58`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical59`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical60`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical61`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical62`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical90` and `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical91`; the proofs of `OAI.MUB6.Certificate.PairSemantics.canonical5123`, `OAI.MUB6.Certificate.PairSemantics.canonical5164`, `OAI.MUB6.Certificate.PairSemantics.canonical7982`, `OAI.MUB6.Certificate.PairSemantics.canonical845`, `OAI.MUB6.Certificate.PairSemantics.canonical9056`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical110`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical111`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical112`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical113`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical114`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical115`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical116`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical117`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical118`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical119`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical120`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical121`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical122`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical123`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical125`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical126`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical35`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical36`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical4`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical5`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical56`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical57`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical58`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical59`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical60`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical61`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical62`, `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical90` and `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical91`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_MUBSix

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def order (a : Charge) : ℕ := ∑ i, (a i).toNat

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Families
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and cardinality lemmas. These reductions do not establish the
no-seven or completion theorem, which remain separate proof obligations. -/

noncomputable section
namespace MUB6

/-- Precise completion statement, including preservation of the original bases. -/
def SixExtendToSeven : Prop :=
  ∀ B : Fin 6 → Basis, IsMUBFamily B →
    ∃ C : Fin 7 → Basis, IsMUBFamily C ∧ ∀ i : Fin 6, C i.castSucc = B i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite trace-preserving Kraus maps

The proof establishes the fixed-point commutation step needed in Weiner's completion
argument. It replaces the appeal to two-positivity and the multiplicative domain
with the squared Hilbert--Schmidt norm of each commutator.
-/

namespace MUB6.Weiner

open scoped BigOperators ComplexOrder
open Matrix

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- A finite Kraus sum, with the adjoint on the left. -/
def kraus (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (A i)ᴴ * X * A i

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Superoperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Realignment of a self-adjoint projection

The complement operator in Weiner's argument is an orthogonal projection whose
matrix is invariant under realignment. Its columns therefore form a finite
Kraus family; choosing an orthonormal basis of its range is unnecessary.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a matrix on pairs of indices to an ordinary matrix. -/
def applySuper (C : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ p, C (i, j) p * X p.1 p.2

/-- A column of a superoperator, reshaped as an ordinary matrix. -/
def superColumn (C : Matrix (n × n) (n × n) ℂ) (p : n × n) : Matrix n n ℂ :=
  fun i j => C (i, j) p

/-- The realignment symmetry relevant to a Kraus decomposition. -/
def IsRealigned (C : Matrix (n × n) (n × n) ℂ) : Prop :=
  ∀ i j k l, C (i, j) (k, l) = C (l, j) (k, i)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Complement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete complement supermatrix

The Hermitian and realignment symmetries are algebraic identities for arbitrary
complex vectors. Orthonormality and mutual unbiasedness are needed for the
separate unitality and idempotence identities.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]

/-- Supermatrix of the unnormalized trace map `X ↦ trace(X) I`. -/
def traceMatrix : Matrix (n × n) (n × n) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

/-- Supermatrix of the sum of rank-one pinching maps for a vector family. -/
def pinchingMatrix (v : κ → n → ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun p q => ∑ a, v a p.1 * star (v a p.2) * star (v a q.1) * v a q.2

/-- Candidate missing-basis projection for six bases in dimension six. -/
def complementMatrix (v : ι → κ → n → ℂ) : Matrix (n × n) (n × n) ℂ :=
  1 + traceMatrix - ∑ r, pinchingMatrix (v r)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Frame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank-one frame identities used to calculate the complement projection. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {I κ η n : Type*} [Fintype I] [Fintype κ] [Fintype η] [Fintype n]

/-- Sum of the rank-one operators of a finite vector family. -/
def frameOperator (v : κ → I → ℂ) : Matrix I I ℂ :=
  ∑ a, Matrix.vecMulVec (v a) (star (v a))

/-- Flatten the rank-one matrix associated with an arbitrary complex vector. -/
def projectorVector (v : n → ℂ) : n × n → ℂ := fun p => v p.1 * star (v p.2)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_JointBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An orthonormal eigenbasis for a commuting symmetric family

This is the finite-dimensional simultaneous spectral step in the completion
argument. It specializes mathlib's joint-eigenspace decomposition and retains
an explicit common eigenvalue for each basis vector and each operator.
-/

namespace MUB6.Weiner

open Module
open scoped Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Finite tuples of actual eigenvalues, excluding irrelevant scalar tuples. -/
abbrev JointIndex (T : ι → End ℂ E) := ∀ i, (T i).Eigenvalues

noncomputable def jointSubspace (T : ι → End ℂ E) (χ : JointIndex T) : Submodule ℂ E :=
  ⨅ i, (T i).eigenspace (χ i : ℂ)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_OrthogonalPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplication tables for six and seven unbiased pinching operators. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

abbrev SuperSix := Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) ℂ

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_ProjectionBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-one projectors fixed by a realigned orthogonal projection

The fixed space of the complement operator contains the projectors of an
orthonormal basis. This is the spectral part of the completion argument.
-/

namespace MUB6.Weiner

open Matrix Module
open scoped BigOperators Function

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of the orthogonal rank-one operator associated with a vector. -/
def projector (v : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.vecMulVec v (star v)

/-- The real and imaginary parts of the reshaped columns. -/
noncomputable def hermitianColumn (C : Matrix (n × n) (n × n) ℂ)
    (p : Bool × (n × n)) : Matrix n n ℂ :=
  if p.1 then (imaginaryPart (superColumn C p.2) : Matrix n n ℂ)
  else (realPart (superColumn C p.2) : Matrix n n ℂ)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary symmetric sums for the six-entry cubic classification. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def elementarySum (v : (Fin 6) → ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin 6)).powersetCard k, ∏ i ∈ s, v i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicMultiplicityCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity counting once the two possible cubed values are known. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def cubeClass (v : (Fin 6) → ℂ) (a : ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = a)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-support step of the cubic classification in §3.

These lemmas concern two three-element supports avoiding coordinate zero.
The last theorem states that a quotient having the cubed-value pattern proved
for Hadamard row ratios forces the supports to coincide.
-/

noncomputable section

namespace MUB6

def TwoValuePattern (f : (Fin 6) → ℂ) : Prop := by
  classical
  exact (∃ a b : ℂ, ∀ i, f i = a ∨ f i = b) ∧
    ∀ a : ℂ, (∃ i, f i = a) → (∃ j, f j ≠ a) →
      (Finset.univ.filter (fun i => f i = a)).card = 3

def supportedValue (S : Finset (Fin 6)) (x : ℂ) (i : (Fin 6)) : ℂ :=
  if i ∈ S then x else 1

def supportedRatio (S U : Finset (Fin 6)) (x y : ℂ) (i : (Fin 6)) : ℂ :=
  supportedValue S x i / supportedValue U y i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_FiveCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite, kernel-checked classification of simple two-regular graphs on
five vertices.  Ten Boolean edge choices are checked, not matrices over a
restricted alphabet. -/

namespace MUB6

def fiveGraph (b : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool :=
  !![false, b 0, b 1, b 2, b 3;
     b 0, false, b 4, b 5, b 6;
     b 1, b 4, false, b 7, b 8;
     b 2, b 5, b 7, false, b 9;
     b 3, b 6, b 8, b 9, false]

def fiveCycleOrder : Fin 12 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4], ![0, 1, 3, 4, 2],
    ![0, 1, 4, 2, 3], ![0, 1, 4, 3, 2], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3],
    ![0, 2, 3, 1, 4], ![0, 2, 4, 1, 3], ![0, 3, 1, 2, 4], ![0, 3, 2, 1, 4]]

def canonicalFiveCycle : Fin 5 → Fin 5 → Bool :=
  fiveGraph ![true, false, false, true, true, false, false, true, false, true]

theorem fiveCycleOrder_bijective : ∀ c, Function.Bijective (fiveCycleOrder c) := by
  decide +kernel

noncomputable def fiveCyclePermutation (c : Fin 12) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (fiveCycleOrder c) (fiveCycleOrder_bijective c)

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_NormalizedCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A second finite presentation of the five-cycle classification.  A row has
two positive signs among four off-diagonal positions, hence six choices. -/

namespace MUB6

def fourChoices : Fin 6 → Fin 4 → Bool :=
  ![![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false],
    ![false, true, false, true], ![false, false, true, true]]

def offDiagonalIndex (i j : Fin 5) (h : i ≠ j) : Fin 4 :=
  ⟨if j.val < i.val then j.val else j.val - 1, by
    have hn : i.val ≠ j.val := fun e => h (Fin.ext e)
    split_ifs <;> omega⟩

def fiveRowChoice (i : Fin 5) (a : Fin 6) (j : Fin 5) : Bool :=
  if h : i = j then false else fourChoices a (offDiagonalIndex i j h)

def normalizedCodeGraph (a : Fin 5 → Fin 6) (i j : Fin 5) : Bool :=
  fiveRowChoice i (a i) j

def normalizedCodeOrthogonal (a : Fin 5 → Fin 6) : Prop :=
  ∀ i j, i ≠ j →
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧
      normalizedCodeGraph a i k = normalizedCodeGraph a j k)).card = 1

def normalizedCodeClassified (a : Fin 5 → Fin 6) : Prop :=
  normalizedCodeOrthogonal a →
    ∃ c, ∀ i j, normalizedCodeGraph a (fiveCycleOrder c i) (fiveCycleOrder c j) =
      canonicalFiveCycle i j

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite set-partition expansion, presented by explicit surjective block
labels. This separates the finite combinatorics from complex matrix moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.EqualityPatterns

variable {A P B V : Type*}

/-- Each `label p` is a surjection onto the blocks of one partition. -/
structure Family (A P : Type*) where
  blocks : P → ℕ
  label : (p : P) → A → Fin (blocks p)
  onto : ∀ p, Function.Surjective (label p)
  unique : ∀ p q, (∀ i j, label p i = label p j ↔ label q i = label q j) → p = q

namespace Family

def flatten (F : Family A P) (s : Σ p, Fin (F.blocks p) ↪ B) : A → B :=
  fun i => s.2 (F.label s.1 i)

theorem flatten_injective (F : Family A P) : Function.Injective (F.flatten (B := B)) := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have hpq : p = q := F.unique p q (by
    intro i j
    have hi := congrFun h i
    have hj := congrFun h j
    change e (F.label p i) = f (F.label q i) at hi
    change e (F.label p j) = f (F.label q j) at hj
    constructor
    · intro hij
      apply f.injective
      rw [← hi, ← hj, hij]
    · intro hij
      apply e.injective
      rw [hi, hj, hij])
  subst q
  congr 1
  ext b
  obtain ⟨i, rfl⟩ := F.onto p b
  exact congrFun h i

theorem flatten_surjective (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) :
    Function.Surjective (F.flatten (B := B)) := by
  classical
  intro f
  obtain ⟨p, hp⟩ := cover f
  let r : Fin (F.blocks p) → A := Function.surjInv (F.onto p)
  have hr : ∀ b, F.label p (r b) = b := Function.rightInverse_surjInv (F.onto p)
  let e : Fin (F.blocks p) ↪ B :=
    ⟨fun b => f (r b), by
      intro b c h
      have hbc := (hp (r b) (r c)).mpr h
      simpa only [hr] using hbc⟩
  refine ⟨⟨p, e⟩, ?_⟩
  funext i
  exact (hp (r (F.label p i)) i).mp (hr _)

/-- Every function has exactly one equality pattern and an injection assigning
distinct values to its blocks. No probabilistic premise is used. -/
def assignmentsEquiv (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) :
    (Σ p, Fin (F.blocks p) ↪ B) ≃ (A → B) :=
  Equiv.ofBijective F.flatten ⟨F.flatten_injective, F.flatten_surjective cover⟩

end Family

end MUB6.EqualityPatterns

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

def dropFirst {p : ℕ} (e : Fin (p + 1) ↪ B) : Fin p ↪ B :=
  (Equiv.embeddingFinSucc p B e).1

omit [Fintype B] in
@[simp] theorem dropFirst_apply {p : ℕ} (e : Fin (p + 1) ↪ B) (i : Fin p) :
    dropFirst e i = e i.succ := rfl

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def mergeFirst {p q : ℕ} (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (j : Fin p) :
    Matrix (Fin p) (Fin q) ℤ :=
  fun u v => A u.succ v + if u = j then A 0 v else 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

def groupedColumns {p n k : ℕ} (A : Matrix (Fin p) (Fin n) ℤ)
    (label : Fin n → Fin k) : Matrix (Fin p) (Fin k) ℤ :=
  fun i b => ∑ j with label j = b, A i j

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

def raw2 : Fin 2 → Fin 2 → ℕ := ![![0, 0], ![0, 1]]

def blocks3 : Fin 5 → ℕ := ![1, 2, 2, 2, 3]
def raw3 : Fin 5 → Fin 3 → ℕ := ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2]]
def label3 (p : Fin 5) (i : Fin 3) : Fin (blocks3 p) :=
  ⟨raw3 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family3 : Family (Fin 3) (Fin 5) where
  blocks := blocks3
  label := label3
  onto := by decide +kernel
  unique := by decide +kernel

def blocks4 : Fin 15 → ℕ := ![1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 4]
def raw4 : Fin 15 → Fin 4 → ℕ := ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0], ![0, 1, 1, 1], ![0, 1, 1, 2], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, 1, 2, 3]]
def label4 (p : Fin 15) (i : Fin 4) : Fin (blocks4 p) :=
  ⟨raw4 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family4 : Family (Fin 4) (Fin 15) where
  blocks := blocks4
  label := label4
  onto := by decide +kernel
  unique := by decide +kernel

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

def pairCoefficient : Fin 4 → ℂ := ![2, 1, 1, 1]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraPermutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraPermutation6 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation7 : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation8 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation9 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation51 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 1, 0]
  invFun := ![4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation52 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 1, 2]
  invFun := ![2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation53 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 0, 2]
  invFun := ![3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation54 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 2, 0]
  invFun := ![4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation55 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 1, 0]
  invFun := ![4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation56 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation57 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation58 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation59 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation60 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation61 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation62 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation63 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation64 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation65 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation66 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation67 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def extraRaw0step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw0step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw0step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def extraRaw1step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw1step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def extraRaw1step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def extraRaw2step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def extraRaw2step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw3 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]

def extraRaw3step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def extraRaw3step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 1, 1]]

def extraRaw3step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw4 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def extraRaw4step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def extraRaw4step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw5 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def extraRaw5step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def extraRaw5step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def extraRaw5step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw6 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw6step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw6step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw7 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw7step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw8 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw8step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw8step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw9 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw9step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw9step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw9step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw9step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw9step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw10 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw10step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw10step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw11 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw11step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw11step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw11step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw12 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw12step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw13 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw13step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw13step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw14 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw14step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw14step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw14step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0]]

def extraRaw14step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw14step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw15 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw15step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw15step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw16 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw16step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw16step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw16step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw16step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw16step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw17 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw17step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw17step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw18 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw18step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw18step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw18step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw19 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw19step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw20 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw20step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def extraRaw20step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1]]

def extraRaw20step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw21 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def extraRaw21step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw21step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw22 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw22step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -1, 1]]

def extraRaw22step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -1, 1]]

def extraRaw22step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw23 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw23step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw23step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw23step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw23step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw23step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw24 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1]]

def extraRaw24step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def extraRaw25 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1]]

def extraRaw25step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw25step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw25step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw26 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw26step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw26step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw27 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw27step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def extraRaw27step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, -1, 1, 1]]

def extraRaw27step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw28 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def extraRaw28step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw28step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw29 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw29step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]

def extraRaw29step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]

def extraRaw29step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw30 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw30step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![-1, 1]]

def extraRaw30step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw30step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw31 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]

def extraRaw31step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw32 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def extraRaw32step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw32step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw32step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw33 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw33step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw33step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw34 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw34step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def extraRaw34step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def extraRaw34step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw35 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw35step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw35step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw36 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw36step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def extraRaw37 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw37step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw37step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def extraRaw37step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def extraRaw37step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw38 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw38step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw38step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def extraRaw39 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw39step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw39step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw40 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw40step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw40step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw40step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw41 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw41step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw41step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw42 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw42step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw42step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw43 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw43step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def extraRaw43step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw43step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw44 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1], ![0, 0], ![0, 0]]

def extraRaw44step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw44step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def extraRaw44step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def extraRaw44step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def extraRaw45 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw45step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw45step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def extraRaw46 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]

def extraRaw46step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw46step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]

def extraRaw46step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def extraRaw47 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def extraRaw47step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw48 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw48step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def extraRaw48step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def extraRaw49 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![0, 0]]

def extraRaw49step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw49step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def extraRaw49step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw50 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw50step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw50step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw51 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![0, 0]]

def extraRaw51step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw51step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw51step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw51step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw51step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw52 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]

def extraRaw52step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, 0, 1]]

def extraRaw52step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw53 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1]]

def extraRaw53step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw53step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1]]

def extraRaw53step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw54 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw54step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw55 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw55step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 1, -1, -1]]

def extraRaw55step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw56 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def extraRaw56step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw56step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def extraRaw56step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw57 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw57step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw57step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw58 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw58step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def extraRaw58step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw58step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw58step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw58step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw59 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def extraRaw59step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]

def extraRaw59step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw60 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]

def extraRaw60step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw60step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0]]

def extraRaw60step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw61 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw61step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def extraRaw61step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw62 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw62step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def extraRaw62step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw63 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-1, 1]]

def extraRaw63step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-2, 2], ![-1, 1]]

def extraRaw63step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-2, 2], ![-1, 1]]

def extraRaw63step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw64 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]]

def extraRaw64step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![0, 2, -2], ![1, 1, -2]]

def extraRaw64step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw65 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def extraRaw65step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw65step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw65step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw66 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw66step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw66step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw67 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw67step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw67step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw68 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw68step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def extraRaw69 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw69step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw69step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw70 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw70step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw70step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw71 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![0, 0]]

def extraRaw71step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw71step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![1, -1], ![-1, 1]]

def extraRaw71step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw72 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw72step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]

def extraRaw72step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]

def extraRaw72step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw73 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw73step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw73step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw74 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1]]

def extraRaw74step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw75 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]

def extraRaw75step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]

def extraRaw75step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]

def extraRaw75step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw76 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![1, 1, -1, -1]]

def extraRaw76step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![-1, -1, 1, 1]]

def extraRaw76step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![-1, 0, 0, 1], ![0, -2, 1, 1], ![-1, -1, 1, 1]]

def extraRaw76step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw77 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1]]

def extraRaw77step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def extraRaw77step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def extraRaw78 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2], ![0, 0]]

def extraRaw78step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw78step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw78step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-2, 2]]

def extraRaw78step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def extraRaw79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1]]

def extraRaw79step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, 0, 1]]

def extraRaw79step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, 0, 1]]

def extraRaw79step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw80 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 1, -1]]

def extraRaw80step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 1, -1]]

def extraRaw80step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw81 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]

def extraRaw81step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw81step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw81step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw82 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]]

def extraRaw82step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![1, 1, -1, -1]]

def extraRaw82step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def extraRaw83 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def extraRaw83step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw84 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2]]

def extraRaw84step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def extraRaw85 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw85step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw86 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw86step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2]]

def extraRaw86step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw87 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0]]

def extraRaw87step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0]]

def extraRaw87step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw88 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw88step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw88step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw89 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]]

def extraRaw89step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![0, 2, -1, -1], ![1, 1, 0, -2]]

def extraRaw89step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw90 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]

def extraRaw90step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2]]

def extraRaw90step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]

def extraRaw90step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def extraRaw91 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]]

def extraRaw91step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![0, 2, -2]]

def extraRaw91step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def extraRaw92 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw92step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw92step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw92step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw93 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw93step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw93step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def extraRaw94 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw94step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw94step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw95 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw95step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw96 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw96step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw96step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw97 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw97step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw97step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw98 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![-1, 1]]

def extraRaw98step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw98step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-1, 1], ![1, -1], ![-1, 1]]

def extraRaw98step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw99 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw99step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]

def extraRaw99step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]

def extraRaw99step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def extraRaw100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]

def extraRaw100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def extraRaw101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1]]

def extraRaw101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def extraRaw102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

def extraRaw102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

def extraRaw102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

def extraRaw102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def extraRaw103 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![-1, -1, 0, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1], ![0, 2, -1, -1]]

def extraRaw103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 1, 1]]

def extraRaw103step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 2, -2, -1], ![1, 1, 0, -2], ![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 1, 1]]

def extraRaw103step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def extraRaw104 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![1, -1], ![-1, 1]]

def extraRaw104step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![1, -1], ![-1, 1]]

def extraRaw104step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def extraRaw105 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1]]

def extraRaw105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def extraRaw106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1]]

def extraRaw106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]

def extraRaw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]

def extraRaw107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]

def extraRaw108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]

def extraRaw108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def extraRaw109 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]]

def extraRaw109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![0, 2, -1, -1]]

def extraRaw109step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def extraRaw110 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2]]

def extraRaw110step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def extraRaw111 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![-2, 2]]

def extraRaw111step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw111step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![0, 0], ![1, -1], ![-2, 2]]

def extraRaw111step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![-2, 2]]

def extraRaw111step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2]]

def extraRaw112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]

def extraRaw112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]

def extraRaw112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]

def extraRaw113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]

def extraRaw113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def extraRaw114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]

def extraRaw114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def extraRaw114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw114step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def extraRaw115 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]]

def extraRaw115step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![1, 0, -1, 0], ![1, 1, -1, -1], ![0, 2, 0, -2]]

def extraRaw115step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def extraRaw116 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![0, 0]]

def extraRaw116step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0]]

def extraRaw116step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2]]

def extraRaw116step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![-2, 2]]

def extraRaw116step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw116step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw117 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-3, 3], ![-1, 1], ![-1, 1]]

def extraRaw117step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

def extraRaw118 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def extraRaw119 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0], ![0, 0]]

def extraRaw119step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def extraRaw119step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def extraRaw119step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def extraRaw119step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0]]

def extraRaw120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0]]

def extraRaw120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]

def extraRaw120step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -2, 2]]

def extraRaw120step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]

def extraRaw120step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw120step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw121 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1]]

def extraRaw121step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw124step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw124step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def extraRaw126 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-1, -2, 1, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def extraRaw126step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def extraRaw127 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw127step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw127step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0], ![0, 0]]

def extraRaw127step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-2, 2], ![0, 0]]

def extraRaw127step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw127step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraRaw128 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw128step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw129 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def extraRaw130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def extraRaw130step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def extraRaw130step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0]]

def extraRaw131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2], ![0, 0, 0]]

def extraRaw131step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]

def extraRaw131step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]

def extraRaw131step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def extraRaw132 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]

def extraRaw132step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def extraRaw133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def extraRaw133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def extraRaw133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def extraRaw135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def extraRaw135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def extraRaw136 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 2, -1, -2], ![1, -2, -1, 2], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def extraRaw136step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

end MUB6.Certificate.PairTargetSemantics

end OAI
end


