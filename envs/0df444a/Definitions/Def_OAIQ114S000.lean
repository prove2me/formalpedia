-- Prove2me | Definitions.Def_OAIQ114S000
-- name    : OAIQ114S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:29:58.197963+00:00
-- url     : https://prove2.me/theorems/77863a58-6b81-4bc7-a799-fa2b9416b4df
-- title:
--   Definitions bundle OAIQ114S000 of the split of OpenAI, Snaky in 21 Maker moves
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SnakyCertificate.certificate_correct`, carved from OpenAI's openai/math development (OpenAI, *Snaky in 21 Maker moves*, OpenAI Math Release, September 25, 2026, result family 187, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4141 declarations of OpenAI's Lean: 4061 definitions, 1 inductive type or structure, 9 instances and 70 theorems. The definitions and types are `OAI.SnakyCertificate.Check.CacheEquation`, `OAI.SnakyCertificate.Check.ListRow`, `OAI.SnakyCertificate.Check.cacheChunk_0`, `OAI.SnakyCertificate.Check.cacheChunk_1`, `OAI.SnakyCertificate.Check.cacheChunk_10`, `OAI.SnakyCertificate.Check.cacheChunk_11`, `OAI.SnakyCertificate.Check.cacheChunk_12`, `OAI.SnakyCertificate.Check.cacheChunk_13`, `OAI.SnakyCertificate.Check.cacheChunk_14`, `OAI.SnakyCertificate.Check.cacheChunk_15`, `OAI.SnakyCertificate.Check.cacheChunk_16`, `OAI.SnakyCertificate.Check.cacheChunk_17`, `OAI.SnakyCertificate.Check.cacheChunk_18`, `OAI.SnakyCertificate.Check.cacheChunk_19`, `OAI.SnakyCertificate.Check.cacheChunk_2`, `OAI.SnakyCertificate.Check.cacheChunk_20`, `OAI.SnakyCertificate.Check.cacheChunk_21`, `OAI.SnakyCertificate.Check.cacheChunk_22`, `OAI.SnakyCertificate.Check.cacheChunk_23`, `OAI.SnakyCertificate.Check.cacheChunk_24`, `OAI.SnakyCertificate.Check.cacheChunk_25`, `OAI.SnakyCertificate.Check.cacheChunk_26`, `OAI.SnakyCertificate.Check.cacheChunk_27`, `OAI.SnakyCertificate.Check.cacheChunk_28`, `OAI.SnakyCertificate.Check.cacheChunk_29`, `OAI.SnakyCertificate.Check.cacheChunk_3`, `OAI.SnakyCertificate.Check.cacheChunk_30`, `OAI.SnakyCertificate.Check.cacheChunk_4`, `OAI.SnakyCertificate.Check.cacheChunk_5`, `OAI.SnakyCertificate.Check.cacheChunk_6`, `OAI.SnakyCertificate.Check.cacheChunk_7`, `OAI.SnakyCertificate.Check.cacheChunk_8`, `OAI.SnakyCertificate.Check.cacheChunk_9`, `OAI.SnakyCertificate.Check.cacheChunks`, `OAI.SnakyCertificate.Check.cache_0`, `OAI.SnakyCertificate.Check.cache_0_A`, `OAI.SnakyCertificate.Check.cache_0_A_part0`, `OAI.SnakyCertificate.Check.cache_0_H`, `OAI.SnakyCertificate.Check.cache_0_H_part0`, `OAI.SnakyCertificate.Check.cache_1` and 4022 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `SnakyCertificate_Cache`, `SnakyCertificate_CacheData00`, `SnakyCertificate_CacheData01`, `SnakyCertificate_CacheData02`, `SnakyCertificate_CacheData03`, `SnakyCertificate_CacheData04`, `SnakyCertificate_CacheData05`, `SnakyCertificate_CacheData06`, `SnakyCertificate_CacheData07`, `SnakyCertificate_CacheData08`, `SnakyCertificate_CacheData09`, `SnakyCertificate_CacheData10`, `SnakyCertificate_CacheData11`, `SnakyCertificate_CacheData12`, `SnakyCertificate_CacheData13`, `SnakyCertificate_CacheData14`, `SnakyCertificate_CacheData15`, `SnakyCertificate_Invariants`, `SnakyCertificate_Lists`, `SnakyCertificate_TableList`, `SnakyCertificate_TableValidity`.
--
--   **Imports.** It imports the published bundle `Def_SnakyCertificate`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SnakyCertificate.Check.cache_equation_600`, `OAI.SnakyCertificate.Check.cache_equation_601`, `OAI.SnakyCertificate.Check.cache_equation_602`, `OAI.SnakyCertificate.Check.cache_equation_603`, `OAI.SnakyCertificate.Check.cache_equation_604`, `OAI.SnakyCertificate.Check.cache_equation_605`, `OAI.SnakyCertificate.Check.cache_equation_606`, `OAI.SnakyCertificate.Check.cache_equation_607`, `OAI.SnakyCertificate.Check.cache_equation_608`, `OAI.SnakyCertificate.Check.cache_equation_609`, `OAI.SnakyCertificate.Check.cache_equation_610`, `OAI.SnakyCertificate.Check.cache_equation_611`, `OAI.SnakyCertificate.Check.cache_equation_612`, `OAI.SnakyCertificate.Check.cache_equation_613`, `OAI.SnakyCertificate.Check.cache_equation_614`, `OAI.SnakyCertificate.Check.cache_equation_615`, `OAI.SnakyCertificate.Check.cache_equations_range_0_144`, `OAI.SnakyCertificate.Check.cache_equations_range_144_304`, `OAI.SnakyCertificate.Check.cache_equations_range_304_464`, `OAI.SnakyCertificate.Check.cache_equations_range_384_464`, `OAI.SnakyCertificate.Check.cache_equations_range_464_544`, `OAI.SnakyCertificate.Check.cache_equations_range_544_576`, `OAI.SnakyCertificate.Check.cache_equations_range_576`, `OAI.SnakyCertificate.Check.cache_equations_range_592`, `OAI.SnakyCertificate.Check.cache_omits_557`, `OAI.SnakyCertificate.Check.cache_omits_595`, `OAI.SnakyCertificate.Check.cache_omits_603`, `OAI.SnakyCertificate.Check.cache_omits_615`, `OAI.SnakyCertificate.Check.cache_summary_557`, `OAI.SnakyCertificate.Check.cache_summary_595`, `OAI.SnakyCertificate.Check.cache_summary_603` and `OAI.SnakyCertificate.Check.cache_summary_615`; the proofs of `OAI.SnakyCertificate.Check.cache_equation_600`, `OAI.SnakyCertificate.Check.cache_equation_601`, `OAI.SnakyCertificate.Check.cache_equation_602`, `OAI.SnakyCertificate.Check.cache_equation_603`, `OAI.SnakyCertificate.Check.cache_equation_604`, `OAI.SnakyCertificate.Check.cache_equation_605`, `OAI.SnakyCertificate.Check.cache_equation_606`, `OAI.SnakyCertificate.Check.cache_equation_607`, `OAI.SnakyCertificate.Check.cache_equation_608`, `OAI.SnakyCertificate.Check.cache_equation_609`, `OAI.SnakyCertificate.Check.cache_equation_610`, `OAI.SnakyCertificate.Check.cache_equation_611`, `OAI.SnakyCertificate.Check.cache_equation_612`, `OAI.SnakyCertificate.Check.cache_equation_613`, `OAI.SnakyCertificate.Check.cache_equation_614`, `OAI.SnakyCertificate.Check.cache_equation_615`, `OAI.SnakyCertificate.Check.cache_equations_range_0_144`, `OAI.SnakyCertificate.Check.cache_equations_range_144_304`, `OAI.SnakyCertificate.Check.cache_equations_range_304_464`, `OAI.SnakyCertificate.Check.cache_equations_range_384_464`, `OAI.SnakyCertificate.Check.cache_equations_range_464_544`, `OAI.SnakyCertificate.Check.cache_equations_range_544_576`, `OAI.SnakyCertificate.Check.cache_equations_range_576`, `OAI.SnakyCertificate.Check.cache_equations_range_592`, `OAI.SnakyCertificate.Check.cache_omits_557`, `OAI.SnakyCertificate.Check.cache_omits_595`, `OAI.SnakyCertificate.Check.cache_omits_603`, `OAI.SnakyCertificate.Check.cache_omits_615`, `OAI.SnakyCertificate.Check.cache_summary_557`, `OAI.SnakyCertificate.Check.cache_summary_595`, `OAI.SnakyCertificate.Check.cache_summary_603`, `OAI.SnakyCertificate.Check.cache_summary_615` and `OAI.SnakyCertificate.certificate_correct`.
-- source:
--   OpenAI, Snaky in 21 Maker moves, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 187; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_SnakyCertificate

section
-- module Solutions.OAIQ114_SC.Compat
attribute [-instance] _root_.OAI.SnakyCertificate.digitModulus_neZero _root_.OAI.SnakyCertificate.rotationModulus_neZero
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
-- module Solutions.OAIQ114_SC.SnakyCertificate_Lists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def mergeFuel : ℕ → List Cell → List Cell → List Cell
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if x = y then x :: mergeFuel n xs ys
    else if toLex x < toLex y then x :: mergeFuel n xs (y :: ys)
    else y :: mergeFuel n (x :: xs) ys

def mergeUnion (xs ys : List Cell) : List Cell :=
  mergeFuel (xs.length + ys.length) xs ys

structure ListRow where
  A : List Cell
  H : List Cell
  height : ℕ
  deriving DecidableEq

def denote (d : ListRow) : RowData := ⟨d.A.toFinset, d.H.toFinset, d.height⟩

def keyPlace (t : Term) (p : Cell) : Cell :=
  placement t.rotation t.shift p

def sortFuel : ℕ → List Cell → List Cell
  | 0, xs => xs
  | n + 1, xs =>
    if xs.length ≤ 1 then xs else
      mergeUnion (sortFuel n (xs.take (xs.length / 2)))
        (sortFuel n (xs.drop (xs.length / 2)))

def sorted (xs : List Cell) : List Cell := sortFuel xs.length xs

def place (t : Term) (d : ListRow) : ListRow :=
  ⟨sorted (d.A.map (keyPlace t)), sorted (d.H.map (keyPlace t)), d.height⟩

def unions (xs : List (List Cell)) : List Cell := xs.foldr mergeUnion []

def common (xs : List (List Cell)) : List Cell :=
  match xs with
  | [] => []
  | x :: rest => rest.foldr (· ∩ ·) x

def fork (ds : List ListRow) : ListRow :=
  ⟨(mergeUnion (unions (ds.map ListRow.A)) (common (ds.map ListRow.H))).filter
      (fun p => decide (p ≠ origin)),
   mergeUnion [origin] (unions (ds.map ListRow.H)),
   1 + (ds.map ListRow.height).foldr max 0⟩

@[simp] theorem toFinset_inter_cell (xs ys : List Cell) :
    (xs ∩ ys).toFinset = xs.toFinset ∩ ys.toFinset := by
  ext p; simp

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_0_A_part0 : List Cell := [(1, 0), (2, 0), (3, 0), (3, 1), (4, 1)]

def cache_0_A : List Cell := cache_0_A_part0

def cache_0_H_part0 : List Cell := [(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)]

def cache_0_H : List Cell := cache_0_H_part0

def cache_0 : ListRow := ⟨cache_0_A, cache_0_H, 1⟩

def cache_1_A_part0 : List Cell := [(-1, 0), (1, 0), (2, 0), (2, 1), (3, 1)]

def cache_1_A : List Cell := cache_1_A_part0

def cache_1_H_part0 : List Cell := [(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 1)]

def cache_1_H : List Cell := cache_1_H_part0

def cache_1 : ListRow := ⟨cache_1_A, cache_1_H, 1⟩

def cache_2_A_part0 : List Cell := [(-2, 0), (-1, 0), (1, 0), (1, 1), (2, 1)]

def cache_2_A : List Cell := cache_2_A_part0

def cache_2_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)]

def cache_2_H : List Cell := cache_2_H_part0

def cache_2 : ListRow := ⟨cache_2_A, cache_2_H, 1⟩

def cache_3_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (0, 1), (1, 1)]

def cache_3_A : List Cell := cache_3_A_part0

def cache_3_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)]

def cache_3_H : List Cell := cache_3_H_part0

def cache_3 : ListRow := ⟨cache_3_A, cache_3_H, 1⟩

def cache_4_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, 0)]

def cache_4_A : List Cell := cache_4_A_part0

def cache_4_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, 0)]

def cache_4_H : List Cell := cache_4_H_part0

def cache_4 : ListRow := ⟨cache_4_A, cache_4_H, 1⟩

def cache_5_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)]

def cache_5_A : List Cell := cache_5_A_part0

def cache_5_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)]

def cache_5_H : List Cell := cache_5_H_part0

def cache_5 : ListRow := ⟨cache_5_A, cache_5_H, 1⟩

def cache_6_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)]

def cache_6_A : List Cell := cache_6_A_part0

def cache_6_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)]

def cache_6_H : List Cell := cache_6_H_part0

def cache_6 : ListRow := ⟨cache_6_A, cache_6_H, 2⟩

def cache_7_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)]

def cache_7_A : List Cell := cache_7_A_part0

def cache_7_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)]

def cache_7_H : List Cell := cache_7_H_part0

def cache_7 : ListRow := ⟨cache_7_A, cache_7_H, 3⟩

def cache_8_A_part0 : List Cell := [(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_8_A : List Cell := cache_8_A_part0

def cache_8_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_8_H : List Cell := cache_8_H_part0

def cache_8 : ListRow := ⟨cache_8_A, cache_8_H, 3⟩

def cache_9_A_part0 : List Cell := [(-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)]

def cache_9_A : List Cell := cache_9_A_part0

def cache_9_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0)]

def cache_9_H : List Cell := cache_9_H_part0

def cache_9 : ListRow := ⟨cache_9_A, cache_9_H, 3⟩

def cache_10_A_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-1, -1), (-1, 0)]

def cache_10_A : List Cell := cache_10_A_part0

def cache_10_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0)]

def cache_10_H : List Cell := cache_10_H_part0

def cache_10 : ListRow := ⟨cache_10_A, cache_10_H, 2⟩

def cache_11_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)]

def cache_11_A : List Cell := cache_11_A_part0

def cache_11_H_part0 : List Cell := [(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, 0)]

def cache_11_H : List Cell := cache_11_H_part0

def cache_11 : ListRow := ⟨cache_11_A, cache_11_H, 3⟩

def cache_12_A_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0)]

def cache_12_A : List Cell := cache_12_A_part0

def cache_12_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)]

def cache_12_H : List Cell := cache_12_H_part0

def cache_12 : ListRow := ⟨cache_12_A, cache_12_H, 2⟩

def cache_13_A_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)]

def cache_13_A : List Cell := cache_13_A_part0

def cache_13_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)]

def cache_13_H : List Cell := cache_13_H_part0

def cache_13 : ListRow := ⟨cache_13_A, cache_13_H, 3⟩

def cache_14_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)]

def cache_14_A : List Cell := cache_14_A_part0

def cache_14_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)]

def cache_14_H : List Cell := cache_14_H_part0

def cache_14 : ListRow := ⟨cache_14_A, cache_14_H, 2⟩

def cache_15_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)]

def cache_15_A : List Cell := cache_15_A_part0

def cache_15_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)]

def cache_15_H : List Cell := cache_15_H_part0

def cache_15 : ListRow := ⟨cache_15_A, cache_15_H, 2⟩

def cache_16_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, 0), (2, 0)]

def cache_16_A : List Cell := cache_16_A_part0

def cache_16_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)]

def cache_16_H : List Cell := cache_16_H_part0

def cache_16 : ListRow := ⟨cache_16_A, cache_16_H, 2⟩

def cache_17_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)]

def cache_17_A : List Cell := cache_17_A_part0

def cache_17_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)]

def cache_17_H : List Cell := cache_17_H_part0

def cache_17 : ListRow := ⟨cache_17_A, cache_17_H, 2⟩

def cache_18_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)]

def cache_18_A : List Cell := cache_18_A_part0

def cache_18_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)]

def cache_18_H : List Cell := cache_18_H_part0

def cache_18 : ListRow := ⟨cache_18_A, cache_18_H, 2⟩

def cache_19_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0), (1, 0), (1, 1)]

def cache_19_A : List Cell := cache_19_A_part0

def cache_19_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)]

def cache_19_H : List Cell := cache_19_H_part0

def cache_19 : ListRow := ⟨cache_19_A, cache_19_H, 3⟩

def cache_20_A_part0 : List Cell := [(-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 1)]

def cache_20_A : List Cell := cache_20_A_part0

def cache_20_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)]

def cache_20_H : List Cell := cache_20_H_part0

def cache_20 : ListRow := ⟨cache_20_A, cache_20_H, 3⟩

def cache_21_A_part0 : List Cell := [(-3, -1), (-2, 0), (-1, 0), (1, 0), (1, 1)]

def cache_21_A : List Cell := cache_21_A_part0

def cache_21_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)]

def cache_21_H : List Cell := cache_21_H_part0

def cache_21 : ListRow := ⟨cache_21_A, cache_21_H, 3⟩

def cache_22_A_part0 : List Cell := [(-2, 0), (-1, 0), (0, 1), (1, 1), (2, 1)]

def cache_22_A : List Cell := cache_22_A_part0

def cache_22_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)]

def cache_22_H : List Cell := cache_22_H_part0

def cache_22 : ListRow := ⟨cache_22_A, cache_22_H, 2⟩

def cache_23_A_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, 0)]

def cache_23_A : List Cell := cache_23_A_part0

def cache_23_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)]

def cache_23_H : List Cell := cache_23_H_part0

def cache_23 : ListRow := ⟨cache_23_A, cache_23_H, 2⟩

def cache_24_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0)]

def cache_24_A : List Cell := cache_24_A_part0

def cache_24_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)]

def cache_24_H : List Cell := cache_24_H_part0

def cache_24 : ListRow := ⟨cache_24_A, cache_24_H, 3⟩

def cache_25_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0)]

def cache_25_A : List Cell := cache_25_A_part0

def cache_25_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)]

def cache_25_H : List Cell := cache_25_H_part0

def cache_25 : ListRow := ⟨cache_25_A, cache_25_H, 3⟩

def cache_26_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0), (-1, 1), (1, 0), (1, 1)]

def cache_26_A : List Cell := cache_26_A_part0

def cache_26_H_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1)]

def cache_26_H : List Cell := cache_26_H_part0

def cache_26 : ListRow := ⟨cache_26_A, cache_26_H, 3⟩

def cache_27_A_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0)]

def cache_27_A : List Cell := cache_27_A_part0

def cache_27_H_part0 : List Cell := [(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)]

def cache_27_H : List Cell := cache_27_H_part0

def cache_27 : ListRow := ⟨cache_27_A, cache_27_H, 3⟩

def cache_28_A_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, 0)]

def cache_28_A : List Cell := cache_28_A_part0

def cache_28_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_28_H : List Cell := cache_28_H_part0

def cache_28 : ListRow := ⟨cache_28_A, cache_28_H, 3⟩

def cache_29_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (4, -1)]

def cache_29_A : List Cell := cache_29_A_part0

def cache_29_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_29_H : List Cell := cache_29_H_part0

def cache_29 : ListRow := ⟨cache_29_A, cache_29_H, 3⟩

def cache_30_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, 0)]

def cache_30_A : List Cell := cache_30_A_part0

def cache_30_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)]

def cache_30_H : List Cell := cache_30_H_part0

def cache_30 : ListRow := ⟨cache_30_A, cache_30_H, 3⟩

def cache_31_A_part0 : List Cell := [(-2, 0), (-1, 0), (0, 1), (1, 1)]

def cache_31_A : List Cell := cache_31_A_part0

def cache_31_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)]

def cache_31_H : List Cell := cache_31_H_part0

def cache_31 : ListRow := ⟨cache_31_A, cache_31_H, 3⟩

def cache_32_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_32_A : List Cell := cache_32_A_part0

def cache_32_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_32_H : List Cell := cache_32_H_part0

def cache_32 : ListRow := ⟨cache_32_A, cache_32_H, 3⟩

def cache_33_A_part0 : List Cell := [(-1, 0), (1, 0), (1, 1), (2, 1)]

def cache_33_A : List Cell := cache_33_A_part0

def cache_33_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (4, 1)]

def cache_33_H : List Cell := cache_33_H_part0

def cache_33 : ListRow := ⟨cache_33_A, cache_33_H, 3⟩

def cache_34_A_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)]

def cache_34_A : List Cell := cache_34_A_part0

def cache_34_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_34_H : List Cell := cache_34_H_part0

def cache_34 : ListRow := ⟨cache_34_A, cache_34_H, 3⟩

def cache_35_A_part0 : List Cell := [(-1, 0), (1, 0), (1, 1), (2, 1)]

def cache_35_A : List Cell := cache_35_A_part0

def cache_35_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 1)]

def cache_35_H : List Cell := cache_35_H_part0

def cache_35 : ListRow := ⟨cache_35_A, cache_35_H, 3⟩

def cache_36_A_part0 : List Cell := [(1, 0), (2, 0), (2, 1), (3, 1)]

def cache_36_A : List Cell := cache_36_A_part0

def cache_36_H_part0 : List Cell := [(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)]

def cache_36_H : List Cell := cache_36_H_part0

def cache_36 : ListRow := ⟨cache_36_A, cache_36_H, 3⟩

def cache_37_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)]

def cache_37_A : List Cell := cache_37_A_part0

def cache_37_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_37_H : List Cell := cache_37_H_part0

def cache_37 : ListRow := ⟨cache_37_A, cache_37_H, 3⟩

def cache_38_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, 0)]

def cache_38_A : List Cell := cache_38_A_part0

def cache_38_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)]

def cache_38_H : List Cell := cache_38_H_part0

def cache_38 : ListRow := ⟨cache_38_A, cache_38_H, 3⟩

def cache_39_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, 0)]

def cache_39_A : List Cell := cache_39_A_part0

def cache_39_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_39_H : List Cell := cache_39_H_part0

def cache_39 : ListRow := ⟨cache_39_A, cache_39_H, 3⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_40_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (1, 0)]

def cache_40_A : List Cell := cache_40_A_part0

def cache_40_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)]

def cache_40_H : List Cell := cache_40_H_part0

def cache_40 : ListRow := ⟨cache_40_A, cache_40_H, 3⟩

def cache_41_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (1, -1), (3, -1)]

def cache_41_A : List Cell := cache_41_A_part0

def cache_41_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)]

def cache_41_H : List Cell := cache_41_H_part0

def cache_41 : ListRow := ⟨cache_41_A, cache_41_H, 3⟩

def cache_42_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (1, 0)]

def cache_42_A : List Cell := cache_42_A_part0

def cache_42_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)]

def cache_42_H : List Cell := cache_42_H_part0

def cache_42 : ListRow := ⟨cache_42_A, cache_42_H, 3⟩

def cache_43_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (2, -1), (3, -1)]

def cache_43_A : List Cell := cache_43_A_part0

def cache_43_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)]

def cache_43_H : List Cell := cache_43_H_part0

def cache_43 : ListRow := ⟨cache_43_A, cache_43_H, 3⟩

def cache_44_A_part0 : List Cell := [(-4, 0), (-4, 1), (-3, 0), (-2, 0), (-1, 0)]

def cache_44_A : List Cell := cache_44_A_part0

def cache_44_H_part0 : List Cell := [(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)]

def cache_44_H : List Cell := cache_44_H_part0

def cache_44 : ListRow := ⟨cache_44_A, cache_44_H, 4⟩

def cache_45_A_part0 : List Cell := [(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)]

def cache_45_A : List Cell := cache_45_A_part0

def cache_45_H_part0 : List Cell := [(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)]

def cache_45_H : List Cell := cache_45_H_part0

def cache_45 : ListRow := ⟨cache_45_A, cache_45_H, 4⟩

def cache_46_A_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_46_A : List Cell := cache_46_A_part0

def cache_46_H_part0 : List Cell := [(-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)]

def cache_46_H : List Cell := cache_46_H_part0

def cache_46 : ListRow := ⟨cache_46_A, cache_46_H, 4⟩

def cache_47_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)]

def cache_47_A : List Cell := cache_47_A_part0

def cache_47_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)]

def cache_47_H : List Cell := cache_47_H_part0

def cache_47 : ListRow := ⟨cache_47_A, cache_47_H, 3⟩

def cache_48_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0)]

def cache_48_A : List Cell := cache_48_A_part0

def cache_48_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)]

def cache_48_H : List Cell := cache_48_H_part0

def cache_48 : ListRow := ⟨cache_48_A, cache_48_H, 3⟩

def cache_49_A_part0 : List Cell := [(-1, -4), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_49_A : List Cell := cache_49_A_part0

def cache_49_H_part0 : List Cell := [(-1, -4), (-1, -3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)]

def cache_49_H : List Cell := cache_49_H_part0

def cache_49 : ListRow := ⟨cache_49_A, cache_49_H, 4⟩

def cache_50_A_part0 : List Cell := [(-1, 0), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_50_A : List Cell := cache_50_A_part0

def cache_50_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)]

def cache_50_H : List Cell := cache_50_H_part0

def cache_50 : ListRow := ⟨cache_50_A, cache_50_H, 4⟩

def cache_51_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, -1), (-2, 0), (0, -1)]

def cache_51_A : List Cell := cache_51_A_part0

def cache_51_H_part0 : List Cell := [(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)]

def cache_51_H : List Cell := cache_51_H_part0

def cache_51 : ListRow := ⟨cache_51_A, cache_51_H, 4⟩

def cache_52_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)]

def cache_52_A : List Cell := cache_52_A_part0

def cache_52_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)]

def cache_52_H : List Cell := cache_52_H_part0

def cache_52 : ListRow := ⟨cache_52_A, cache_52_H, 2⟩

def cache_53_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)]

def cache_53_A : List Cell := cache_53_A_part0

def cache_53_H_part0 : List Cell := [(-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)]

def cache_53_H : List Cell := cache_53_H_part0

def cache_53 : ListRow := ⟨cache_53_A, cache_53_H, 3⟩

def cache_54_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, 0), (-1, 0)]

def cache_54_A : List Cell := cache_54_A_part0

def cache_54_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)]

def cache_54_H : List Cell := cache_54_H_part0

def cache_54 : ListRow := ⟨cache_54_A, cache_54_H, 3⟩

def cache_55_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_55_A : List Cell := cache_55_A_part0

def cache_55_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)]

def cache_55_H : List Cell := cache_55_H_part0

def cache_55 : ListRow := ⟨cache_55_A, cache_55_H, 4⟩

def cache_56_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_56_A : List Cell := cache_56_A_part0

def cache_56_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)]

def cache_56_H : List Cell := cache_56_H_part0

def cache_56 : ListRow := ⟨cache_56_A, cache_56_H, 4⟩

def cache_57_A_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)]

def cache_57_A : List Cell := cache_57_A_part0

def cache_57_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]

def cache_57_H : List Cell := cache_57_H_part0

def cache_57 : ListRow := ⟨cache_57_A, cache_57_H, 4⟩

def cache_58_A_part0 : List Cell := [(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)]

def cache_58_A : List Cell := cache_58_A_part0

def cache_58_H_part0 : List Cell := [(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]

def cache_58_H : List Cell := cache_58_H_part0

def cache_58 : ListRow := ⟨cache_58_A, cache_58_H, 4⟩

def cache_59_A_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)]

def cache_59_A : List Cell := cache_59_A_part0

def cache_59_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)]

def cache_59_H : List Cell := cache_59_H_part0

def cache_59 : ListRow := ⟨cache_59_A, cache_59_H, 4⟩

def cache_60_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0), (1, 0)]

def cache_60_A : List Cell := cache_60_A_part0

def cache_60_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)]

def cache_60_H : List Cell := cache_60_H_part0

def cache_60 : ListRow := ⟨cache_60_A, cache_60_H, 5⟩

def cache_61_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -1)]

def cache_61_A : List Cell := cache_61_A_part0

def cache_61_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0)]

def cache_61_H : List Cell := cache_61_H_part0

def cache_61 : ListRow := ⟨cache_61_A, cache_61_H, 3⟩

def cache_62_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)]

def cache_62_A : List Cell := cache_62_A_part0

def cache_62_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, 0)]

def cache_62_H : List Cell := cache_62_H_part0

def cache_62 : ListRow := ⟨cache_62_A, cache_62_H, 4⟩

def cache_63_A_part0 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1)]

def cache_63_A : List Cell := cache_63_A_part0

def cache_63_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1)]

def cache_63_H : List Cell := cache_63_H_part0

def cache_63 : ListRow := ⟨cache_63_A, cache_63_H, 5⟩

def cache_64_A_part0 : List Cell := [(0, 1), (1, 1), (2, 1), (3, 1)]

def cache_64_A : List Cell := cache_64_A_part0

def cache_64_H_part0 : List Cell := [(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)]

def cache_64_H : List Cell := cache_64_H_part0

def cache_64 : ListRow := ⟨cache_64_A, cache_64_H, 5⟩

def cache_65_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_65_A : List Cell := cache_65_A_part0

def cache_65_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_65_H : List Cell := cache_65_H_part0

def cache_65 : ListRow := ⟨cache_65_A, cache_65_H, 5⟩

def cache_66_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)]

def cache_66_A : List Cell := cache_66_A_part0

def cache_66_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)]

def cache_66_H : List Cell := cache_66_H_part0

def cache_66 : ListRow := ⟨cache_66_A, cache_66_H, 4⟩

def cache_67_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_67_A : List Cell := cache_67_A_part0

def cache_67_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_67_H : List Cell := cache_67_H_part0

def cache_67 : ListRow := ⟨cache_67_A, cache_67_H, 4⟩

def cache_68_A_part0 : List Cell := [(-3, 0), (-3, 1), (-2, 0), (-1, 0)]

def cache_68_A : List Cell := cache_68_A_part0

def cache_68_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_68_H : List Cell := cache_68_H_part0

def cache_68 : ListRow := ⟨cache_68_A, cache_68_H, 5⟩

def cache_69_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (4, 1)]

def cache_69_A : List Cell := cache_69_A_part0

def cache_69_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 1), (2, 2), (3, 1), (4, 1)]

def cache_69_H : List Cell := cache_69_H_part0

def cache_69 : ListRow := ⟨cache_69_A, cache_69_H, 4⟩

def cache_70_A_part0 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (4, -1)]

def cache_70_A : List Cell := cache_70_A_part0

def cache_70_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_70_H : List Cell := cache_70_H_part0

def cache_70 : ListRow := ⟨cache_70_A, cache_70_H, 4⟩

def cache_71_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)]

def cache_71_A : List Cell := cache_71_A_part0

def cache_71_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (2, -1)]

def cache_71_H : List Cell := cache_71_H_part0

def cache_71 : ListRow := ⟨cache_71_A, cache_71_H, 3⟩

def cache_72_A_part0 : List Cell := [(-2, 1), (-1, 1), (-1, 2), (-1, 3), (0, 1), (1, 1)]

def cache_72_A : List Cell := cache_72_A_part0

def cache_72_H_part0 : List Cell := [(-3, 1), (-2, 1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)]

def cache_72_H : List Cell := cache_72_H_part0

def cache_72 : ListRow := ⟨cache_72_A, cache_72_H, 4⟩

def cache_73_A_part0 : List Cell := [(-1, 1), (0, -3), (0, -2), (0, -1)]

def cache_73_A : List Cell := cache_73_A_part0

def cache_73_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2)]

def cache_73_H : List Cell := cache_73_H_part0

def cache_73 : ListRow := ⟨cache_73_A, cache_73_H, 5⟩

def cache_74_A_part0 : List Cell := [(-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2), (2, -2)]

def cache_74_A : List Cell := cache_74_A_part0

def cache_74_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (2, -2)]

def cache_74_H : List Cell := cache_74_H_part0

def cache_74 : ListRow := ⟨cache_74_A, cache_74_H, 4⟩

def cache_75_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0), (2, -1)]

def cache_75_A : List Cell := cache_75_A_part0

def cache_75_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_75_H : List Cell := cache_75_H_part0

def cache_75 : ListRow := ⟨cache_75_A, cache_75_H, 4⟩

def cache_76_A_part0 : List Cell := [(-1, 0), (0, -1), (1, 0), (1, 1), (1, 2), (2, 1)]

def cache_76_A : List Cell := cache_76_A_part0

def cache_76_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1), (4, 1)]

def cache_76_H : List Cell := cache_76_H_part0

def cache_76 : ListRow := ⟨cache_76_A, cache_76_H, 3⟩

def cache_77_A_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1)]

def cache_77_A : List Cell := cache_77_A_part0

def cache_77_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)]

def cache_77_H : List Cell := cache_77_H_part0

def cache_77 : ListRow := ⟨cache_77_A, cache_77_H, 3⟩

def cache_78_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, -1), (2, -1), (3, -1)]

def cache_78_A : List Cell := cache_78_A_part0

def cache_78_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_78_H : List Cell := cache_78_H_part0

def cache_78 : ListRow := ⟨cache_78_A, cache_78_H, 3⟩

def cache_79_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)]

def cache_79_A : List Cell := cache_79_A_part0

def cache_79_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)]

def cache_79_H : List Cell := cache_79_H_part0

def cache_79 : ListRow := ⟨cache_79_A, cache_79_H, 4⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_80_A_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)]

def cache_80_A : List Cell := cache_80_A_part0

def cache_80_H_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)]

def cache_80_H : List Cell := cache_80_H_part0

def cache_80 : ListRow := ⟨cache_80_A, cache_80_H, 4⟩

def cache_81_A_part0 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1), (3, -1), (4, -1)]

def cache_81_A : List Cell := cache_81_A_part0

def cache_81_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_81_H : List Cell := cache_81_H_part0

def cache_81 : ListRow := ⟨cache_81_A, cache_81_H, 4⟩

def cache_82_A_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_82_A : List Cell := cache_82_A_part0

def cache_82_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_82_H : List Cell := cache_82_H_part0

def cache_82 : ListRow := ⟨cache_82_A, cache_82_H, 4⟩

def cache_83_A_part0 : List Cell := [(0, -1), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_83_A : List Cell := cache_83_A_part0

def cache_83_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (3, -1), (4, -1)]

def cache_83_H : List Cell := cache_83_H_part0

def cache_83 : ListRow := ⟨cache_83_A, cache_83_H, 5⟩

def cache_84_A_part0 : List Cell := [(0, -1), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_84_A : List Cell := cache_84_A_part0

def cache_84_H_part0 : List Cell := [(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, 0), (4, 0)]

def cache_84_H : List Cell := cache_84_H_part0

def cache_84 : ListRow := ⟨cache_84_A, cache_84_H, 5⟩

def cache_85_A_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)]

def cache_85_A : List Cell := cache_85_A_part0

def cache_85_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)]

def cache_85_H : List Cell := cache_85_H_part0

def cache_85 : ListRow := ⟨cache_85_A, cache_85_H, 4⟩

def cache_86_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)]

def cache_86_A : List Cell := cache_86_A_part0

def cache_86_H_part0 : List Cell := [(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)]

def cache_86_H : List Cell := cache_86_H_part0

def cache_86 : ListRow := ⟨cache_86_A, cache_86_H, 5⟩

def cache_87_A_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -1)]

def cache_87_A : List Cell := cache_87_A_part0

def cache_87_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_87_H : List Cell := cache_87_H_part0

def cache_87 : ListRow := ⟨cache_87_A, cache_87_H, 4⟩

def cache_88_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)]

def cache_88_A : List Cell := cache_88_A_part0

def cache_88_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)]

def cache_88_H : List Cell := cache_88_H_part0

def cache_88 : ListRow := ⟨cache_88_A, cache_88_H, 5⟩

def cache_89_A_part0 : List Cell := [(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_89_A : List Cell := cache_89_A_part0

def cache_89_H_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]

def cache_89_H : List Cell := cache_89_H_part0

def cache_89 : ListRow := ⟨cache_89_A, cache_89_H, 4⟩

def cache_90_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, 0)]

def cache_90_A : List Cell := cache_90_A_part0

def cache_90_H_part0 : List Cell := [(-5, -1), (-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)]

def cache_90_H : List Cell := cache_90_H_part0

def cache_90 : ListRow := ⟨cache_90_A, cache_90_H, 4⟩

def cache_91_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (4, -1)]

def cache_91_A : List Cell := cache_91_A_part0

def cache_91_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)]

def cache_91_H : List Cell := cache_91_H_part0

def cache_91 : ListRow := ⟨cache_91_A, cache_91_H, 5⟩

def cache_92_A_part0 : List Cell := [(-3, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_92_A : List Cell := cache_92_A_part0

def cache_92_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_92_H : List Cell := cache_92_H_part0

def cache_92 : ListRow := ⟨cache_92_A, cache_92_H, 4⟩

def cache_93_A_part0 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1), (2, 0), (3, -1), (3, 0)]

def cache_93_A : List Cell := cache_93_A_part0

def cache_93_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)]

def cache_93_H : List Cell := cache_93_H_part0

def cache_93 : ListRow := ⟨cache_93_A, cache_93_H, 4⟩

def cache_94_A_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1)]

def cache_94_A : List Cell := cache_94_A_part0

def cache_94_H_part0 : List Cell := [(-2, -2), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1)]

def cache_94_H : List Cell := cache_94_H_part0

def cache_94 : ListRow := ⟨cache_94_A, cache_94_H, 4⟩

def cache_95_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (2, 0)]

def cache_95_A : List Cell := cache_95_A_part0

def cache_95_H_part0 : List Cell := [(-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)]

def cache_95_H : List Cell := cache_95_H_part0

def cache_95 : ListRow := ⟨cache_95_A, cache_95_H, 4⟩

def cache_96_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)]

def cache_96_A : List Cell := cache_96_A_part0

def cache_96_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)]

def cache_96_H : List Cell := cache_96_H_part0

def cache_96 : ListRow := ⟨cache_96_A, cache_96_H, 5⟩

def cache_97_A_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)]

def cache_97_A : List Cell := cache_97_A_part0

def cache_97_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_97_H : List Cell := cache_97_H_part0

def cache_97 : ListRow := ⟨cache_97_A, cache_97_H, 5⟩

def cache_98_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)]

def cache_98_A : List Cell := cache_98_A_part0

def cache_98_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)]

def cache_98_H : List Cell := cache_98_H_part0

def cache_98 : ListRow := ⟨cache_98_A, cache_98_H, 5⟩

def cache_99_A_part0 : List Cell := [(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)]

def cache_99_A : List Cell := cache_99_A_part0

def cache_99_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_99_H : List Cell := cache_99_H_part0

def cache_99 : ListRow := ⟨cache_99_A, cache_99_H, 4⟩

def cache_100_A_part0 : List Cell := [(-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1)]

def cache_100_A : List Cell := cache_100_A_part0

def cache_100_H_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)]

def cache_100_H : List Cell := cache_100_H_part0

def cache_100 : ListRow := ⟨cache_100_A, cache_100_H, 4⟩

def cache_101_A_part0 : List Cell := [(-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 1)]

def cache_101_A : List Cell := cache_101_A_part0

def cache_101_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_101_H : List Cell := cache_101_H_part0

def cache_101 : ListRow := ⟨cache_101_A, cache_101_H, 4⟩

def cache_102_A_part0 : List Cell := [(-1, 0), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_102_A : List Cell := cache_102_A_part0

def cache_102_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)]

def cache_102_H : List Cell := cache_102_H_part0

def cache_102 : ListRow := ⟨cache_102_A, cache_102_H, 4⟩

def cache_103_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (3, -1)]

def cache_103_A : List Cell := cache_103_A_part0

def cache_103_H_part0 : List Cell := [(-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (4, -1)]

def cache_103_H : List Cell := cache_103_H_part0

def cache_103 : ListRow := ⟨cache_103_A, cache_103_H, 4⟩

def cache_104_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, -1)]

def cache_104_A : List Cell := cache_104_A_part0

def cache_104_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_104_H : List Cell := cache_104_H_part0

def cache_104 : ListRow := ⟨cache_104_A, cache_104_H, 5⟩

def cache_105_A_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_105_A : List Cell := cache_105_A_part0

def cache_105_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)]

def cache_105_H : List Cell := cache_105_H_part0

def cache_105 : ListRow := ⟨cache_105_A, cache_105_H, 4⟩

def cache_106_A_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_106_A : List Cell := cache_106_A_part0

def cache_106_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_106_H : List Cell := cache_106_H_part0

def cache_106 : ListRow := ⟨cache_106_A, cache_106_H, 4⟩

def cache_107_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_107_A : List Cell := cache_107_A_part0

def cache_107_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_107_H : List Cell := cache_107_H_part0

def cache_107 : ListRow := ⟨cache_107_A, cache_107_H, 6⟩

def cache_108_A_part0 : List Cell := [(-4, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_108_A : List Cell := cache_108_A_part0

def cache_108_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_108_H : List Cell := cache_108_H_part0

def cache_108 : ListRow := ⟨cache_108_A, cache_108_H, 6⟩

def cache_109_A_part0 : List Cell := [(-4, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_109_A : List Cell := cache_109_A_part0

def cache_109_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_109_H : List Cell := cache_109_H_part0

def cache_109 : ListRow := ⟨cache_109_A, cache_109_H, 5⟩

def cache_110_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0), (1, 0)]

def cache_110_A : List Cell := cache_110_A_part0

def cache_110_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_110_H : List Cell := cache_110_H_part0

def cache_110 : ListRow := ⟨cache_110_A, cache_110_H, 6⟩

def cache_111_A_part0 : List Cell := [(1, 0), (1, 1), (1, 2), (1, 3)]

def cache_111_A : List Cell := cache_111_A_part0

def cache_111_H_part0 : List Cell := [(-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0), (4, 0)]

def cache_111_H : List Cell := cache_111_H_part0

def cache_111 : ListRow := ⟨cache_111_A, cache_111_H, 6⟩

def cache_112_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, 1), (2, 0), (2, 1)]

def cache_112_A : List Cell := cache_112_A_part0

def cache_112_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0)]

def cache_112_H : List Cell := cache_112_H_part0

def cache_112 : ListRow := ⟨cache_112_A, cache_112_H, 5⟩

def cache_113_A_part0 : List Cell := [(-1, -1), (0, -1), (1, 0), (1, 1), (2, 1), (3, 0)]

def cache_113_A : List Cell := cache_113_A_part0

def cache_113_H_part0 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)]

def cache_113_H : List Cell := cache_113_H_part0

def cache_113 : ListRow := ⟨cache_113_A, cache_113_H, 4⟩

def cache_114_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0), (1, 1)]

def cache_114_A : List Cell := cache_114_A_part0

def cache_114_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)]

def cache_114_H : List Cell := cache_114_H_part0

def cache_114 : ListRow := ⟨cache_114_A, cache_114_H, 5⟩

def cache_115_A_part0 : List Cell := [(-1, -3), (-1, -1), (-1, 0), (1, 0), (2, -1), (2, 0)]

def cache_115_A : List Cell := cache_115_A_part0

def cache_115_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)]

def cache_115_H : List Cell := cache_115_H_part0

def cache_115 : ListRow := ⟨cache_115_A, cache_115_H, 5⟩

def cache_116_A_part0 : List Cell := [(-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 1)]

def cache_116_A : List Cell := cache_116_A_part0

def cache_116_H_part0 : List Cell := [(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)]

def cache_116_H : List Cell := cache_116_H_part0

def cache_116 : ListRow := ⟨cache_116_A, cache_116_H, 4⟩

def cache_117_A_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)]

def cache_117_A : List Cell := cache_117_A_part0

def cache_117_H_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0)]

def cache_117_H : List Cell := cache_117_H_part0

def cache_117 : ListRow := ⟨cache_117_A, cache_117_H, 5⟩

def cache_118_A_part0 : List Cell := [(-2, -1), (-1, -4), (-1, -1), (0, -3), (0, -2), (0, -1)]

def cache_118_A : List Cell := cache_118_A_part0

def cache_118_H_part0 : List Cell := [(-2, -1), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, 0), (3, 0)]

def cache_118_H : List Cell := cache_118_H_part0

def cache_118 : ListRow := ⟨cache_118_A, cache_118_H, 4⟩

def cache_119_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0), (1, 0)]

def cache_119_A : List Cell := cache_119_A_part0

def cache_119_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)]

def cache_119_H : List Cell := cache_119_H_part0

def cache_119 : ListRow := ⟨cache_119_A, cache_119_H, 5⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_120_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 1)]

def cache_120_A : List Cell := cache_120_A_part0

def cache_120_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]

def cache_120_H : List Cell := cache_120_H_part0

def cache_120 : ListRow := ⟨cache_120_A, cache_120_H, 5⟩

def cache_121_A_part0 : List Cell := [(-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_121_A : List Cell := cache_121_A_part0

def cache_121_H_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1)]

def cache_121_H : List Cell := cache_121_H_part0

def cache_121 : ListRow := ⟨cache_121_A, cache_121_H, 4⟩

def cache_122_A_part0 : List Cell := [(0, -1), (1, 0), (2, 0), (3, 0)]

def cache_122_A : List Cell := cache_122_A_part0

def cache_122_H_part0 : List Cell := [(-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, 0), (4, 0)]

def cache_122_H : List Cell := cache_122_H_part0

def cache_122 : ListRow := ⟨cache_122_A, cache_122_H, 5⟩

def cache_123_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0), (1, 0)]

def cache_123_A : List Cell := cache_123_A_part0

def cache_123_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)]

def cache_123_H : List Cell := cache_123_H_part0

def cache_123 : ListRow := ⟨cache_123_A, cache_123_H, 6⟩

def cache_124_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1), (2, -1)]

def cache_124_A : List Cell := cache_124_A_part0

def cache_124_H_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)]

def cache_124_H : List Cell := cache_124_H_part0

def cache_124 : ListRow := ⟨cache_124_A, cache_124_H, 4⟩

def cache_125_A_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (1, 0)]

def cache_125_A : List Cell := cache_125_A_part0

def cache_125_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)]

def cache_125_H : List Cell := cache_125_H_part0

def cache_125 : ListRow := ⟨cache_125_A, cache_125_H, 4⟩

def cache_126_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_126_A : List Cell := cache_126_A_part0

def cache_126_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4)]

def cache_126_H : List Cell := cache_126_H_part0

def cache_126 : ListRow := ⟨cache_126_A, cache_126_H, 5⟩

def cache_127_A_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_127_A : List Cell := cache_127_A_part0

def cache_127_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_127_H : List Cell := cache_127_H_part0

def cache_127 : ListRow := ⟨cache_127_A, cache_127_H, 5⟩

def cache_128_A_part0 : List Cell := [(-2, 1), (-1, 0), (-1, 1), (0, 1), (1, 1)]

def cache_128_A : List Cell := cache_128_A_part0

def cache_128_H_part0 : List Cell := [(-4, 1), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)]

def cache_128_H : List Cell := cache_128_H_part0

def cache_128 : ListRow := ⟨cache_128_A, cache_128_H, 5⟩

def cache_129_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 0), (2, 0)]

def cache_129_A : List Cell := cache_129_A_part0

def cache_129_H_part0 : List Cell := [(-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)]

def cache_129_H : List Cell := cache_129_H_part0

def cache_129 : ListRow := ⟨cache_129_A, cache_129_H, 5⟩

def cache_130_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)]

def cache_130_A : List Cell := cache_130_A_part0

def cache_130_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)]

def cache_130_H : List Cell := cache_130_H_part0

def cache_130 : ListRow := ⟨cache_130_A, cache_130_H, 6⟩

def cache_131_A_part0 : List Cell := [(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_131_A : List Cell := cache_131_A_part0

def cache_131_H_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]

def cache_131_H : List Cell := cache_131_H_part0

def cache_131 : ListRow := ⟨cache_131_A, cache_131_H, 5⟩

def cache_132_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_132_A : List Cell := cache_132_A_part0

def cache_132_H_part0 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)]

def cache_132_H : List Cell := cache_132_H_part0

def cache_132 : ListRow := ⟨cache_132_A, cache_132_H, 5⟩

def cache_133_A_part0 : List Cell := [(-2, 0), (-1, -2), (0, -2), (0, -1), (0, 1)]

def cache_133_A : List Cell := cache_133_A_part0

def cache_133_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (3, 1)]

def cache_133_H : List Cell := cache_133_H_part0

def cache_133 : ListRow := ⟨cache_133_A, cache_133_H, 5⟩

def cache_134_A_part0 : List Cell := [(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)]

def cache_134_A : List Cell := cache_134_A_part0

def cache_134_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (3, 0)]

def cache_134_H : List Cell := cache_134_H_part0

def cache_134 : ListRow := ⟨cache_134_A, cache_134_H, 5⟩

def cache_135_A_part0 : List Cell := [(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)]

def cache_135_A : List Cell := cache_135_A_part0

def cache_135_H_part0 : List Cell := [(-6, 0), (-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_135_H : List Cell := cache_135_H_part0

def cache_135 : ListRow := ⟨cache_135_A, cache_135_H, 5⟩

def cache_136_A_part0 : List Cell := [(-2, -1), (-1, 2), (0, -1), (0, 1), (0, 2)]

def cache_136_A : List Cell := cache_136_A_part0

def cache_136_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (3, 0)]

def cache_136_H : List Cell := cache_136_H_part0

def cache_136 : ListRow := ⟨cache_136_A, cache_136_H, 5⟩

def cache_137_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, 0)]

def cache_137_A : List Cell := cache_137_A_part0

def cache_137_H_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_137_H : List Cell := cache_137_H_part0

def cache_137 : ListRow := ⟨cache_137_A, cache_137_H, 6⟩

def cache_138_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 2), (0, 2)]

def cache_138_A : List Cell := cache_138_A_part0

def cache_138_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)]

def cache_138_H : List Cell := cache_138_H_part0

def cache_138 : ListRow := ⟨cache_138_A, cache_138_H, 4⟩

def cache_139_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 2)]

def cache_139_A : List Cell := cache_139_A_part0

def cache_139_H_part0 : List Cell := [(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)]

def cache_139_H : List Cell := cache_139_H_part0

def cache_139 : ListRow := ⟨cache_139_A, cache_139_H, 4⟩

def cache_140_A_part0 : List Cell := [(-1, -1), (-1, 1), (0, -1), (0, 1), (0, 2)]

def cache_140_A : List Cell := cache_140_A_part0

def cache_140_H_part0 : List Cell := [(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)]

def cache_140_H : List Cell := cache_140_H_part0

def cache_140 : ListRow := ⟨cache_140_A, cache_140_H, 5⟩

def cache_141_A_part0 : List Cell := [(-5, 0), (-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_141_A : List Cell := cache_141_A_part0

def cache_141_H_part0 : List Cell := [(-6, 0), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]

def cache_141_H : List Cell := cache_141_H_part0

def cache_141 : ListRow := ⟨cache_141_A, cache_141_H, 4⟩

def cache_142_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2)]

def cache_142_A : List Cell := cache_142_A_part0

def cache_142_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)]

def cache_142_H : List Cell := cache_142_H_part0

def cache_142 : ListRow := ⟨cache_142_A, cache_142_H, 5⟩

def cache_143_A_part0 : List Cell := [(0, 1), (1, 1), (2, 1), (3, 1)]

def cache_143_A : List Cell := cache_143_A_part0

def cache_143_H_part0 : List Cell := [(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)]

def cache_143_H : List Cell := cache_143_H_part0

def cache_143 : ListRow := ⟨cache_143_A, cache_143_H, 7⟩

def cache_144_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_144_A : List Cell := cache_144_A_part0

def cache_144_H_part0 : List Cell := [(-6, 0), (-5, 0), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_144_H : List Cell := cache_144_H_part0

def cache_144 : ListRow := ⟨cache_144_A, cache_144_H, 6⟩

def cache_145_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3), (1, -2), (3, -1)]

def cache_145_A : List Cell := cache_145_A_part0

def cache_145_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)]

def cache_145_H : List Cell := cache_145_H_part0

def cache_145 : ListRow := ⟨cache_145_A, cache_145_H, 6⟩

def cache_146_A_part0 : List Cell := [(-2, -1), (-1, -2), (-1, -1), (-1, 0)]

def cache_146_A : List Cell := cache_146_A_part0

def cache_146_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)]

def cache_146_H : List Cell := cache_146_H_part0

def cache_146 : ListRow := ⟨cache_146_A, cache_146_H, 4⟩

def cache_147_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)]

def cache_147_A : List Cell := cache_147_A_part0

def cache_147_H_part0 : List Cell := [(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)]

def cache_147_H : List Cell := cache_147_H_part0

def cache_147 : ListRow := ⟨cache_147_A, cache_147_H, 5⟩

def cache_148_A_part0 : List Cell := [(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (1, -2)]

def cache_148_A : List Cell := cache_148_A_part0

def cache_148_H_part0 : List Cell := [(-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_148_H : List Cell := cache_148_H_part0

def cache_148 : ListRow := ⟨cache_148_A, cache_148_H, 6⟩

def cache_149_A_part0 : List Cell := [(-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, 1)]

def cache_149_A : List Cell := cache_149_A_part0

def cache_149_H_part0 : List Cell := [(-3, 1), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)]

def cache_149_H : List Cell := cache_149_H_part0

def cache_149 : ListRow := ⟨cache_149_A, cache_149_H, 4⟩

def cache_150_A_part0 : List Cell := [(-5, 0), (-4, -1), (-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_150_A : List Cell := cache_150_A_part0

def cache_150_H_part0 : List Cell := [(-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)]

def cache_150_H : List Cell := cache_150_H_part0

def cache_150 : ListRow := ⟨cache_150_A, cache_150_H, 6⟩

def cache_151_A_part0 : List Cell := [(0, -3), (0, -2), (1, 0), (1, 1), (2, -2), (2, 0)]

def cache_151_A : List Cell := cache_151_A_part0

def cache_151_H_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (5, -1)]

def cache_151_H : List Cell := cache_151_H_part0

def cache_151 : ListRow := ⟨cache_151_A, cache_151_H, 5⟩

def cache_152_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (4, -1)]

def cache_152_A : List Cell := cache_152_A_part0

def cache_152_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_152_H : List Cell := cache_152_H_part0

def cache_152 : ListRow := ⟨cache_152_A, cache_152_H, 6⟩

def cache_153_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0)]

def cache_153_A : List Cell := cache_153_A_part0

def cache_153_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)]

def cache_153_H : List Cell := cache_153_H_part0

def cache_153 : ListRow := ⟨cache_153_A, cache_153_H, 5⟩

def cache_154_A_part0 : List Cell := [(1, 0), (2, 0), (3, 0), (4, 0)]

def cache_154_A : List Cell := cache_154_A_part0

def cache_154_H_part0 : List Cell := [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (6, 0)]

def cache_154_H : List Cell := cache_154_H_part0

def cache_154 : ListRow := ⟨cache_154_A, cache_154_H, 6⟩

def cache_155_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1)]

def cache_155_A : List Cell := cache_155_A_part0

def cache_155_H_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]

def cache_155_H : List Cell := cache_155_H_part0

def cache_155 : ListRow := ⟨cache_155_A, cache_155_H, 5⟩

def cache_156_A_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-1, -1), (-1, 0)]

def cache_156_A : List Cell := cache_156_A_part0

def cache_156_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)]

def cache_156_H : List Cell := cache_156_H_part0

def cache_156 : ListRow := ⟨cache_156_A, cache_156_H, 6⟩

def cache_157_A_part0 : List Cell := [(0, -1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_157_A : List Cell := cache_157_A_part0

def cache_157_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)]

def cache_157_H : List Cell := cache_157_H_part0

def cache_157 : ListRow := ⟨cache_157_A, cache_157_H, 5⟩

def cache_158_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)]

def cache_158_A : List Cell := cache_158_A_part0

def cache_158_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (3, -1)]

def cache_158_H : List Cell := cache_158_H_part0

def cache_158 : ListRow := ⟨cache_158_A, cache_158_H, 5⟩

def cache_159_A_part0 : List Cell := [(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_159_A : List Cell := cache_159_A_part0

def cache_159_H_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)]

def cache_159_H : List Cell := cache_159_H_part0

def cache_159 : ListRow := ⟨cache_159_A, cache_159_H, 6⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_160_A_part0 : List Cell := [(1, 0), (1, 1), (1, 2), (2, 0), (3, 0)]

def cache_160_A : List Cell := cache_160_A_part0

def cache_160_H_part0 : List Cell := [(-1, -1), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_160_H : List Cell := cache_160_H_part0

def cache_160 : ListRow := ⟨cache_160_A, cache_160_H, 6⟩

def cache_161_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, 2)]

def cache_161_A : List Cell := cache_161_A_part0

def cache_161_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)]

def cache_161_H : List Cell := cache_161_H_part0

def cache_161 : ListRow := ⟨cache_161_A, cache_161_H, 6⟩

def cache_162_A_part0 : List Cell := [(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_162_A : List Cell := cache_162_A_part0

def cache_162_H_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

def cache_162_H : List Cell := cache_162_H_part0

def cache_162 : ListRow := ⟨cache_162_A, cache_162_H, 6⟩

def cache_163_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_163_A : List Cell := cache_163_A_part0

def cache_163_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_163_H : List Cell := cache_163_H_part0

def cache_163 : ListRow := ⟨cache_163_A, cache_163_H, 5⟩

def cache_164_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)]

def cache_164_A : List Cell := cache_164_A_part0

def cache_164_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_164_H : List Cell := cache_164_H_part0

def cache_164 : ListRow := ⟨cache_164_A, cache_164_H, 7⟩

def cache_165_A_part0 : List Cell := [(0, 1), (1, 1), (1, 2), (1, 3), (2, 1)]

def cache_165_A : List Cell := cache_165_A_part0

def cache_165_H_part0 : List Cell := [(-1, 0), (0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)]

def cache_165_H : List Cell := cache_165_H_part0

def cache_165 : ListRow := ⟨cache_165_A, cache_165_H, 7⟩

def cache_166_A_part0 : List Cell := [(-1, -1), (-1, 0), (0, 2), (0, 3), (1, 0)]

def cache_166_A : List Cell := cache_166_A_part0

def cache_166_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_166_H : List Cell := cache_166_H_part0

def cache_166 : ListRow := ⟨cache_166_A, cache_166_H, 7⟩

def cache_167_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)]

def cache_167_A : List Cell := cache_167_A_part0

def cache_167_H_part0 : List Cell := [(-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]

def cache_167_H : List Cell := cache_167_H_part0

def cache_167 : ListRow := ⟨cache_167_A, cache_167_H, 5⟩

def cache_168_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, 0), (3, -1)]

def cache_168_A : List Cell := cache_168_A_part0

def cache_168_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_168_H : List Cell := cache_168_H_part0

def cache_168 : ListRow := ⟨cache_168_A, cache_168_H, 7⟩

def cache_169_A_part0 : List Cell := [(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_169_A : List Cell := cache_169_A_part0

def cache_169_H_part0 : List Cell := [(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_169_H : List Cell := cache_169_H_part0

def cache_169 : ListRow := ⟨cache_169_A, cache_169_H, 6⟩

def cache_170_A_part0 : List Cell := [(-4, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0)]

def cache_170_A : List Cell := cache_170_A_part0

def cache_170_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)]

def cache_170_H : List Cell := cache_170_H_part0

def cache_170 : ListRow := ⟨cache_170_A, cache_170_H, 6⟩

def cache_171_A_part0 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)]

def cache_171_A : List Cell := cache_171_A_part0

def cache_171_H_part0 : List Cell := [(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0)]

def cache_171_H : List Cell := cache_171_H_part0

def cache_171 : ListRow := ⟨cache_171_A, cache_171_H, 6⟩

def cache_172_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_172_A : List Cell := cache_172_A_part0

def cache_172_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_172_H : List Cell := cache_172_H_part0

def cache_172 : ListRow := ⟨cache_172_A, cache_172_H, 6⟩

def cache_173_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_173_A : List Cell := cache_173_A_part0

def cache_173_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_173_H : List Cell := cache_173_H_part0

def cache_173 : ListRow := ⟨cache_173_A, cache_173_H, 6⟩

def cache_174_A_part0 : List Cell := [(-1, -2), (-1, -1), (0, -3), (0, -2), (0, -1)]

def cache_174_A : List Cell := cache_174_A_part0

def cache_174_H_part0 : List Cell := [(-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)]

def cache_174_H : List Cell := cache_174_H_part0

def cache_174 : ListRow := ⟨cache_174_A, cache_174_H, 6⟩

def cache_175_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_175_A : List Cell := cache_175_A_part0

def cache_175_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)]

def cache_175_H : List Cell := cache_175_H_part0

def cache_175 : ListRow := ⟨cache_175_A, cache_175_H, 6⟩

def cache_176_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_176_A : List Cell := cache_176_A_part0

def cache_176_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_176_H : List Cell := cache_176_H_part0

def cache_176 : ListRow := ⟨cache_176_A, cache_176_H, 6⟩

def cache_177_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, -2), (2, 0)]

def cache_177_A : List Cell := cache_177_A_part0

def cache_177_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1)]

def cache_177_H : List Cell := cache_177_H_part0

def cache_177 : ListRow := ⟨cache_177_A, cache_177_H, 6⟩

def cache_178_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)]

def cache_178_A : List Cell := cache_178_A_part0

def cache_178_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)]

def cache_178_H : List Cell := cache_178_H_part0

def cache_178 : ListRow := ⟨cache_178_A, cache_178_H, 6⟩

def cache_179_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1)]

def cache_179_A : List Cell := cache_179_A_part0

def cache_179_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)]

def cache_179_H : List Cell := cache_179_H_part0

def cache_179 : ListRow := ⟨cache_179_A, cache_179_H, 7⟩

def cache_180_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1)]

def cache_180_A : List Cell := cache_180_A_part0

def cache_180_H_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

def cache_180_H : List Cell := cache_180_H_part0

def cache_180 : ListRow := ⟨cache_180_A, cache_180_H, 6⟩

def cache_181_A_part0 : List Cell := [(1, -2), (1, -1), (1, 0), (2, 1)]

def cache_181_A : List Cell := cache_181_A_part0

def cache_181_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)]

def cache_181_H : List Cell := cache_181_H_part0

def cache_181 : ListRow := ⟨cache_181_A, cache_181_H, 5⟩

def cache_182_A_part0 : List Cell := [(1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, 2)]

def cache_182_A : List Cell := cache_182_A_part0

def cache_182_H_part0 : List Cell := [(-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0)]

def cache_182_H : List Cell := cache_182_H_part0

def cache_182 : ListRow := ⟨cache_182_A, cache_182_H, 5⟩

def cache_183_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_183_A : List Cell := cache_183_A_part0

def cache_183_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)]

def cache_183_H : List Cell := cache_183_H_part0

def cache_183 : ListRow := ⟨cache_183_A, cache_183_H, 6⟩

def cache_184_A_part0 : List Cell := [(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1)]

def cache_184_A : List Cell := cache_184_A_part0

def cache_184_H_part0 : List Cell := [(-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1), (4, -1), (5, -1)]

def cache_184_H : List Cell := cache_184_H_part0

def cache_184 : ListRow := ⟨cache_184_A, cache_184_H, 4⟩

def cache_185_A_part0 : List Cell := [(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)]

def cache_185_A : List Cell := cache_185_A_part0

def cache_185_H_part0 : List Cell := [(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)]

def cache_185_H : List Cell := cache_185_H_part0

def cache_185 : ListRow := ⟨cache_185_A, cache_185_H, 6⟩

def cache_186_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_186_A : List Cell := cache_186_A_part0

def cache_186_H_part0 : List Cell := [(-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)]

def cache_186_H : List Cell := cache_186_H_part0

def cache_186 : ListRow := ⟨cache_186_A, cache_186_H, 5⟩

def cache_187_A_part0 : List Cell := [(0, -2), (0, -1), (1, -3), (1, -1), (2, -1), (3, -1)]

def cache_187_A : List Cell := cache_187_A_part0

def cache_187_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)]

def cache_187_H : List Cell := cache_187_H_part0

def cache_187 : ListRow := ⟨cache_187_A, cache_187_H, 7⟩

def cache_188_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -2), (4, -2), (4, -1)]

def cache_188_A : List Cell := cache_188_A_part0

def cache_188_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, 1)]

def cache_188_H : List Cell := cache_188_H_part0

def cache_188 : ListRow := ⟨cache_188_A, cache_188_H, 6⟩

def cache_189_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1)]

def cache_189_A : List Cell := cache_189_A_part0

def cache_189_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)]

def cache_189_H : List Cell := cache_189_H_part0

def cache_189 : ListRow := ⟨cache_189_A, cache_189_H, 6⟩

def cache_190_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, 0)]

def cache_190_A : List Cell := cache_190_A_part0

def cache_190_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1)]

def cache_190_H : List Cell := cache_190_H_part0

def cache_190 : ListRow := ⟨cache_190_A, cache_190_H, 7⟩

def cache_191_A_part0 : List Cell := [(0, -2), (0, -1), (1, -2), (1, -1), (2, -1), (3, -1), (3, 0)]

def cache_191_A : List Cell := cache_191_A_part0

def cache_191_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0)]

def cache_191_H : List Cell := cache_191_H_part0

def cache_191 : ListRow := ⟨cache_191_A, cache_191_H, 7⟩

def cache_192_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (2, -1)]

def cache_192_A : List Cell := cache_192_A_part0

def cache_192_H_part0 : List Cell := [(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)]

def cache_192_H : List Cell := cache_192_H_part0

def cache_192 : ListRow := ⟨cache_192_A, cache_192_H, 6⟩

def cache_193_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, -1), (1, 0), (2, 0)]

def cache_193_A : List Cell := cache_193_A_part0

def cache_193_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_193_H : List Cell := cache_193_H_part0

def cache_193 : ListRow := ⟨cache_193_A, cache_193_H, 7⟩

def cache_194_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)]

def cache_194_A : List Cell := cache_194_A_part0

def cache_194_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 1), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_194_H : List Cell := cache_194_H_part0

def cache_194 : ListRow := ⟨cache_194_A, cache_194_H, 5⟩

def cache_195_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0)]

def cache_195_A : List Cell := cache_195_A_part0

def cache_195_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_195_H : List Cell := cache_195_H_part0

def cache_195 : ListRow := ⟨cache_195_A, cache_195_H, 7⟩

def cache_196_A_part0 : List Cell := [(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_196_A : List Cell := cache_196_A_part0

def cache_196_H_part0 : List Cell := [(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_196_H : List Cell := cache_196_H_part0

def cache_196 : ListRow := ⟨cache_196_A, cache_196_H, 8⟩

def cache_197_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_197_A : List Cell := cache_197_A_part0

def cache_197_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_197_H : List Cell := cache_197_H_part0

def cache_197 : ListRow := ⟨cache_197_A, cache_197_H, 6⟩

def cache_198_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, -1), (-1, 0)]

def cache_198_A : List Cell := cache_198_A_part0

def cache_198_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)]

def cache_198_H : List Cell := cache_198_H_part0

def cache_198 : ListRow := ⟨cache_198_A, cache_198_H, 6⟩

def cache_199_A_part0 : List Cell := [(-1, -1), (0, -3), (0, -2), (0, -1)]

def cache_199_A : List Cell := cache_199_A_part0

def cache_199_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)]

def cache_199_H : List Cell := cache_199_H_part0

def cache_199 : ListRow := ⟨cache_199_A, cache_199_H, 6⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_200_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (2, -1)]

def cache_200_A : List Cell := cache_200_A_part0

def cache_200_H_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)]

def cache_200_H : List Cell := cache_200_H_part0

def cache_200 : ListRow := ⟨cache_200_A, cache_200_H, 6⟩

def cache_201_A_part0 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_201_A : List Cell := cache_201_A_part0

def cache_201_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)]

def cache_201_H : List Cell := cache_201_H_part0

def cache_201 : ListRow := ⟨cache_201_A, cache_201_H, 5⟩

def cache_202_A_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_202_A : List Cell := cache_202_A_part0

def cache_202_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_202_H : List Cell := cache_202_H_part0

def cache_202 : ListRow := ⟨cache_202_A, cache_202_H, 7⟩

def cache_203_A_part0 : List Cell := [(-4, -1), (-2, -1), (-2, 0), (-1, 0)]

def cache_203_A : List Cell := cache_203_A_part0

def cache_203_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_203_H : List Cell := cache_203_H_part0

def cache_203 : ListRow := ⟨cache_203_A, cache_203_H, 7⟩

def cache_204_A_part0 : List Cell := [(0, -3), (0, -1), (1, -4), (1, -3), (2, -1)]

def cache_204_A : List Cell := cache_204_A_part0

def cache_204_H_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)]

def cache_204_H : List Cell := cache_204_H_part0

def cache_204 : ListRow := ⟨cache_204_A, cache_204_H, 8⟩

def cache_205_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, -1)]

def cache_205_A : List Cell := cache_205_A_part0

def cache_205_H_part0 : List Cell := [(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_205_H : List Cell := cache_205_H_part0

def cache_205 : ListRow := ⟨cache_205_A, cache_205_H, 8⟩

def cache_206_A_part0 : List Cell := [(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_206_A : List Cell := cache_206_A_part0

def cache_206_H_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)]

def cache_206_H : List Cell := cache_206_H_part0

def cache_206 : ListRow := ⟨cache_206_A, cache_206_H, 6⟩

def cache_207_A_part0 : List Cell := [(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_207_A : List Cell := cache_207_A_part0

def cache_207_H_part0 : List Cell := [(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_207_H : List Cell := cache_207_H_part0

def cache_207 : ListRow := ⟨cache_207_A, cache_207_H, 6⟩

def cache_208_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, 0)]

def cache_208_A : List Cell := cache_208_A_part0

def cache_208_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)]

def cache_208_H : List Cell := cache_208_H_part0

def cache_208 : ListRow := ⟨cache_208_A, cache_208_H, 6⟩

def cache_209_A_part0 : List Cell := [(-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 2), (0, -1), (0, 2)]

def cache_209_A : List Cell := cache_209_A_part0

def cache_209_H_part0 : List Cell := [(-3, -1), (-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 3), (3, 0)]

def cache_209_H : List Cell := cache_209_H_part0

def cache_209 : ListRow := ⟨cache_209_A, cache_209_H, 5⟩

def cache_210_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2)]

def cache_210_A : List Cell := cache_210_A_part0

def cache_210_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)]

def cache_210_H : List Cell := cache_210_H_part0

def cache_210 : ListRow := ⟨cache_210_A, cache_210_H, 6⟩

def cache_211_A_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)]

def cache_211_A : List Cell := cache_211_A_part0

def cache_211_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)]

def cache_211_H : List Cell := cache_211_H_part0

def cache_211 : ListRow := ⟨cache_211_A, cache_211_H, 5⟩

def cache_212_A_part0 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (0, -1)]

def cache_212_A : List Cell := cache_212_A_part0

def cache_212_H_part0 : List Cell := [(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2)]

def cache_212_H : List Cell := cache_212_H_part0

def cache_212 : ListRow := ⟨cache_212_A, cache_212_H, 7⟩

def cache_213_A_part0 : List Cell := [(-1, -1), (-1, 0), (0, -1), (1, 0), (2, 0), (2, 1)]

def cache_213_A : List Cell := cache_213_A_part0

def cache_213_H_part0 : List Cell := [(-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 1)]

def cache_213_H : List Cell := cache_213_H_part0

def cache_213 : ListRow := ⟨cache_213_A, cache_213_H, 8⟩

def cache_214_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (3, -2)]

def cache_214_A : List Cell := cache_214_A_part0

def cache_214_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 1), (1, 2), (1, 3), (2, -2), (3, -2)]

def cache_214_H : List Cell := cache_214_H_part0

def cache_214 : ListRow := ⟨cache_214_A, cache_214_H, 7⟩

def cache_215_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (0, 1)]

def cache_215_A : List Cell := cache_215_A_part0

def cache_215_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)]

def cache_215_H : List Cell := cache_215_H_part0

def cache_215 : ListRow := ⟨cache_215_A, cache_215_H, 7⟩

def cache_216_A_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, 0)]

def cache_216_A : List Cell := cache_216_A_part0

def cache_216_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)]

def cache_216_H : List Cell := cache_216_H_part0

def cache_216 : ListRow := ⟨cache_216_A, cache_216_H, 6⟩

def cache_217_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_217_A : List Cell := cache_217_A_part0

def cache_217_H_part0 : List Cell := [(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_217_H : List Cell := cache_217_H_part0

def cache_217 : ListRow := ⟨cache_217_A, cache_217_H, 7⟩

def cache_218_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (1, 2)]

def cache_218_A : List Cell := cache_218_A_part0

def cache_218_H_part0 : List Cell := [(-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0)]

def cache_218_H : List Cell := cache_218_H_part0

def cache_218 : ListRow := ⟨cache_218_A, cache_218_H, 6⟩

def cache_219_A_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -1), (1, -1), (1, 0), (1, 1)]

def cache_219_A : List Cell := cache_219_A_part0

def cache_219_H_part0 : List Cell := [(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)]

def cache_219_H : List Cell := cache_219_H_part0

def cache_219 : ListRow := ⟨cache_219_A, cache_219_H, 8⟩

def cache_220_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_220_A : List Cell := cache_220_A_part0

def cache_220_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)]

def cache_220_H : List Cell := cache_220_H_part0

def cache_220 : ListRow := ⟨cache_220_A, cache_220_H, 7⟩

def cache_221_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_221_A : List Cell := cache_221_A_part0

def cache_221_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)]

def cache_221_H : List Cell := cache_221_H_part0

def cache_221 : ListRow := ⟨cache_221_A, cache_221_H, 7⟩

def cache_222_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)]

def cache_222_A : List Cell := cache_222_A_part0

def cache_222_H_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_222_H : List Cell := cache_222_H_part0

def cache_222 : ListRow := ⟨cache_222_A, cache_222_H, 6⟩

def cache_223_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, 0)]

def cache_223_A : List Cell := cache_223_A_part0

def cache_223_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)]

def cache_223_H : List Cell := cache_223_H_part0

def cache_223 : ListRow := ⟨cache_223_A, cache_223_H, 7⟩

def cache_224_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (1, -2), (2, -2)]

def cache_224_A : List Cell := cache_224_A_part0

def cache_224_H_part0 : List Cell := [(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_224_H : List Cell := cache_224_H_part0

def cache_224 : ListRow := ⟨cache_224_A, cache_224_H, 8⟩

def cache_225_A_part0 : List Cell := [(1, -2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_225_A : List Cell := cache_225_A_part0

def cache_225_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (2, 2), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_225_H : List Cell := cache_225_H_part0

def cache_225 : ListRow := ⟨cache_225_A, cache_225_H, 7⟩

def cache_226_A_part0 : List Cell := [(-3, -1), (-3, 0), (-1, -1), (-1, 0)]

def cache_226_A : List Cell := cache_226_A_part0

def cache_226_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_226_H : List Cell := cache_226_H_part0

def cache_226 : ListRow := ⟨cache_226_A, cache_226_H, 8⟩

def cache_227_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, -2), (3, -2)]

def cache_227_A : List Cell := cache_227_A_part0

def cache_227_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_227_H : List Cell := cache_227_H_part0

def cache_227 : ListRow := ⟨cache_227_A, cache_227_H, 8⟩

def cache_228_A_part0 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_228_A : List Cell := cache_228_A_part0

def cache_228_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)]

def cache_228_H : List Cell := cache_228_H_part0

def cache_228 : ListRow := ⟨cache_228_A, cache_228_H, 6⟩

def cache_229_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)]

def cache_229_A : List Cell := cache_229_A_part0

def cache_229_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1)]

def cache_229_H : List Cell := cache_229_H_part0

def cache_229 : ListRow := ⟨cache_229_A, cache_229_H, 7⟩

def cache_230_A_part0 : List Cell := [(0, 1), (2, 0), (2, 1), (3, 1)]

def cache_230_A : List Cell := cache_230_A_part0

def cache_230_H_part0 : List Cell := [(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 2)]

def cache_230_H : List Cell := cache_230_H_part0

def cache_230 : ListRow := ⟨cache_230_A, cache_230_H, 8⟩

def cache_231_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2)]

def cache_231_A : List Cell := cache_231_A_part0

def cache_231_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_231_H : List Cell := cache_231_H_part0

def cache_231 : ListRow := ⟨cache_231_A, cache_231_H, 7⟩

def cache_232_A_part0 : List Cell := [(-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 1)]

def cache_232_A : List Cell := cache_232_A_part0

def cache_232_H_part0 : List Cell := [(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)]

def cache_232_H : List Cell := cache_232_H_part0

def cache_232 : ListRow := ⟨cache_232_A, cache_232_H, 7⟩

def cache_233_A_part0 : List Cell := [(-1, -2), (0, -2), (0, -1), (1, -2), (2, -2), (2, -1), (2, 1)]

def cache_233_A : List Cell := cache_233_A_part0

def cache_233_H_part0 : List Cell := [(-2, -3), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (5, 1)]

def cache_233_H : List Cell := cache_233_H_part0

def cache_233 : ListRow := ⟨cache_233_A, cache_233_H, 6⟩

def cache_234_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)]

def cache_234_A : List Cell := cache_234_A_part0

def cache_234_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -1)]

def cache_234_H : List Cell := cache_234_H_part0

def cache_234 : ListRow := ⟨cache_234_A, cache_234_H, 7⟩

def cache_235_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (1, 0), (3, 0)]

def cache_235_A : List Cell := cache_235_A_part0

def cache_235_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_235_H : List Cell := cache_235_H_part0

def cache_235 : ListRow := ⟨cache_235_A, cache_235_H, 7⟩

def cache_236_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1)]

def cache_236_A : List Cell := cache_236_A_part0

def cache_236_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_236_H : List Cell := cache_236_H_part0

def cache_236 : ListRow := ⟨cache_236_A, cache_236_H, 6⟩

def cache_237_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)]

def cache_237_A : List Cell := cache_237_A_part0

def cache_237_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_237_H : List Cell := cache_237_H_part0

def cache_237 : ListRow := ⟨cache_237_A, cache_237_H, 7⟩

def cache_238_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)]

def cache_238_A : List Cell := cache_238_A_part0

def cache_238_H_part0 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_238_H : List Cell := cache_238_H_part0

def cache_238 : ListRow := ⟨cache_238_A, cache_238_H, 7⟩

def cache_239_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)]

def cache_239_A : List Cell := cache_239_A_part0

def cache_239_H_part0 : List Cell := [(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_239_H : List Cell := cache_239_H_part0

def cache_239 : ListRow := ⟨cache_239_A, cache_239_H, 7⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_240_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_240_A : List Cell := cache_240_A_part0

def cache_240_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_240_H : List Cell := cache_240_H_part0

def cache_240 : ListRow := ⟨cache_240_A, cache_240_H, 8⟩

def cache_241_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -2), (-1, -1), (-1, 0)]

def cache_241_A : List Cell := cache_241_A_part0

def cache_241_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)]

def cache_241_H : List Cell := cache_241_H_part0

def cache_241 : ListRow := ⟨cache_241_A, cache_241_H, 7⟩

def cache_242_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_242_A : List Cell := cache_242_A_part0

def cache_242_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1)]

def cache_242_H : List Cell := cache_242_H_part0

def cache_242 : ListRow := ⟨cache_242_A, cache_242_H, 8⟩

def cache_243_A_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (0, -1), (0, 2)]

def cache_243_A : List Cell := cache_243_A_part0

def cache_243_H_part0 : List Cell := [(-4, -2), (-3, -2), (-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)]

def cache_243_H : List Cell := cache_243_H_part0

def cache_243 : ListRow := ⟨cache_243_A, cache_243_H, 7⟩

def cache_244_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, 0)]

def cache_244_A : List Cell := cache_244_A_part0

def cache_244_H_part0 : List Cell := [(-5, 1), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_244_H : List Cell := cache_244_H_part0

def cache_244 : ListRow := ⟨cache_244_A, cache_244_H, 7⟩

def cache_245_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_245_A : List Cell := cache_245_A_part0

def cache_245_H_part0 : List Cell := [(-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_245_H : List Cell := cache_245_H_part0

def cache_245 : ListRow := ⟨cache_245_A, cache_245_H, 8⟩

def cache_246_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_246_A : List Cell := cache_246_A_part0

def cache_246_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)]

def cache_246_H : List Cell := cache_246_H_part0

def cache_246 : ListRow := ⟨cache_246_A, cache_246_H, 8⟩

def cache_247_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)]

def cache_247_A : List Cell := cache_247_A_part0

def cache_247_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, 0)]

def cache_247_H : List Cell := cache_247_H_part0

def cache_247 : ListRow := ⟨cache_247_A, cache_247_H, 8⟩

def cache_248_A_part0 : List Cell := [(-1, 0), (1, 0), (2, 0)]

def cache_248_A : List Cell := cache_248_A_part0

def cache_248_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)]

def cache_248_H : List Cell := cache_248_H_part0

def cache_248 : ListRow := ⟨cache_248_A, cache_248_H, 8⟩

def cache_249_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1)]

def cache_249_A : List Cell := cache_249_A_part0

def cache_249_H_part0 : List Cell := [(-3, 0), (-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -1), (3, -3)]

def cache_249_H : List Cell := cache_249_H_part0

def cache_249 : ListRow := ⟨cache_249_A, cache_249_H, 8⟩

def cache_250_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)]

def cache_250_A : List Cell := cache_250_A_part0

def cache_250_H_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_250_H : List Cell := cache_250_H_part0

def cache_250 : ListRow := ⟨cache_250_A, cache_250_H, 8⟩

def cache_251_A_part0 : List Cell := [(-3, 1), (-2, 1), (-1, 1), (0, 1), (0, 2)]

def cache_251_A : List Cell := cache_251_A_part0

def cache_251_H_part0 : List Cell := [(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 3), (1, 4), (1, 5), (2, 3), (3, 3)]

def cache_251_H : List Cell := cache_251_H_part0

def cache_251 : ListRow := ⟨cache_251_A, cache_251_H, 8⟩

def cache_252_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_252_A : List Cell := cache_252_A_part0

def cache_252_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)]

def cache_252_H : List Cell := cache_252_H_part0

def cache_252 : ListRow := ⟨cache_252_A, cache_252_H, 7⟩

def cache_253_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)]

def cache_253_A : List Cell := cache_253_A_part0

def cache_253_H_part0 : List Cell := [(-2, -4), (-1, -4), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1), (5, -1)]

def cache_253_H : List Cell := cache_253_H_part0

def cache_253 : ListRow := ⟨cache_253_A, cache_253_H, 7⟩

def cache_254_A_part0 : List Cell := [(0, -2), (1, 1), (2, 1), (3, 1)]

def cache_254_A : List Cell := cache_254_A_part0

def cache_254_H_part0 : List Cell := [(-2, 2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)]

def cache_254_H : List Cell := cache_254_H_part0

def cache_254 : ListRow := ⟨cache_254_A, cache_254_H, 7⟩

def cache_255_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (3, 0)]

def cache_255_A : List Cell := cache_255_A_part0

def cache_255_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)]

def cache_255_H : List Cell := cache_255_H_part0

def cache_255 : ListRow := ⟨cache_255_A, cache_255_H, 9⟩

def cache_256_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)]

def cache_256_A : List Cell := cache_256_A_part0

def cache_256_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_256_H : List Cell := cache_256_H_part0

def cache_256 : ListRow := ⟨cache_256_A, cache_256_H, 8⟩

def cache_257_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, 1), (3, 1)]

def cache_257_A : List Cell := cache_257_A_part0

def cache_257_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)]

def cache_257_H : List Cell := cache_257_H_part0

def cache_257 : ListRow := ⟨cache_257_A, cache_257_H, 8⟩

def cache_258_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (1, 1), (2, -1), (3, -1)]

def cache_258_A : List Cell := cache_258_A_part0

def cache_258_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)]

def cache_258_H : List Cell := cache_258_H_part0

def cache_258 : ListRow := ⟨cache_258_A, cache_258_H, 9⟩

def cache_259_A_part0 : List Cell := [(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_259_A : List Cell := cache_259_A_part0

def cache_259_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_259_H : List Cell := cache_259_H_part0

def cache_259 : ListRow := ⟨cache_259_A, cache_259_H, 8⟩

def cache_260_A_part0 : List Cell := [(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)]

def cache_260_A : List Cell := cache_260_A_part0

def cache_260_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)]

def cache_260_H : List Cell := cache_260_H_part0

def cache_260 : ListRow := ⟨cache_260_A, cache_260_H, 8⟩

def cache_261_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0)]

def cache_261_A : List Cell := cache_261_A_part0

def cache_261_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0), (5, 1)]

def cache_261_H : List Cell := cache_261_H_part0

def cache_261 : ListRow := ⟨cache_261_A, cache_261_H, 9⟩

def cache_262_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (0, -1), (1, 0), (1, 1), (1, 2)]

def cache_262_A : List Cell := cache_262_A_part0

def cache_262_H_part0 : List Cell := [(-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1)]

def cache_262_H : List Cell := cache_262_H_part0

def cache_262 : ListRow := ⟨cache_262_A, cache_262_H, 9⟩

def cache_263_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_263_A : List Cell := cache_263_A_part0

def cache_263_H_part0 : List Cell := [(-6, -1), (-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)]

def cache_263_H : List Cell := cache_263_H_part0

def cache_263 : ListRow := ⟨cache_263_A, cache_263_H, 8⟩

def cache_264_A_part0 : List Cell := [(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_264_A : List Cell := cache_264_A_part0

def cache_264_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_264_H : List Cell := cache_264_H_part0

def cache_264 : ListRow := ⟨cache_264_A, cache_264_H, 9⟩

def cache_265_A_part0 : List Cell := [(0, 1), (1, 1), (2, 1), (3, 1)]

def cache_265_A : List Cell := cache_265_A_part0

def cache_265_H_part0 : List Cell := [(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 2)]

def cache_265_H : List Cell := cache_265_H_part0

def cache_265 : ListRow := ⟨cache_265_A, cache_265_H, 9⟩

def cache_266_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1)]

def cache_266_A : List Cell := cache_266_A_part0

def cache_266_H_part0 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)]

def cache_266_H : List Cell := cache_266_H_part0

def cache_266 : ListRow := ⟨cache_266_A, cache_266_H, 9⟩

def cache_267_A_part0 : List Cell := [(-2, 0), (-1, 0), (1, 0)]

def cache_267_A : List Cell := cache_267_A_part0

def cache_267_H_part0 : List Cell := [(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)]

def cache_267_H : List Cell := cache_267_H_part0

def cache_267 : ListRow := ⟨cache_267_A, cache_267_H, 8⟩

def cache_268_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1)]

def cache_268_A : List Cell := cache_268_A_part0

def cache_268_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1)]

def cache_268_H : List Cell := cache_268_H_part0

def cache_268 : ListRow := ⟨cache_268_A, cache_268_H, 9⟩

def cache_269_A_part0 : List Cell := [(-1, 1), (-1, 3), (0, 1), (1, 1), (2, 1)]

def cache_269_A : List Cell := cache_269_A_part0

def cache_269_H_part0 : List Cell := [(-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)]

def cache_269_H : List Cell := cache_269_H_part0

def cache_269 : ListRow := ⟨cache_269_A, cache_269_H, 8⟩

def cache_270_A_part0 : List Cell := [(-1, -1), (0, -1), (0, 1), (0, 2)]

def cache_270_A : List Cell := cache_270_A_part0

def cache_270_H_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4)]

def cache_270_H : List Cell := cache_270_H_part0

def cache_270 : ListRow := ⟨cache_270_A, cache_270_H, 6⟩

def cache_271_A_part0 : List Cell := [(0, -1), (0, 1), (1, -1), (2, -1)]

def cache_271_A : List Cell := cache_271_A_part0

def cache_271_H_part0 : List Cell := [(-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)]

def cache_271_H : List Cell := cache_271_H_part0

def cache_271 : ListRow := ⟨cache_271_A, cache_271_H, 7⟩

def cache_272_A_part0 : List Cell := [(-2, -1), (-1, -4), (-1, -2), (-1, -1), (0, -1)]

def cache_272_A : List Cell := cache_272_A_part0

def cache_272_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (3, -2)]

def cache_272_H : List Cell := cache_272_H_part0

def cache_272 : ListRow := ⟨cache_272_A, cache_272_H, 9⟩

def cache_273_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_273_A : List Cell := cache_273_A_part0

def cache_273_H_part0 : List Cell := [(-4, 0), (-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_273_H : List Cell := cache_273_H_part0

def cache_273 : ListRow := ⟨cache_273_A, cache_273_H, 8⟩

def cache_274_A_part0 : List Cell := [(-1, -2), (0, -2), (0, -1), (0, 1)]

def cache_274_A : List Cell := cache_274_A_part0

def cache_274_H_part0 : List Cell := [(-3, 0), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)]

def cache_274_H : List Cell := cache_274_H_part0

def cache_274 : ListRow := ⟨cache_274_A, cache_274_H, 9⟩

def cache_275_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, 0), (-1, 0)]

def cache_275_A : List Cell := cache_275_A_part0

def cache_275_H_part0 : List Cell := [(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_275_H : List Cell := cache_275_H_part0

def cache_275 : ListRow := ⟨cache_275_A, cache_275_H, 7⟩

def cache_276_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (3, -2), (3, 0)]

def cache_276_A : List Cell := cache_276_A_part0

def cache_276_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (4, -1)]

def cache_276_H : List Cell := cache_276_H_part0

def cache_276 : ListRow := ⟨cache_276_A, cache_276_H, 7⟩

def cache_277_A_part0 : List Cell := [(-1, -3), (-1, -1), (0, -1), (1, -3), (1, -2), (1, -1)]

def cache_277_A : List Cell := cache_277_A_part0

def cache_277_H_part0 : List Cell := [(-2, -4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)]

def cache_277_H : List Cell := cache_277_H_part0

def cache_277 : ListRow := ⟨cache_277_A, cache_277_H, 9⟩

def cache_278_A_part0 : List Cell := [(1, 0), (2, -1), (2, 0), (3, 0)]

def cache_278_A : List Cell := cache_278_A_part0

def cache_278_H_part0 : List Cell := [(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)]

def cache_278_H : List Cell := cache_278_H_part0

def cache_278 : ListRow := ⟨cache_278_A, cache_278_H, 7⟩

def cache_279_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)]

def cache_279_A : List Cell := cache_279_A_part0

def cache_279_H_part0 : List Cell := [(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)]

def cache_279_H : List Cell := cache_279_H_part0

def cache_279 : ListRow := ⟨cache_279_A, cache_279_H, 8⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_280_A_part0 : List Cell := [(-3, -2), (-2, -3), (-2, -2), (-1, -2), (-1, 0), (-1, 1), (0, -2)]

def cache_280_A : List Cell := cache_280_A_part0

def cache_280_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)]

def cache_280_H : List Cell := cache_280_H_part0

def cache_280 : ListRow := ⟨cache_280_A, cache_280_H, 5⟩

def cache_281_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0), (-1, 1)]

def cache_281_A : List Cell := cache_281_A_part0

def cache_281_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_281_H : List Cell := cache_281_H_part0

def cache_281 : ListRow := ⟨cache_281_A, cache_281_H, 7⟩

def cache_282_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_282_A : List Cell := cache_282_A_part0

def cache_282_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_282_H : List Cell := cache_282_H_part0

def cache_282 : ListRow := ⟨cache_282_A, cache_282_H, 10⟩

def cache_283_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -2), (-1, 0)]

def cache_283_A : List Cell := cache_283_A_part0

def cache_283_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)]

def cache_283_H : List Cell := cache_283_H_part0

def cache_283 : ListRow := ⟨cache_283_A, cache_283_H, 9⟩

def cache_284_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)]

def cache_284_A : List Cell := cache_284_A_part0

def cache_284_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_284_H : List Cell := cache_284_H_part0

def cache_284 : ListRow := ⟨cache_284_A, cache_284_H, 9⟩

def cache_285_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0)]

def cache_285_A : List Cell := cache_285_A_part0

def cache_285_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_285_H : List Cell := cache_285_H_part0

def cache_285 : ListRow := ⟨cache_285_A, cache_285_H, 9⟩

def cache_286_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (0, -1)]

def cache_286_A : List Cell := cache_286_A_part0

def cache_286_H_part0 : List Cell := [(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)]

def cache_286_H : List Cell := cache_286_H_part0

def cache_286 : ListRow := ⟨cache_286_A, cache_286_H, 10⟩

def cache_287_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1)]

def cache_287_A : List Cell := cache_287_A_part0

def cache_287_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]

def cache_287_H : List Cell := cache_287_H_part0

def cache_287 : ListRow := ⟨cache_287_A, cache_287_H, 10⟩

def cache_288_A_part0 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)]

def cache_288_A : List Cell := cache_288_A_part0

def cache_288_H_part0 : List Cell := [(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (1, 2)]

def cache_288_H : List Cell := cache_288_H_part0

def cache_288 : ListRow := ⟨cache_288_A, cache_288_H, 7⟩

def cache_289_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)]

def cache_289_A : List Cell := cache_289_A_part0

def cache_289_H_part0 : List Cell := [(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_289_H : List Cell := cache_289_H_part0

def cache_289 : ListRow := ⟨cache_289_A, cache_289_H, 9⟩

def cache_290_A_part0 : List Cell := [(-2, -1), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 1)]

def cache_290_A : List Cell := cache_290_A_part0

def cache_290_H_part0 : List Cell := [(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (3, -2)]

def cache_290_H : List Cell := cache_290_H_part0

def cache_290 : ListRow := ⟨cache_290_A, cache_290_H, 8⟩

def cache_291_A_part0 : List Cell := [(1, -1), (1, 0), (2, 0), (3, 0)]

def cache_291_A : List Cell := cache_291_A_part0

def cache_291_H_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)]

def cache_291_H : List Cell := cache_291_H_part0

def cache_291 : ListRow := ⟨cache_291_A, cache_291_H, 8⟩

def cache_292_A_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, 1)]

def cache_292_A : List Cell := cache_292_A_part0

def cache_292_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (2, 0)]

def cache_292_H : List Cell := cache_292_H_part0

def cache_292 : ListRow := ⟨cache_292_A, cache_292_H, 9⟩

def cache_293_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)]

def cache_293_A : List Cell := cache_293_A_part0

def cache_293_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)]

def cache_293_H : List Cell := cache_293_H_part0

def cache_293 : ListRow := ⟨cache_293_A, cache_293_H, 6⟩

def cache_294_A_part0 : List Cell := [(-3, 0), (-2, -2), (-2, 0), (-1, 0)]

def cache_294_A : List Cell := cache_294_A_part0

def cache_294_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_294_H_part1 : List Cell := [(2, 1)]

def cache_294_H : List Cell := (cache_294_H_part0 ++ cache_294_H_part1)

def cache_294 : ListRow := ⟨cache_294_A, cache_294_H, 9⟩

def cache_295_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_295_A : List Cell := cache_295_A_part0

def cache_295_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1)]

def cache_295_H_part1 : List Cell := [(2, 1)]

def cache_295_H : List Cell := (cache_295_H_part0 ++ cache_295_H_part1)

def cache_295 : ListRow := ⟨cache_295_A, cache_295_H, 10⟩

def cache_296_A_part0 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-1, -2), (0, -2), (0, -1)]

def cache_296_A : List Cell := cache_296_A_part0

def cache_296_H_part0 : List Cell := [(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2)]

def cache_296_H_part1 : List Cell := [(1, 3)]

def cache_296_H : List Cell := (cache_296_H_part0 ++ cache_296_H_part1)

def cache_296 : ListRow := ⟨cache_296_A, cache_296_H, 7⟩

def cache_297_A_part0 : List Cell := [(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)]

def cache_297_A : List Cell := cache_297_A_part0

def cache_297_H_part0 : List Cell := [(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_297_H_part1 : List Cell := [(4, 4)]

def cache_297_H : List Cell := (cache_297_H_part0 ++ cache_297_H_part1)

def cache_297 : ListRow := ⟨cache_297_A, cache_297_H, 10⟩

def cache_298_A_part0 : List Cell := [(0, -1), (1, 0), (2, -1), (2, 0)]

def cache_298_A : List Cell := cache_298_A_part0

def cache_298_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_298_H_part1 : List Cell := [(7, -1)]

def cache_298_H : List Cell := (cache_298_H_part0 ++ cache_298_H_part1)

def cache_298 : ListRow := ⟨cache_298_A, cache_298_H, 8⟩

def cache_299_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)]

def cache_299_A : List Cell := cache_299_A_part0

def cache_299_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0)]

def cache_299_H_part1 : List Cell := [(4, 2)]

def cache_299_H : List Cell := (cache_299_H_part0 ++ cache_299_H_part1)

def cache_299 : ListRow := ⟨cache_299_A, cache_299_H, 10⟩

def cache_300_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_300_A : List Cell := cache_300_A_part0

def cache_300_H_part0 : List Cell := [(-3, -2), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4)]

def cache_300_H_part1 : List Cell := [(4, -2)]

def cache_300_H : List Cell := (cache_300_H_part0 ++ cache_300_H_part1)

def cache_300 : ListRow := ⟨cache_300_A, cache_300_H, 9⟩

def cache_301_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (0, -1)]

def cache_301_A : List Cell := cache_301_A_part0

def cache_301_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0)]

def cache_301_H_part1 : List Cell := [(2, 1)]

def cache_301_H : List Cell := (cache_301_H_part0 ++ cache_301_H_part1)

def cache_301 : ListRow := ⟨cache_301_A, cache_301_H, 10⟩

def cache_302_A_part0 : List Cell := [(-2, -2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -2), (2, -1)]

def cache_302_A : List Cell := cache_302_A_part0

def cache_302_H_part0 : List Cell := [(-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0)]

def cache_302_H_part1 : List Cell := [(3, -1), (4, -1)]

def cache_302_H : List Cell := (cache_302_H_part0 ++ cache_302_H_part1)

def cache_302 : ListRow := ⟨cache_302_A, cache_302_H, 7⟩

def cache_303_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3)]

def cache_303_A : List Cell := cache_303_A_part0

def cache_303_H_part0 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1)]

def cache_303_H_part1 : List Cell := [(4, 0), (4, 1)]

def cache_303_H : List Cell := (cache_303_H_part0 ++ cache_303_H_part1)

def cache_303 : ListRow := ⟨cache_303_A, cache_303_H, 10⟩

def cache_304_A_part0 : List Cell := [(1, -1), (1, 0), (2, 0), (3, 0)]

def cache_304_A : List Cell := cache_304_A_part0

def cache_304_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_304_H_part1 : List Cell := [(7, -1), (7, 1)]

def cache_304_H : List Cell := (cache_304_H_part0 ++ cache_304_H_part1)

def cache_304 : ListRow := ⟨cache_304_A, cache_304_H, 8⟩

def cache_305_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_305_A : List Cell := cache_305_A_part0

def cache_305_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0)]

def cache_305_H_part1 : List Cell := [(3, 1), (4, -1)]

def cache_305_H : List Cell := (cache_305_H_part0 ++ cache_305_H_part1)

def cache_305 : ListRow := ⟨cache_305_A, cache_305_H, 8⟩

def cache_306_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)]

def cache_306_A : List Cell := cache_306_A_part0

def cache_306_H_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, 0)]

def cache_306_H_part1 : List Cell := [(3, 1), (3, 2)]

def cache_306_H : List Cell := (cache_306_H_part0 ++ cache_306_H_part1)

def cache_306 : ListRow := ⟨cache_306_A, cache_306_H, 8⟩

def cache_307_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)]

def cache_307_A : List Cell := cache_307_A_part0

def cache_307_H_part0 : List Cell := [(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1)]

def cache_307_H_part1 : List Cell := [(4, 2), (5, 0)]

def cache_307_H : List Cell := (cache_307_H_part0 ++ cache_307_H_part1)

def cache_307 : ListRow := ⟨cache_307_A, cache_307_H, 9⟩

def cache_308_A_part0 : List Cell := [(0, 1), (1, 1), (2, 1), (3, 1)]

def cache_308_A : List Cell := cache_308_A_part0

def cache_308_H_part0 : List Cell := [(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4)]

def cache_308_H_part1 : List Cell := [(4, 2), (4, 4)]

def cache_308_H : List Cell := (cache_308_H_part0 ++ cache_308_H_part1)

def cache_308 : ListRow := ⟨cache_308_A, cache_308_H, 11⟩

def cache_309_A_part0 : List Cell := [(-2, 0), (0, 1), (0, 2), (0, 3), (1, 1)]

def cache_309_A : List Cell := cache_309_A_part0

def cache_309_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (4, 2)]

def cache_309_H_part1 : List Cell := [(4, 3), (4, 4)]

def cache_309_H : List Cell := (cache_309_H_part0 ++ cache_309_H_part1)

def cache_309 : ListRow := ⟨cache_309_A, cache_309_H, 10⟩

def cache_310_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1)]

def cache_310_A : List Cell := cache_310_A_part0

def cache_310_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0)]

def cache_310_H_part1 : List Cell := [(4, -2), (4, 0)]

def cache_310_H : List Cell := (cache_310_H_part0 ++ cache_310_H_part1)

def cache_310 : ListRow := ⟨cache_310_A, cache_310_H, 8⟩

def cache_311_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)]

def cache_311_A : List Cell := cache_311_A_part0

def cache_311_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0)]

def cache_311_H_part1 : List Cell := [(4, 1), (5, -1)]

def cache_311_H : List Cell := (cache_311_H_part0 ++ cache_311_H_part1)

def cache_311 : ListRow := ⟨cache_311_A, cache_311_H, 8⟩

def cache_312_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -3), (-1, -1), (-1, 0)]

def cache_312_A : List Cell := cache_312_A_part0

def cache_312_H_part0 : List Cell := [(-3, -1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1)]

def cache_312_H_part1 : List Cell := [(2, 0), (2, 1), (3, -1)]

def cache_312_H : List Cell := (cache_312_H_part0 ++ cache_312_H_part1)

def cache_312 : ListRow := ⟨cache_312_A, cache_312_H, 10⟩

def cache_313_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -3), (0, -2), (0, -1), (1, -1)]

def cache_313_A : List Cell := cache_313_A_part0

def cache_313_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (3, -2), (3, -1)]

def cache_313_H_part1 : List Cell := [(4, -2), (4, -1), (5, -2)]

def cache_313_H : List Cell := (cache_313_H_part0 ++ cache_313_H_part1)

def cache_313 : ListRow := ⟨cache_313_A, cache_313_H, 7⟩

def cache_314_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0)]

def cache_314_A : List Cell := cache_314_A_part0

def cache_314_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_314_H_part1 : List Cell := [(5, 0), (5, 1), (6, -1)]

def cache_314_H : List Cell := (cache_314_H_part0 ++ cache_314_H_part1)

def cache_314 : ListRow := ⟨cache_314_A, cache_314_H, 9⟩

def cache_315_A_part0 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)]

def cache_315_A : List Cell := cache_315_A_part0

def cache_315_H_part0 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0)]

def cache_315_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4)]

def cache_315_H : List Cell := (cache_315_H_part0 ++ cache_315_H_part1)

def cache_315 : ListRow := ⟨cache_315_A, cache_315_H, 8⟩

def cache_316_A_part0 : List Cell := [(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)]

def cache_316_A : List Cell := cache_316_A_part0

def cache_316_H_part0 : List Cell := [(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2)]

def cache_316_H_part1 : List Cell := [(4, 4), (4, 5), (4, 6)]

def cache_316_H : List Cell := (cache_316_H_part0 ++ cache_316_H_part1)

def cache_316 : ListRow := ⟨cache_316_A, cache_316_H, 9⟩

def cache_317_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (1, 0)]

def cache_317_A : List Cell := cache_317_A_part0

def cache_317_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_317_H_part1 : List Cell := [(5, -1), (5, 0), (5, 1)]

def cache_317_H : List Cell := (cache_317_H_part0 ++ cache_317_H_part1)

def cache_317 : ListRow := ⟨cache_317_A, cache_317_H, 9⟩

def cache_318_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_318_A : List Cell := cache_318_A_part0

def cache_318_H_part0 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0)]

def cache_318_H_part1 : List Cell := [(3, 1), (4, 0), (4, 1)]

def cache_318_H : List Cell := (cache_318_H_part0 ++ cache_318_H_part1)

def cache_318 : ListRow := ⟨cache_318_A, cache_318_H, 10⟩

def cache_319_A_part0 : List Cell := [(-3, 1), (-2, 1), (-1, 1)]

def cache_319_A : List Cell := cache_319_A_part0

def cache_319_H_part0 : List Cell := [(-6, 2), (-5, 1), (-5, 2), (-4, 1), (-4, 2), (-3, 1), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 2), (1, 3), (1, 4)]

def cache_319_H_part1 : List Cell := [(1, 5), (2, 0), (2, 3), (3, 3)]

def cache_319_H : List Cell := (cache_319_H_part0 ++ cache_319_H_part1)

def cache_319 : ListRow := ⟨cache_319_A, cache_319_H, 10⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_320_A_part0 : List Cell := [(0, -3), (0, -2), (1, -3), (1, 0), (3, 0)]

def cache_320_A : List Cell := cache_320_A_part0

def cache_320_H_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0)]

def cache_320_H_part1 : List Cell := [(4, 1), (5, 0), (5, 1), (6, 1)]

def cache_320_H : List Cell := (cache_320_H_part0 ++ cache_320_H_part1)

def cache_320 : ListRow := ⟨cache_320_A, cache_320_H, 9⟩

def cache_321_A_part0 : List Cell := [(0, 1), (0, 2), (1, 1), (2, 1)]

def cache_321_A : List Cell := cache_321_A_part0

def cache_321_H_part0 : List Cell := [(-3, 3), (-2, 3), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (3, 1)]

def cache_321_H_part1 : List Cell := [(3, 2), (4, 1), (4, 2), (5, 2)]

def cache_321_H : List Cell := (cache_321_H_part0 ++ cache_321_H_part1)

def cache_321 : ListRow := ⟨cache_321_A, cache_321_H, 8⟩

def cache_322_A_part0 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)]

def cache_322_A : List Cell := cache_322_A_part0

def cache_322_H_part0 : List Cell := [(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4)]

def cache_322_H_part1 : List Cell := [(2, -2), (2, -1), (2, 0), (2, 1)]

def cache_322_H : List Cell := (cache_322_H_part0 ++ cache_322_H_part1)

def cache_322 : ListRow := ⟨cache_322_A, cache_322_H, 9⟩

def cache_323_A_part0 : List Cell := [(-2, 0), (-1, -2), (-1, -1), (-1, 0)]

def cache_323_A : List Cell := cache_323_A_part0

def cache_323_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)]

def cache_323_H_part1 : List Cell := [(3, -1), (3, 0), (3, 1), (4, -1)]

def cache_323_H : List Cell := (cache_323_H_part0 ++ cache_323_H_part1)

def cache_323 : ListRow := ⟨cache_323_A, cache_323_H, 8⟩

def cache_324_A_part0 : List Cell := [(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_324_A : List Cell := cache_324_A_part0

def cache_324_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_324_H_part1 : List Cell := [(5, -1), (5, 0), (5, 1), (6, -1)]

def cache_324_H : List Cell := (cache_324_H_part0 ++ cache_324_H_part1)

def cache_324 : ListRow := ⟨cache_324_A, cache_324_H, 9⟩

def cache_325_A_part0 : List Cell := [(-1, 0), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_325_A : List Cell := cache_325_A_part0

def cache_325_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_325_H_part1 : List Cell := [(5, -1), (5, 0), (5, 1), (6, 1)]

def cache_325_H : List Cell := (cache_325_H_part0 ++ cache_325_H_part1)

def cache_325 : ListRow := ⟨cache_325_A, cache_325_H, 8⟩

def cache_326_A_part0 : List Cell := [(-4, -3), (-3, 0), (-2, 0), (-1, 0)]

def cache_326_A : List Cell := cache_326_A_part0

def cache_326_H_part0 : List Cell := [(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1)]

def cache_326_H_part1 : List Cell := [(1, 0), (1, 1), (2, -1), (2, 1)]

def cache_326_H : List Cell := (cache_326_H_part0 ++ cache_326_H_part1)

def cache_326 : ListRow := ⟨cache_326_A, cache_326_H, 10⟩

def cache_327_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, -1), (1, 0)]

def cache_327_A : List Cell := cache_327_A_part0

def cache_327_H_part0 : List Cell := [(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0)]

def cache_327_H_part1 : List Cell := [(4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_327_H : List Cell := (cache_327_H_part0 ++ cache_327_H_part1)

def cache_327 : ListRow := ⟨cache_327_A, cache_327_H, 8⟩

def cache_328_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (0, -1)]

def cache_328_A : List Cell := cache_328_A_part0

def cache_328_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0)]

def cache_328_H_part1 : List Cell := [(3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_328_H : List Cell := (cache_328_H_part0 ++ cache_328_H_part1)

def cache_328 : ListRow := ⟨cache_328_A, cache_328_H, 10⟩

def cache_329_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)]

def cache_329_A : List Cell := cache_329_A_part0

def cache_329_H_part0 : List Cell := [(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]

def cache_329_H_part1 : List Cell := [(3, 2), (4, 0), (4, 1), (4, 2), (5, 0)]

def cache_329_H : List Cell := (cache_329_H_part0 ++ cache_329_H_part1)

def cache_329 : ListRow := ⟨cache_329_A, cache_329_H, 9⟩

def cache_330_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_330_A : List Cell := cache_330_A_part0

def cache_330_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1)]

def cache_330_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (3, 1), (3, 2)]

def cache_330_H : List Cell := (cache_330_H_part0 ++ cache_330_H_part1)

def cache_330 : ListRow := ⟨cache_330_A, cache_330_H, 10⟩

def cache_331_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, 1)]

def cache_331_A : List Cell := cache_331_A_part0

def cache_331_H_part0 : List Cell := [(-7, 0), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2)]

def cache_331_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (3, 0), (3, 2)]

def cache_331_H : List Cell := (cache_331_H_part0 ++ cache_331_H_part1)

def cache_331 : ListRow := ⟨cache_331_A, cache_331_H, 9⟩

def cache_332_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -1), (1, 0)]

def cache_332_A : List Cell := cache_332_A_part0

def cache_332_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3)]

def cache_332_H_part1 : List Cell := [(4, -2), (5, -4), (5, -3), (5, -2), (6, -2)]

def cache_332_H : List Cell := (cache_332_H_part0 ++ cache_332_H_part1)

def cache_332 : ListRow := ⟨cache_332_A, cache_332_H, 10⟩

def cache_333_A_part0 : List Cell := [(0, -3), (0, -2), (1, -4), (1, -3), (1, -2), (2, 0)]

def cache_333_A : List Cell := cache_333_A_part0

def cache_333_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_333_H_part1 : List Cell := [(5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_333_H : List Cell := (cache_333_H_part0 ++ cache_333_H_part1)

def cache_333 : ListRow := ⟨cache_333_A, cache_333_H, 10⟩

def cache_334_A_part0 : List Cell := [(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)]

def cache_334_A : List Cell := cache_334_A_part0

def cache_334_H_part0 : List Cell := [(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1)]

def cache_334_H_part1 : List Cell := [(4, 2), (5, 0), (5, 1), (5, 2), (6, 0)]

def cache_334_H : List Cell := (cache_334_H_part0 ++ cache_334_H_part1)

def cache_334 : ListRow := ⟨cache_334_A, cache_334_H, 10⟩

def cache_335_A_part0 : List Cell := [(-3, 0), (-2, -2), (-2, 0), (-1, -1), (-1, 0)]

def cache_335_A : List Cell := cache_335_A_part0

def cache_335_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_335_H_part1 : List Cell := [(2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_335_H : List Cell := (cache_335_H_part0 ++ cache_335_H_part1)

def cache_335 : ListRow := ⟨cache_335_A, cache_335_H, 9⟩

def cache_336_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, 0)]

def cache_336_A : List Cell := cache_336_A_part0

def cache_336_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0)]

def cache_336_H_part1 : List Cell := [(3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_336_H : List Cell := (cache_336_H_part0 ++ cache_336_H_part1)

def cache_336 : ListRow := ⟨cache_336_A, cache_336_H, 9⟩

def cache_337_A_part0 : List Cell := [(-3, 0), (-1, 0), (-1, 1), (-1, 2)]

def cache_337_A : List Cell := cache_337_A_part0

def cache_337_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]

def cache_337_H_part1 : List Cell := [(2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_337_H : List Cell := (cache_337_H_part0 ++ cache_337_H_part1)

def cache_337 : ListRow := ⟨cache_337_A, cache_337_H, 9⟩

def cache_338_A_part0 : List Cell := [(-1, 0), (1, -2), (1, -1), (1, 0)]

def cache_338_A : List Cell := cache_338_A_part0

def cache_338_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_338_H_part1 : List Cell := [(4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)]

def cache_338_H : List Cell := (cache_338_H_part0 ++ cache_338_H_part1)

def cache_338 : ListRow := ⟨cache_338_A, cache_338_H, 8⟩

def cache_339_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)]

def cache_339_A : List Cell := cache_339_A_part0

def cache_339_H_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, -1)]

def cache_339_H_part1 : List Cell := [(3, 0), (4, -4), (4, -2), (4, -1), (4, 0), (4, 1)]

def cache_339_H : List Cell := (cache_339_H_part0 ++ cache_339_H_part1)

def cache_339 : ListRow := ⟨cache_339_A, cache_339_H, 10⟩

def cache_340_A_part0 : List Cell := [(-1, 1), (0, -1), (0, 1)]

def cache_340_A : List Cell := cache_340_A_part0

def cache_340_H_part0 : List Cell := [(-4, -2), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0)]

def cache_340_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0)]

def cache_340_H : List Cell := (cache_340_H_part0 ++ cache_340_H_part1)

def cache_340 : ListRow := ⟨cache_340_A, cache_340_H, 10⟩

def cache_341_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1)]

def cache_341_A : List Cell := cache_341_A_part0

def cache_341_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_341_H_part1 : List Cell := [(2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)]

def cache_341_H : List Cell := (cache_341_H_part0 ++ cache_341_H_part1)

def cache_341 : ListRow := ⟨cache_341_A, cache_341_H, 9⟩

def cache_342_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2)]

def cache_342_A : List Cell := cache_342_A_part0

def cache_342_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_342_H_part1 : List Cell := [(2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1)]

def cache_342_H : List Cell := (cache_342_H_part0 ++ cache_342_H_part1)

def cache_342 : ListRow := ⟨cache_342_A, cache_342_H, 9⟩

def cache_343_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)]

def cache_343_A : List Cell := cache_343_A_part0

def cache_343_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_343_H : List Cell := cache_343_H_part0

def cache_343 : ListRow := ⟨cache_343_A, cache_343_H, 9⟩

def cache_344_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (2, -3), (3, -3), (3, -2)]

def cache_344_A : List Cell := cache_344_A_part0

def cache_344_H_part0 : List Cell := [(-1, -1), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3)]

def cache_344_H_part1 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_344_H : List Cell := (cache_344_H_part0 ++ cache_344_H_part1)

def cache_344 : ListRow := ⟨cache_344_A, cache_344_H, 10⟩

def cache_345_A_part0 : List Cell := [(-3, 0), (-3, 3), (-2, 0), (-1, 0), (-1, 3), (0, 1)]

def cache_345_A : List Cell := cache_345_A_part0

def cache_345_H_part0 : List Cell := [(-6, 4), (-5, 3), (-5, 4), (-4, 3), (-4, 4), (-3, 0), (-3, 3), (-3, 4), (-2, 0), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_345_H_part1 : List Cell := [(1, 5), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)]

def cache_345_H : List Cell := (cache_345_H_part0 ++ cache_345_H_part1)

def cache_345 : ListRow := ⟨cache_345_A, cache_345_H, 10⟩

def cache_346_A_part0 : List Cell := [(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-1, -3), (0, -3), (0, -2)]

def cache_346_A : List Cell := cache_346_A_part0

def cache_346_H_part0 : List Cell := [(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1)]

def cache_346_H_part1 : List Cell := [(0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_346_H : List Cell := (cache_346_H_part0 ++ cache_346_H_part1)

def cache_346 : ListRow := ⟨cache_346_A, cache_346_H, 10⟩

def cache_347_A_part0 : List Cell := [(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)]

def cache_347_A : List Cell := cache_347_A_part0

def cache_347_H_part0 : List Cell := [(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 1), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2)]

def cache_347_H_part1 : List Cell := [(4, 3), (4, 4), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5)]

def cache_347_H : List Cell := (cache_347_H_part0 ++ cache_347_H_part1)

def cache_347 : ListRow := ⟨cache_347_A, cache_347_H, 11⟩

def cache_348_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, -1), (0, -2), (0, -1), (1, -1), (1, 0)]

def cache_348_A : List Cell := cache_348_A_part0

def cache_348_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, -2)]

def cache_348_H_part1 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def cache_348_H : List Cell := (cache_348_H_part0 ++ cache_348_H_part1)

def cache_348 : ListRow := ⟨cache_348_A, cache_348_H, 11⟩

def cache_349_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (0, -1)]

def cache_349_A : List Cell := cache_349_A_part0

def cache_349_H_part0 : List Cell := [(-4, 0), (-3, 0), (-2, -4), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2)]

def cache_349_H_part1 : List Cell := [(3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)]

def cache_349_H : List Cell := (cache_349_H_part0 ++ cache_349_H_part1)

def cache_349 : ListRow := ⟨cache_349_A, cache_349_H, 11⟩

def cache_350_A_part0 : List Cell := [(-1, 0), (-1, 1), (1, 0), (1, 2)]

def cache_350_A : List Cell := cache_350_A_part0

def cache_350_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 3)]

def cache_350_H_part1 : List Cell := [(2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_350_H : List Cell := (cache_350_H_part0 ++ cache_350_H_part1)

def cache_350 : ListRow := ⟨cache_350_A, cache_350_H, 8⟩

def cache_351_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (-1, 0)]

def cache_351_A : List Cell := cache_351_A_part0

def cache_351_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_351_H_part1 : List Cell := [(1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_351_H : List Cell := (cache_351_H_part0 ++ cache_351_H_part1)

def cache_351 : ListRow := ⟨cache_351_A, cache_351_H, 11⟩

def cache_352_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2), (3, -1)]

def cache_352_A : List Cell := cache_352_A_part0

def cache_352_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_352_H_part1 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def cache_352_H : List Cell := (cache_352_H_part0 ++ cache_352_H_part1)

def cache_352 : ListRow := ⟨cache_352_A, cache_352_H, 11⟩

def cache_353_A_part0 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)]

def cache_353_A : List Cell := cache_353_A_part0

def cache_353_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0)]

def cache_353_H_part1 : List Cell := [(1, 1), (1, 2), (1, 3), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_353_H : List Cell := (cache_353_H_part0 ++ cache_353_H_part1)

def cache_353 : ListRow := ⟨cache_353_A, cache_353_H, 12⟩

def cache_354_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 1), (1, -2)]

def cache_354_A : List Cell := cache_354_A_part0

def cache_354_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0)]

def cache_354_H_part1 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0)]

def cache_354_H : List Cell := (cache_354_H_part0 ++ cache_354_H_part1)

def cache_354 : ListRow := ⟨cache_354_A, cache_354_H, 11⟩

def cache_355_A_part0 : List Cell := [(1, -1), (1, 0), (2, -1), (2, 0)]

def cache_355_A : List Cell := cache_355_A_part0

def cache_355_H_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1)]

def cache_355_H_part1 : List Cell := [(3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)]

def cache_355_H : List Cell := (cache_355_H_part0 ++ cache_355_H_part1)

def cache_355 : ListRow := ⟨cache_355_A, cache_355_H, 10⟩

def cache_356_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)]

def cache_356_A : List Cell := cache_356_A_part0

def cache_356_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)]

def cache_356_H : List Cell := cache_356_H_part0

def cache_356 : ListRow := ⟨cache_356_A, cache_356_H, 8⟩

def cache_357_A_part0 : List Cell := [(-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 2)]

def cache_357_A : List Cell := cache_357_A_part0

def cache_357_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_357_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 3)]

def cache_357_H : List Cell := (cache_357_H_part0 ++ cache_357_H_part1)

def cache_357 : ListRow := ⟨cache_357_A, cache_357_H, 10⟩

def cache_358_A_part0 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)]

def cache_358_A : List Cell := cache_358_A_part0

def cache_358_H_part0 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0)]

def cache_358_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_358_H : List Cell := (cache_358_H_part0 ++ cache_358_H_part1)

def cache_358 : ListRow := ⟨cache_358_A, cache_358_H, 11⟩

def cache_359_A_part0 : List Cell := [(-1, -1), (-1, 1), (0, -1), (0, 1)]

def cache_359_A : List Cell := cache_359_A_part0

def cache_359_H_part0 : List Cell := [(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0)]

def cache_359_H_part1 : List Cell := [(2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)]

def cache_359_H : List Cell := (cache_359_H_part0 ++ cache_359_H_part1)

def cache_359 : ListRow := ⟨cache_359_A, cache_359_H, 9⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_360_A_part0 : List Cell := [(-2, -2), (0, -4), (0, -3), (0, -2), (0, -1)]

def cache_360_A : List Cell := cache_360_A_part0

def cache_360_H_part0 : List Cell := [(-3, -1), (-2, -2), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2)]

def cache_360_H_part1 : List Cell := [(2, -1), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)]

def cache_360_H : List Cell := (cache_360_H_part0 ++ cache_360_H_part1)

def cache_360 : ListRow := ⟨cache_360_A, cache_360_H, 10⟩

def cache_361_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (2, -1), (3, -1), (3, 0)]

def cache_361_A : List Cell := cache_361_A_part0

def cache_361_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_361_H_part1 : List Cell := [(2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3)]

def cache_361_H : List Cell := (cache_361_H_part0 ++ cache_361_H_part1)

def cache_361 : ListRow := ⟨cache_361_A, cache_361_H, 12⟩

def cache_362_A_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 2), (-2, -1), (-1, -1), (-1, 2)]

def cache_362_A : List Cell := cache_362_A_part0

def cache_362_H_part0 : List Cell := [(-6, 3), (-5, 2), (-5, 3), (-4, -1), (-4, 2), (-4, 3), (-3, -1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1)]

def cache_362_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]

def cache_362_H : List Cell := (cache_362_H_part0 ++ cache_362_H_part1)

def cache_362 : ListRow := ⟨cache_362_A, cache_362_H, 11⟩

def cache_363_A_part0 : List Cell := [(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)]

def cache_363_A : List Cell := cache_363_A_part0

def cache_363_H_part0 : List Cell := [(-5, -1), (-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -1), (-3, 0), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2)]

def cache_363_H_part1 : List Cell := [(1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)]

def cache_363_H : List Cell := (cache_363_H_part0 ++ cache_363_H_part1)

def cache_363 : ListRow := ⟨cache_363_A, cache_363_H, 9⟩

def cache_364_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_364_A : List Cell := cache_364_A_part0

def cache_364_H_part0 : List Cell := [(-4, -4), (-4, -2), (-3, -4), (-3, -3), (-3, -2), (-2, -4), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2)]

def cache_364_H_part1 : List Cell := [(2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)]

def cache_364_H : List Cell := (cache_364_H_part0 ++ cache_364_H_part1)

def cache_364 : ListRow := ⟨cache_364_A, cache_364_H, 10⟩

def cache_365_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (1, -3)]

def cache_365_A : List Cell := cache_365_A_part0

def cache_365_H_part0 : List Cell := [(-3, -1), (-2, -2), (-2, -1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_365_H_part1 : List Cell := [(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_365_H : List Cell := (cache_365_H_part0 ++ cache_365_H_part1)

def cache_365 : ListRow := ⟨cache_365_A, cache_365_H, 12⟩

def cache_366_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)]

def cache_366_A : List Cell := cache_366_A_part0

def cache_366_H_part0 : List Cell := [(-2, -3), (-1, -3), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)]

def cache_366_H_part1 : List Cell := [(3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 1)]

def cache_366_H : List Cell := (cache_366_H_part0 ++ cache_366_H_part1)

def cache_366 : ListRow := ⟨cache_366_A, cache_366_H, 11⟩

def cache_367_A_part0 : List Cell := [(-3, 1), (-3, 2), (-2, 1), (-1, 1), (0, 1)]

def cache_367_A : List Cell := cache_367_A_part0

def cache_367_H_part0 : List Cell := [(-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3)]

def cache_367_H_part1 : List Cell := [(0, 4), (0, 5), (0, 6), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_367_H : List Cell := (cache_367_H_part0 ++ cache_367_H_part1)

def cache_367 : ListRow := ⟨cache_367_A, cache_367_H, 13⟩

def cache_368_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_368_A : List Cell := cache_368_A_part0

def cache_368_H_part0 : List Cell := [(-4, -3), (-3, -3), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_368_H_part1 : List Cell := [(1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)]

def cache_368_H : List Cell := (cache_368_H_part0 ++ cache_368_H_part1)

def cache_368 : ListRow := ⟨cache_368_A, cache_368_H, 12⟩

def cache_369_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1)]

def cache_369_A : List Cell := cache_369_A_part0

def cache_369_H_part0 : List Cell := [(-4, -2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1)]

def cache_369_H_part1 : List Cell := [(-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_369_H : List Cell := (cache_369_H_part0 ++ cache_369_H_part1)

def cache_369 : ListRow := ⟨cache_369_A, cache_369_H, 14⟩

def cache_370_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0)]

def cache_370_A : List Cell := cache_370_A_part0

def cache_370_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_370_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 2), (4, 2)]

def cache_370_H : List Cell := (cache_370_H_part0 ++ cache_370_H_part1)

def cache_370 : ListRow := ⟨cache_370_A, cache_370_H, 11⟩

def cache_371_A_part0 : List Cell := [(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)]

def cache_371_A : List Cell := cache_371_A_part0

def cache_371_H_part0 : List Cell := [(-6, 1), (-5, 0), (-5, 1), (-4, -3), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3)]

def cache_371_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)]

def cache_371_H : List Cell := (cache_371_H_part0 ++ cache_371_H_part1)

def cache_371 : ListRow := ⟨cache_371_A, cache_371_H, 9⟩

def cache_372_A_part0 : List Cell := [(-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2)]

def cache_372_A : List Cell := cache_372_A_part0

def cache_372_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0)]

def cache_372_H_part1 : List Cell := [(1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_372_H : List Cell := (cache_372_H_part0 ++ cache_372_H_part1)

def cache_372 : ListRow := ⟨cache_372_A, cache_372_H, 11⟩

def cache_373_A_part0 : List Cell := [(-1, -1), (0, -1), (0, 1), (2, -1), (2, 0), (2, 1)]

def cache_373_A : List Cell := cache_373_A_part0

def cache_373_H_part0 : List Cell := [(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0)]

def cache_373_H_part1 : List Cell := [(3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0)]

def cache_373_H : List Cell := (cache_373_H_part0 ++ cache_373_H_part1)

def cache_373 : ListRow := ⟨cache_373_A, cache_373_H, 9⟩

def cache_374_A_part0 : List Cell := [(1, -2), (1, 0), (2, -1), (2, 0)]

def cache_374_A : List Cell := cache_374_A_part0

def cache_374_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0)]

def cache_374_H_part1 : List Cell := [(3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)]

def cache_374_H : List Cell := (cache_374_H_part0 ++ cache_374_H_part1)

def cache_374 : ListRow := ⟨cache_374_A, cache_374_H, 10⟩

def cache_375_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 1), (0, -1), (0, 1)]

def cache_375_A : List Cell := cache_375_A_part0

def cache_375_H_part0 : List Cell := [(-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)]

def cache_375_H_part1 : List Cell := [(1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)]

def cache_375_H : List Cell := (cache_375_H_part0 ++ cache_375_H_part1)

def cache_375 : ListRow := ⟨cache_375_A, cache_375_H, 9⟩

def cache_376_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -1), (-1, 0)]

def cache_376_A : List Cell := cache_376_A_part0

def cache_376_H_part0 : List Cell := [(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1)]

def cache_376_H_part1 : List Cell := [(0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_376_H : List Cell := (cache_376_H_part0 ++ cache_376_H_part1)

def cache_376 : ListRow := ⟨cache_376_A, cache_376_H, 10⟩

def cache_377_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)]

def cache_377_A : List Cell := cache_377_A_part0

def cache_377_H_part0 : List Cell := [(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1)]

def cache_377_H_part1 : List Cell := [(3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_377_H : List Cell := (cache_377_H_part0 ++ cache_377_H_part1)

def cache_377 : ListRow := ⟨cache_377_A, cache_377_H, 12⟩

def cache_378_A_part0 : List Cell := [(-2, 0), (-1, -2), (-1, 0)]

def cache_378_A : List Cell := cache_378_A_part0

def cache_378_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1)]

def cache_378_H_part1 : List Cell := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)]

def cache_378_H : List Cell := (cache_378_H_part0 ++ cache_378_H_part1)

def cache_378 : ListRow := ⟨cache_378_A, cache_378_H, 11⟩

def cache_379_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_379_A : List Cell := cache_379_A_part0

def cache_379_H_part0 : List Cell := [(-3, -3), (-2, -3), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1)]

def cache_379_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)]

def cache_379_H : List Cell := (cache_379_H_part0 ++ cache_379_H_part1)

def cache_379 : ListRow := ⟨cache_379_A, cache_379_H, 13⟩

def cache_380_A_part0 : List Cell := [(-2, 0), (-2, 2), (-1, -1), (-1, 0)]

def cache_380_A : List Cell := cache_380_A_part0

def cache_380_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1)]

def cache_380_H_part1 : List Cell := [(0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_380_H : List Cell := (cache_380_H_part0 ++ cache_380_H_part1)

def cache_380 : ListRow := ⟨cache_380_A, cache_380_H, 8⟩

def cache_381_A_part0 : List Cell := [(1, 0), (2, -1), (2, 0), (2, 1)]

def cache_381_A : List Cell := cache_381_A_part0

def cache_381_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1)]

def cache_381_H_part1 : List Cell := [(2, 2), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)]

def cache_381_H : List Cell := (cache_381_H_part0 ++ cache_381_H_part1)

def cache_381 : ListRow := ⟨cache_381_A, cache_381_H, 10⟩

def cache_382_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)]

def cache_382_A : List Cell := cache_382_A_part0

def cache_382_H_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_382_H : List Cell := cache_382_H_part0

def cache_382 : ListRow := ⟨cache_382_A, cache_382_H, 5⟩

def cache_383_A_part0 : List Cell := [(-1, 0), (-1, 2), (1, 0)]

def cache_383_A : List Cell := cache_383_A_part0

def cache_383_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, -1)]

def cache_383_H_part1 : List Cell := [(1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_383_H : List Cell := (cache_383_H_part0 ++ cache_383_H_part1)

def cache_383 : ListRow := ⟨cache_383_A, cache_383_H, 8⟩

def cache_384_A_part0 : List Cell := [(-1, 0), (1, 0)]

def cache_384_A : List Cell := cache_384_A_part0

def cache_384_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_384_H_part1 : List Cell := [(2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)]

def cache_384_H : List Cell := (cache_384_H_part0 ++ cache_384_H_part1)

def cache_384 : ListRow := ⟨cache_384_A, cache_384_H, 11⟩

def cache_385_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_385_A : List Cell := cache_385_A_part0

def cache_385_H_part0 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1)]

def cache_385_H_part1 : List Cell := [(0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 1)]

def cache_385_H : List Cell := (cache_385_H_part0 ++ cache_385_H_part1)

def cache_385 : ListRow := ⟨cache_385_A, cache_385_H, 15⟩

def cache_386_A_part0 : List Cell := [(-2, 0), (-1, -2), (-1, 0)]

def cache_386_A : List Cell := cache_386_A_part0

def cache_386_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0)]

def cache_386_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_386_H : List Cell := (cache_386_H_part0 ++ cache_386_H_part1)

def cache_386 : ListRow := ⟨cache_386_A, cache_386_H, 10⟩

def cache_387_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (0, 1)]

def cache_387_A : List Cell := cache_387_A_part0

def cache_387_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2)]

def cache_387_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 2), (5, 2)]

def cache_387_H : List Cell := (cache_387_H_part0 ++ cache_387_H_part1)

def cache_387 : ListRow := ⟨cache_387_A, cache_387_H, 12⟩

def cache_388_A_part0 : List Cell := [(0, -2), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_388_A : List Cell := cache_388_A_part0

def cache_388_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3)]

def cache_388_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_388_H : List Cell := (cache_388_H_part0 ++ cache_388_H_part1)

def cache_388 : ListRow := ⟨cache_388_A, cache_388_H, 11⟩

def cache_389_A_part0 : List Cell := [(-2, -2), (0, -2), (0, -1)]

def cache_389_A : List Cell := cache_389_A_part0

def cache_389_H_part0 : List Cell := [(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0)]

def cache_389_H_part1 : List Cell := [(0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (3, 1), (4, 1)]

def cache_389_H : List Cell := (cache_389_H_part0 ++ cache_389_H_part1)

def cache_389 : ListRow := ⟨cache_389_A, cache_389_H, 8⟩

def cache_390_A_part0 : List Cell := [(-1, -2), (-1, -1), (0, -2), (0, -1)]

def cache_390_A : List Cell := cache_390_A_part0

def cache_390_H_part0 : List Cell := [(-4, -5), (-3, -5), (-3, -4), (-2, -5), (-2, -4), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1)]

def cache_390_H_part1 : List Cell := [(1, 0), (1, 1), (1, 2), (2, -5), (2, -4), (2, -2), (3, -5), (3, -4), (3, -3), (3, -2), (4, -5), (4, -4), (4, -3), (5, -5), (5, -4), (5, -3)]

def cache_390_H : List Cell := (cache_390_H_part0 ++ cache_390_H_part1)

def cache_390 : ListRow := ⟨cache_390_A, cache_390_H, 12⟩

def cache_391_A_part0 : List Cell := [(-1, -1), (0, -2), (0, -1), (0, 1), (1, -2)]

def cache_391_A : List Cell := cache_391_A_part0

def cache_391_H_part0 : List Cell := [(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2)]

def cache_391_H_part1 : List Cell := [(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)]

def cache_391_H : List Cell := (cache_391_H_part0 ++ cache_391_H_part1)

def cache_391 : ListRow := ⟨cache_391_A, cache_391_H, 12⟩

def cache_392_A_part0 : List Cell := [(-1, -2), (0, -2), (0, -1)]

def cache_392_A : List Cell := cache_392_A_part0

def cache_392_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5)]

def cache_392_H_part1 : List Cell := [(1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_392_H : List Cell := (cache_392_H_part0 ++ cache_392_H_part1)

def cache_392 : ListRow := ⟨cache_392_A, cache_392_H, 11⟩

def cache_393_A_part0 : List Cell := [(0, -2), (0, -1), (1, -2), (2, -3), (2, -2), (3, -2), (3, -1)]

def cache_393_A : List Cell := cache_393_A_part0

def cache_393_H_part0 : List Cell := [(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_393_H_part1 : List Cell := [(2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_393_H : List Cell := (cache_393_H_part0 ++ cache_393_H_part1)

def cache_393 : ListRow := ⟨cache_393_A, cache_393_H, 12⟩

def cache_394_A_part0 : List Cell := [(-2, -1), (-2, 0), (0, -1)]

def cache_394_A : List Cell := cache_394_A_part0

def cache_394_H_part0 : List Cell := [(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0)]

def cache_394_H_part1 : List Cell := [(1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1)]

def cache_394_H : List Cell := (cache_394_H_part0 ++ cache_394_H_part1)

def cache_394 : ListRow := ⟨cache_394_A, cache_394_H, 9⟩

def cache_395_A_part0 : List Cell := [(-1, 0), (1, -1), (1, 0), (1, 1)]

def cache_395_A : List Cell := cache_395_A_part0

def cache_395_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2)]

def cache_395_H_part1 : List Cell := [(0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_395_H : List Cell := (cache_395_H_part0 ++ cache_395_H_part1)

def cache_395 : ListRow := ⟨cache_395_A, cache_395_H, 11⟩

def cache_396_A_part0 : List Cell := [(0, -2), (0, -1), (1, -2), (2, -2), (3, -2)]

def cache_396_A : List Cell := cache_396_A_part0

def cache_396_H_part0 : List Cell := [(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_396_H_part1 : List Cell := [(2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_396_H : List Cell := (cache_396_H_part0 ++ cache_396_H_part1)

def cache_396 : ListRow := ⟨cache_396_A, cache_396_H, 13⟩

def cache_397_A_part0 : List Cell := [(0, -2), (1, -2), (1, -1), (1, 0)]

def cache_397_A : List Cell := cache_397_A_part0

def cache_397_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4)]

def cache_397_H_part1 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_397_H : List Cell := (cache_397_H_part0 ++ cache_397_H_part1)

def cache_397 : ListRow := ⟨cache_397_A, cache_397_H, 11⟩

def cache_398_A_part0 : List Cell := [(-3, -4), (-3, -3), (-3, -2), (-2, -3), (-2, 0), (-1, -3), (0, -3)]

def cache_398_A : List Cell := cache_398_A_part0

def cache_398_H_part0 : List Cell := [(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)]

def cache_398_H_part1 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_398_H : List Cell := (cache_398_H_part0 ++ cache_398_H_part1)

def cache_398 : ListRow := ⟨cache_398_A, cache_398_H, 10⟩

def cache_399_A_part0 : List Cell := [(-2, -2), (0, -2), (0, -1)]

def cache_399_A : List Cell := cache_399_A_part0

def cache_399_H_part0 : List Cell := [(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-2, -2), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)]

def cache_399_H_part1 : List Cell := [(0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2)]

def cache_399_H : List Cell := (cache_399_H_part0 ++ cache_399_H_part1)

def cache_399 : ListRow := ⟨cache_399_A, cache_399_H, 11⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_400_A_part0 : List Cell := [(-1, -2), (-1, 0), (1, -2), (1, 0)]

def cache_400_A : List Cell := cache_400_A_part0

def cache_400_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0)]

def cache_400_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1)]

def cache_400_H : List Cell := (cache_400_H_part0 ++ cache_400_H_part1)

def cache_400 : ListRow := ⟨cache_400_A, cache_400_H, 10⟩

def cache_401_A_part0 : List Cell := [(-1, -1), (0, -1), (0, 1)]

def cache_401_A : List Cell := cache_401_A_part0

def cache_401_H_part0 : List Cell := [(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3)]

def cache_401_H_part1 : List Cell := [(1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)]

def cache_401_H : List Cell := (cache_401_H_part0 ++ cache_401_H_part1)

def cache_401 : ListRow := ⟨cache_401_A, cache_401_H, 11⟩

def cache_402_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)]

def cache_402_A : List Cell := cache_402_A_part0

def cache_402_H_part0 : List Cell := [(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0)]

def cache_402_H_part1 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_402_H : List Cell := (cache_402_H_part0 ++ cache_402_H_part1)

def cache_402 : ListRow := ⟨cache_402_A, cache_402_H, 12⟩

def cache_403_A_part0 : List Cell := [(-1, -2), (0, -3), (0, -2), (0, -1)]

def cache_403_A : List Cell := cache_403_A_part0

def cache_403_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3)]

def cache_403_H_part1 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_403_H : List Cell := (cache_403_H_part0 ++ cache_403_H_part1)

def cache_403 : ListRow := ⟨cache_403_A, cache_403_H, 12⟩

def cache_404_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2)]

def cache_404_A : List Cell := cache_404_A_part0

def cache_404_H_part0 : List Cell := [(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2)]

def cache_404_H_part1 : List Cell := [(0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)]

def cache_404_H : List Cell := (cache_404_H_part0 ++ cache_404_H_part1)

def cache_404 : ListRow := ⟨cache_404_A, cache_404_H, 12⟩

def cache_405_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2), (1, -3)]

def cache_405_A : List Cell := cache_405_A_part0

def cache_405_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_405_H_part1 : List Cell := [(-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_405_H : List Cell := (cache_405_H_part0 ++ cache_405_H_part1)

def cache_405 : ListRow := ⟨cache_405_A, cache_405_H, 13⟩

def cache_406_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_406_A : List Cell := cache_406_A_part0

def cache_406_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5)]

def cache_406_H_part1 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1)]

def cache_406_H : List Cell := (cache_406_H_part0 ++ cache_406_H_part1)

def cache_406 : ListRow := ⟨cache_406_A, cache_406_H, 11⟩

def cache_407_A_part0 : List Cell := [(0, 1), (0, 2), (0, 3)]

def cache_407_A : List Cell := cache_407_A_part0

def cache_407_H_part0 : List Cell := [(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1)]

def cache_407_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)]

def cache_407_H : List Cell := (cache_407_H_part0 ++ cache_407_H_part1)

def cache_407 : ListRow := ⟨cache_407_A, cache_407_H, 10⟩

def cache_408_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)]

def cache_408_A : List Cell := cache_408_A_part0

def cache_408_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0)]

def cache_408_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_408_H : List Cell := (cache_408_H_part0 ++ cache_408_H_part1)

def cache_408 : ListRow := ⟨cache_408_A, cache_408_H, 11⟩

def cache_409_A_part0 : List Cell := [(0, -3), (0, -2), (1, -3), (2, -1), (2, 0)]

def cache_409_A : List Cell := cache_409_A_part0

def cache_409_H_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_409_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_409_H : List Cell := (cache_409_H_part0 ++ cache_409_H_part1)

def cache_409 : ListRow := ⟨cache_409_A, cache_409_H, 12⟩

def cache_410_A_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1)]

def cache_410_A : List Cell := cache_410_A_part0

def cache_410_H_part0 : List Cell := [(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6)]

def cache_410_H_part1 : List Cell := [(-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2)]

def cache_410_H : List Cell := (cache_410_H_part0 ++ cache_410_H_part1)

def cache_410 : ListRow := ⟨cache_410_A, cache_410_H, 14⟩

def cache_411_A_part0 : List Cell := [(1, 0), (2, 0)]

def cache_411_A : List Cell := cache_411_A_part0

def cache_411_H_part0 : List Cell := [(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_411_H_part1 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 3)]

def cache_411_H : List Cell := (cache_411_H_part0 ++ cache_411_H_part1)

def cache_411 : ListRow := ⟨cache_411_A, cache_411_H, 14⟩

def cache_412_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)]

def cache_412_A : List Cell := cache_412_A_part0

def cache_412_H_part0 : List Cell := [(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_412_H_part1 : List Cell := [(-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1)]

def cache_412_H_part2 : List Cell := [(4, 3)]

def cache_412_H : List Cell := (cache_412_H_part0 ++ (cache_412_H_part1 ++ cache_412_H_part2))

def cache_412 : ListRow := ⟨cache_412_A, cache_412_H, 13⟩

def cache_413_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 1), (0, 1), (0, 2)]

def cache_413_A : List Cell := cache_413_A_part0

def cache_413_H_part0 : List Cell := [(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)]

def cache_413_H_part1 : List Cell := [(-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)]

def cache_413_H_part2 : List Cell := [(5, 2)]

def cache_413_H : List Cell := (cache_413_H_part0 ++ (cache_413_H_part1 ++ cache_413_H_part2))

def cache_413 : ListRow := ⟨cache_413_A, cache_413_H, 13⟩

def cache_414_A_part0 : List Cell := [(-1, -1), (-1, 1), (0, -1), (0, 1)]

def cache_414_A : List Cell := cache_414_A_part0

def cache_414_H_part0 : List Cell := [(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 3)]

def cache_414_H_part1 : List Cell := [(-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (2, 1), (2, 2), (3, -2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def cache_414_H_part2 : List Cell := [(5, 0)]

def cache_414_H : List Cell := (cache_414_H_part0 ++ (cache_414_H_part1 ++ cache_414_H_part2))

def cache_414 : ListRow := ⟨cache_414_A, cache_414_H, 11⟩

def cache_415_A_part0 : List Cell := [(-3, -3), (-2, -3), (-2, 0), (-1, -3), (0, -3)]

def cache_415_A : List Cell := cache_415_A_part0

def cache_415_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)]

def cache_415_H_part1 : List Cell := [(0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -1), (3, 0), (3, 1)]

def cache_415_H_part2 : List Cell := [(4, -1), (4, 0), (4, 1)]

def cache_415_H : List Cell := (cache_415_H_part0 ++ (cache_415_H_part1 ++ cache_415_H_part2))

def cache_415 : ListRow := ⟨cache_415_A, cache_415_H, 12⟩

def cache_416_A_part0 : List Cell := [(-2, 0), (-1, 0)]

def cache_416_A : List Cell := cache_416_A_part0

def cache_416_H_part0 : List Cell := [(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)]

def cache_416_H_part1 : List Cell := [(-2, 6), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_416_H_part2 : List Cell := [(3, -1), (3, 0), (3, 1), (4, 1)]

def cache_416_H : List Cell := (cache_416_H_part0 ++ (cache_416_H_part1 ++ cache_416_H_part2))

def cache_416 : ListRow := ⟨cache_416_A, cache_416_H, 16⟩

def cache_417_A_part0 : List Cell := [(-2, -3), (-2, -2), (-1, -3), (0, -3), (0, -1), (1, -3)]

def cache_417_A : List Cell := cache_417_A_part0

def cache_417_H_part0 : List Cell := [(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)]

def cache_417_H_part1 : List Cell := [(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0)]

def cache_417_H_part2 : List Cell := [(3, 1), (4, -1), (4, 0), (4, 1)]

def cache_417_H : List Cell := (cache_417_H_part0 ++ (cache_417_H_part1 ++ cache_417_H_part2))

def cache_417 : ListRow := ⟨cache_417_A, cache_417_H, 13⟩

def cache_418_A_part0 : List Cell := [(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)]

def cache_418_A : List Cell := cache_418_A_part0

def cache_418_H_part0 : List Cell := [(-5, 0), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1)]

def cache_418_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]

def cache_418_H_part2 : List Cell := [(3, 2), (4, 0), (4, 1), (4, 2), (5, 0)]

def cache_418_H : List Cell := (cache_418_H_part0 ++ (cache_418_H_part1 ++ cache_418_H_part2))

def cache_418 : ListRow := ⟨cache_418_A, cache_418_H, 14⟩

def cache_419_A_part0 : List Cell := [(-3, -3), (-2, -3), (-2, -2), (-1, -3), (0, -3)]

def cache_419_A : List Cell := cache_419_A_part0

def cache_419_H_part0 : List Cell := [(-5, 1), (-4, -4), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4)]

def cache_419_H_part1 : List Cell := [(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1)]

def cache_419_H_part2 : List Cell := [(3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_419_H : List Cell := (cache_419_H_part0 ++ (cache_419_H_part1 ++ cache_419_H_part2))

def cache_419 : ListRow := ⟨cache_419_A, cache_419_H, 13⟩

def cache_420_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3)]

def cache_420_A : List Cell := cache_420_A_part0

def cache_420_H_part0 : List Cell := [(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2)]

def cache_420_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_420_H_part2 : List Cell := [(5, -4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_420_H : List Cell := (cache_420_H_part0 ++ (cache_420_H_part1 ++ cache_420_H_part2))

def cache_420 : ListRow := ⟨cache_420_A, cache_420_H, 13⟩

def cache_421_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (1, 0)]

def cache_421_A : List Cell := cache_421_A_part0

def cache_421_H_part0 : List Cell := [(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0)]

def cache_421_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3)]

def cache_421_H_part2 : List Cell := [(3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)]

def cache_421_H : List Cell := (cache_421_H_part0 ++ (cache_421_H_part1 ++ cache_421_H_part2))

def cache_421 : ListRow := ⟨cache_421_A, cache_421_H, 12⟩

def cache_422_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2)]

def cache_422_A : List Cell := cache_422_A_part0

def cache_422_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_422_H_part1 : List Cell := [(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_422_H_part2 : List Cell := [(5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)]

def cache_422_H : List Cell := (cache_422_H_part0 ++ (cache_422_H_part1 ++ cache_422_H_part2))

def cache_422 : ListRow := ⟨cache_422_A, cache_422_H, 14⟩

def cache_423_A_part0 : List Cell := [(-1, -2), (-1, 0), (0, -2)]

def cache_423_A : List Cell := cache_423_A_part0

def cache_423_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -2), (-1, -1), (-1, 0)]

def cache_423_H_part1 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_423_H_part2 : List Cell := [(2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)]

def cache_423_H : List Cell := (cache_423_H_part0 ++ (cache_423_H_part1 ++ cache_423_H_part2))

def cache_423 : ListRow := ⟨cache_423_A, cache_423_H, 12⟩

def cache_424_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (2, -1)]

def cache_424_A : List Cell := cache_424_A_part0

def cache_424_H_part0 : List Cell := [(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2)]

def cache_424_H_part1 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0)]

def cache_424_H_part2 : List Cell := [(5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)]

def cache_424_H : List Cell := (cache_424_H_part0 ++ (cache_424_H_part1 ++ cache_424_H_part2))

def cache_424 : ListRow := ⟨cache_424_A, cache_424_H, 10⟩

def cache_425_A_part0 : List Cell := [(-1, -2), (-1, 0), (0, -2)]

def cache_425_A : List Cell := cache_425_A_part0

def cache_425_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_425_H_part1 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_425_H_part2 : List Cell := [(2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)]

def cache_425_H : List Cell := (cache_425_H_part0 ++ (cache_425_H_part1 ++ cache_425_H_part2))

def cache_425 : ListRow := ⟨cache_425_A, cache_425_H, 12⟩

def cache_426_A_part0 : List Cell := [(-1, -2), (0, -2), (0, -1)]

def cache_426_A : List Cell := cache_426_A_part0

def cache_426_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5)]

def cache_426_H_part1 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1)]

def cache_426_H_part2 : List Cell := [(3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0)]

def cache_426_H : List Cell := (cache_426_H_part0 ++ (cache_426_H_part1 ++ cache_426_H_part2))

def cache_426 : ListRow := ⟨cache_426_A, cache_426_H, 12⟩

def cache_427_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2)]

def cache_427_A : List Cell := cache_427_A_part0

def cache_427_H_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_427_H_part1 : List Cell := [(1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2)]

def cache_427_H_part2 : List Cell := [(4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)]

def cache_427_H : List Cell := (cache_427_H_part0 ++ (cache_427_H_part1 ++ cache_427_H_part2))

def cache_427 : ListRow := ⟨cache_427_A, cache_427_H, 14⟩

def cache_428_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)]

def cache_428_A : List Cell := cache_428_A_part0

def cache_428_H_part0 : List Cell := [(-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_428_H_part1 : List Cell := [(-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1)]

def cache_428_H_part2 : List Cell := [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_428_H : List Cell := (cache_428_H_part0 ++ (cache_428_H_part1 ++ cache_428_H_part2))

def cache_428 : ListRow := ⟨cache_428_A, cache_428_H, 17⟩

def cache_429_A_part0 : List Cell := [(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)]

def cache_429_A : List Cell := cache_429_A_part0

def cache_429_H_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1)]

def cache_429_H : List Cell := cache_429_H_part0

def cache_429 : ListRow := ⟨cache_429_A, cache_429_H, 6⟩

def cache_430_A_part0 : List Cell := [(-2, -2), (-2, -1), (-2, 0), (-1, -2), (0, -2)]

def cache_430_A : List Cell := cache_430_A_part0

def cache_430_H_part0 : List Cell := [(-7, -1), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2)]

def cache_430_H_part1 : List Cell := [(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3)]

def cache_430_H_part2 : List Cell := [(2, -1), (2, 0), (2, 1), (3, -3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_430_H : List Cell := (cache_430_H_part0 ++ (cache_430_H_part1 ++ cache_430_H_part2))

def cache_430 : ListRow := ⟨cache_430_A, cache_430_H, 10⟩

def cache_431_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (0, -3), (1, -3), (2, -3)]

def cache_431_A : List Cell := cache_431_A_part0

def cache_431_H_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_431_H_part1 : List Cell := [(1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)]

def cache_431_H_part2 : List Cell := [(4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1)]

def cache_431_H : List Cell := (cache_431_H_part0 ++ (cache_431_H_part1 ++ cache_431_H_part2))

def cache_431 : ListRow := ⟨cache_431_A, cache_431_H, 13⟩

def cache_432_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (1, -3), (1, -2)]

def cache_432_A : List Cell := cache_432_A_part0

def cache_432_H_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0)]

def cache_432_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2)]

def cache_432_H_part2 : List Cell := [(3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)]

def cache_432_H : List Cell := (cache_432_H_part0 ++ (cache_432_H_part1 ++ cache_432_H_part2))

def cache_432 : ListRow := ⟨cache_432_A, cache_432_H, 18⟩

def cache_433_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1)]

def cache_433_A : List Cell := cache_433_A_part0

def cache_433_H_part0 : List Cell := [(-3, -3), (-2, -3), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1)]

def cache_433_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_433_H_part2 : List Cell := [(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)]

def cache_433_H : List Cell := (cache_433_H_part0 ++ (cache_433_H_part1 ++ cache_433_H_part2))

def cache_433 : ListRow := ⟨cache_433_A, cache_433_H, 15⟩

def cache_434_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2)]

def cache_434_A : List Cell := cache_434_A_part0

def cache_434_H_part0 : List Cell := [(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2)]

def cache_434_H_part1 : List Cell := [(-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_434_H_part2 : List Cell := [(2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)]

def cache_434_H : List Cell := (cache_434_H_part0 ++ (cache_434_H_part1 ++ cache_434_H_part2))

def cache_434 : ListRow := ⟨cache_434_A, cache_434_H, 15⟩

def cache_435_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)]

def cache_435_A : List Cell := cache_435_A_part0

def cache_435_H_part0 : List Cell := [(-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_435_H_part1 : List Cell := [(2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)]

def cache_435_H_part2 : List Cell := [(5, 3), (5, 4), (5, 5), (5, 6), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)]

def cache_435_H : List Cell := (cache_435_H_part0 ++ (cache_435_H_part1 ++ cache_435_H_part2))

def cache_435 : ListRow := ⟨cache_435_A, cache_435_H, 14⟩

def cache_436_A_part0 : List Cell := [(0, -3), (0, -2), (1, -3), (1, -2)]

def cache_436_A : List Cell := cache_436_A_part0

def cache_436_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0)]

def cache_436_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1)]

def cache_436_H_part2 : List Cell := [(3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)]

def cache_436_H : List Cell := (cache_436_H_part0 ++ (cache_436_H_part1 ++ cache_436_H_part2))

def cache_436 : ListRow := ⟨cache_436_A, cache_436_H, 18⟩

def cache_437_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_437_A : List Cell := cache_437_A_part0

def cache_437_H_part0 : List Cell := [(-3, -3), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2)]

def cache_437_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_437_H_part2 : List Cell := [(4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)]

def cache_437_H : List Cell := (cache_437_H_part0 ++ (cache_437_H_part1 ++ cache_437_H_part2))

def cache_437 : ListRow := ⟨cache_437_A, cache_437_H, 15⟩

def cache_438_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0)]

def cache_438_A : List Cell := cache_438_A_part0

def cache_438_H_part0 : List Cell := [(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0)]

def cache_438_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2)]

def cache_438_H_part2 : List Cell := [(3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)]

def cache_438_H : List Cell := (cache_438_H_part0 ++ (cache_438_H_part1 ++ cache_438_H_part2))

def cache_438 : ListRow := ⟨cache_438_A, cache_438_H, 19⟩

def cache_439_A_part0 : List Cell := [(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0)]

def cache_439_A : List Cell := cache_439_A_part0

def cache_439_H_part0 : List Cell := [(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1)]

def cache_439_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0)]

def cache_439_H_part2 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)]

def cache_439_H : List Cell := (cache_439_H_part0 ++ (cache_439_H_part1 ++ cache_439_H_part2))

def cache_439 : ListRow := ⟨cache_439_A, cache_439_H, 15⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_440_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0), (1, 0)]

def cache_440_A : List Cell := cache_440_A_part0

def cache_440_H_part0 : List Cell := [(-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_440_H_part1 : List Cell := [(0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2)]

def cache_440_H_part2 : List Cell := [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)]

def cache_440_H : List Cell := (cache_440_H_part0 ++ (cache_440_H_part1 ++ cache_440_H_part2))

def cache_440 : ListRow := ⟨cache_440_A, cache_440_H, 15⟩

def cache_441_A_part0 : List Cell := [(0, 1), (1, 1), (2, 1), (3, 1)]

def cache_441_A : List Cell := cache_441_A_part0

def cache_441_H_part0 : List Cell := [(-2, 5), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_441_H_part1 : List Cell := [(2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_441_H_part2 : List Cell := [(5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)]

def cache_441_H : List Cell := (cache_441_H_part0 ++ (cache_441_H_part1 ++ cache_441_H_part2))

def cache_441 : ListRow := ⟨cache_441_A, cache_441_H, 15⟩

def cache_442_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1)]

def cache_442_A : List Cell := cache_442_A_part0

def cache_442_H_part0 : List Cell := [(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2)]

def cache_442_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_442_H_part2 : List Cell := [(4, 4), (4, 5), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)]

def cache_442_H : List Cell := (cache_442_H_part0 ++ (cache_442_H_part1 ++ cache_442_H_part2))

def cache_442 : ListRow := ⟨cache_442_A, cache_442_H, 16⟩

def cache_443_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (0, -1)]

def cache_443_A : List Cell := cache_443_A_part0

def cache_443_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0)]

def cache_443_H_part1 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1)]

def cache_443_H_part2 : List Cell := [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)]

def cache_443_H : List Cell := (cache_443_H_part0 ++ (cache_443_H_part1 ++ cache_443_H_part2))

def cache_443 : ListRow := ⟨cache_443_A, cache_443_H, 20⟩

def cache_444_A_part0 : List Cell := [(-2, -2), (-1, -2), (0, -2), (0, -1)]

def cache_444_A : List Cell := cache_444_A_part0

def cache_444_H_part0 : List Cell := [(-5, -3), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2)]

def cache_444_H_part1 : List Cell := [(-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0)]

def cache_444_H_part2 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)]

def cache_444_H : List Cell := (cache_444_H_part0 ++ (cache_444_H_part1 ++ cache_444_H_part2))

def cache_444 : ListRow := ⟨cache_444_A, cache_444_H, 14⟩

def cache_445_A_part0 : List Cell := [(1, 0), (1, 1), (2, 0), (2, 1)]

def cache_445_A : List Cell := cache_445_A_part0

def cache_445_H_part0 : List Cell := [(-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1)]

def cache_445_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2)]

def cache_445_H_part2 : List Cell := [(4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)]

def cache_445_H : List Cell := (cache_445_H_part0 ++ (cache_445_H_part1 ++ cache_445_H_part2))

def cache_445 : ListRow := ⟨cache_445_A, cache_445_H, 19⟩

def cache_446_A_part0 : List Cell := [(-1, -1), (1, 0), (2, 0), (3, 0), (3, 1)]

def cache_446_A : List Cell := cache_446_A_part0

def cache_446_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)]

def cache_446_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)]

def cache_446_H_part2 : List Cell := [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)]

def cache_446_H : List Cell := (cache_446_H_part0 ++ (cache_446_H_part1 ++ cache_446_H_part2))

def cache_446 : ListRow := ⟨cache_446_A, cache_446_H, 20⟩

def cache_447_A_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1)]

def cache_447_A : List Cell := cache_447_A_part0

def cache_447_H_part0 : List Cell := [(-6, 1), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4)]

def cache_447_H_part1 : List Cell := [(-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3)]

def cache_447_H_part2 : List Cell := [(1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)]

def cache_447_H : List Cell := (cache_447_H_part0 ++ (cache_447_H_part1 ++ cache_447_H_part2))

def cache_447 : ListRow := ⟨cache_447_A, cache_447_H, 19⟩

def cache_448_A_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, -1)]

def cache_448_A : List Cell := cache_448_A_part0

def cache_448_H_part0 : List Cell := [(-5, 1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1)]

def cache_448_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_448_H_part2 : List Cell := [(1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)]

def cache_448_H : List Cell := (cache_448_H_part0 ++ (cache_448_H_part1 ++ cache_448_H_part2))

def cache_448 : ListRow := ⟨cache_448_A, cache_448_H, 19⟩

def cache_449_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 0), (0, -4), (0, -3), (0, -2)]

def cache_449_A : List Cell := cache_449_A_part0

def cache_449_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2)]

def cache_449_H_part1 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_449_H_part2 : List Cell := [(2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)]

def cache_449_H : List Cell := (cache_449_H_part0 ++ (cache_449_H_part1 ++ cache_449_H_part2))

def cache_449 : ListRow := ⟨cache_449_A, cache_449_H, 16⟩

def cache_450_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)]

def cache_450_A : List Cell := cache_450_A_part0

def cache_450_H_part0 : List Cell := [(-2, 4), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1)]

def cache_450_H_part1 : List Cell := [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1)]

def cache_450_H_part2 : List Cell := [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_450_H : List Cell := (cache_450_H_part0 ++ (cache_450_H_part1 ++ cache_450_H_part2))

def cache_450 : ListRow := ⟨cache_450_A, cache_450_H, 16⟩

def cache_451_A_part0 : List Cell := [(0, -3), (0, -2), (1, -4), (1, -3), (1, -2)]

def cache_451_A : List Cell := cache_451_A_part0

def cache_451_H_part0 : List Cell := [(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3)]

def cache_451_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)]

def cache_451_H_part2 : List Cell := [(3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)]

def cache_451_H : List Cell := (cache_451_H_part0 ++ (cache_451_H_part1 ++ cache_451_H_part2))

def cache_451 : ListRow := ⟨cache_451_A, cache_451_H, 17⟩

def cache_452_A_part0 : List Cell := [(-1, 1), (-1, 2), (0, 1), (0, 2), (1, 2)]

def cache_452_A : List Cell := cache_452_A_part0

def cache_452_H_part0 : List Cell := [(-4, 5), (-4, 7), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0)]

def cache_452_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)]

def cache_452_H_part2 : List Cell := [(2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)]

def cache_452_H : List Cell := (cache_452_H_part0 ++ (cache_452_H_part1 ++ cache_452_H_part2))

def cache_452 : ListRow := ⟨cache_452_A, cache_452_H, 18⟩

def cache_453_A_part0 : List Cell := [(-1, -2), (-1, 0), (0, -2)]

def cache_453_A : List Cell := cache_453_A_part0

def cache_453_H_part0 : List Cell := [(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2)]

def cache_453_H_part1 : List Cell := [(-2, 3), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3)]

def cache_453_H_part2 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_453_H : List Cell := (cache_453_H_part0 ++ (cache_453_H_part1 ++ cache_453_H_part2))

def cache_453 : ListRow := ⟨cache_453_A, cache_453_H, 12⟩

def cache_454_A_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)]

def cache_454_A : List Cell := cache_454_A_part0

def cache_454_H_part0 : List Cell := [(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1)]

def cache_454_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_454_H_part2 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)]

def cache_454_H : List Cell := (cache_454_H_part0 ++ (cache_454_H_part1 ++ cache_454_H_part2))

def cache_454 : ListRow := ⟨cache_454_A, cache_454_H, 19⟩

def cache_455_A_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 1)]

def cache_455_A : List Cell := cache_455_A_part0

def cache_455_H_part0 : List Cell := [(-5, 2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0)]

def cache_455_H : List Cell := cache_455_H_part0

def cache_455 : ListRow := ⟨cache_455_A, cache_455_H, 5⟩

def cache_456_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_456_A : List Cell := cache_456_A_part0

def cache_456_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1)]

def cache_456_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, -1), (2, 1)]

def cache_456_H : List Cell := (cache_456_H_part0 ++ cache_456_H_part1)

def cache_456 : ListRow := ⟨cache_456_A, cache_456_H, 12⟩

def cache_457_A_part0 : List Cell := [(-1, -3), (-1, -1), (0, -1), (1, -1), (2, -1)]

def cache_457_A : List Cell := cache_457_A_part0

def cache_457_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)]

def cache_457_H_part1 : List Cell := [(-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_457_H_part2 : List Cell := [(2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1)]

def cache_457_H_part3 : List Cell := [(6, 3)]

def cache_457_H : List Cell := ((cache_457_H_part0 ++ cache_457_H_part1) ++ (cache_457_H_part2 ++ cache_457_H_part3))

def cache_457 : ListRow := ⟨cache_457_A, cache_457_H, 20⟩

def cache_458_A_part0 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)]

def cache_458_A : List Cell := cache_458_A_part0

def cache_458_H_part0 : List Cell := [(-5, 4), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3)]

def cache_458_H_part1 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0)]

def cache_458_H_part2 : List Cell := [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2)]

def cache_458_H_part3 : List Cell := [(4, 3), (4, 4)]

def cache_458_H : List Cell := ((cache_458_H_part0 ++ cache_458_H_part1) ++ (cache_458_H_part2 ++ cache_458_H_part3))

def cache_458 : ListRow := ⟨cache_458_A, cache_458_H, 17⟩

def cache_459_A_part0 : List Cell := [(-1, -1), (0, -2), (0, -1), (1, -1), (2, -1)]

def cache_459_A : List Cell := cache_459_A_part0

def cache_459_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)]

def cache_459_H_part1 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_459_H_part2 : List Cell := [(2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, 1), (5, 2), (5, 3)]

def cache_459_H_part3 : List Cell := [(6, 1), (6, 3)]

def cache_459_H : List Cell := ((cache_459_H_part0 ++ cache_459_H_part1) ++ (cache_459_H_part2 ++ cache_459_H_part3))

def cache_459 : ListRow := ⟨cache_459_A, cache_459_H, 20⟩

def cache_460_A_part0 : List Cell := [(-2, 0), (-1, 0)]

def cache_460_A : List Cell := cache_460_A_part0

def cache_460_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_460_H_part1 : List Cell := [(1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_460_H : List Cell := (cache_460_H_part0 ++ cache_460_H_part1)

def cache_460 : ListRow := ⟨cache_460_A, cache_460_H, 11⟩

def cache_461_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)]

def cache_461_A : List Cell := cache_461_A_part0

def cache_461_H_part0 : List Cell := [(-3, 4), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]

def cache_461_H_part1 : List Cell := [(1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2)]

def cache_461_H_part2 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)]

def cache_461_H_part3 : List Cell := [(6, 1), (6, 2), (6, 3), (6, 4)]

def cache_461_H : List Cell := ((cache_461_H_part0 ++ cache_461_H_part1) ++ (cache_461_H_part2 ++ cache_461_H_part3))

def cache_461 : ListRow := ⟨cache_461_A, cache_461_H, 18⟩

def cache_462_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0)]

def cache_462_A : List Cell := cache_462_A_part0

def cache_462_H_part0 : List Cell := [(-5, 3), (-5, 5), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3)]

def cache_462_H_part1 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_462_H_part2 : List Cell := [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2)]

def cache_462_H_part3 : List Cell := [(4, 3), (4, 4), (4, 5), (5, 3)]

def cache_462_H : List Cell := ((cache_462_H_part0 ++ cache_462_H_part1) ++ (cache_462_H_part2 ++ cache_462_H_part3))

def cache_462 : ListRow := ⟨cache_462_A, cache_462_H, 19⟩

def cache_463_A_part0 : List Cell := [(-2, -2), (-2, -1), (-1, -3), (-1, -1), (0, -1), (1, -1)]

def cache_463_A : List Cell := cache_463_A_part0

def cache_463_H_part0 : List Cell := [(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1)]

def cache_463_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)]

def cache_463_H_part2 : List Cell := [(2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -2), (4, -1), (4, 0), (4, 1)]

def cache_463_H_part3 : List Cell := [(4, 2), (4, 3), (5, 0), (5, 1), (5, 3)]

def cache_463_H : List Cell := ((cache_463_H_part0 ++ cache_463_H_part1) ++ (cache_463_H_part2 ++ cache_463_H_part3))

def cache_463 : ListRow := ⟨cache_463_A, cache_463_H, 20⟩

def cache_464_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)]

def cache_464_A : List Cell := cache_464_A_part0

def cache_464_H_part0 : List Cell := [(-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_464_H_part1 : List Cell := [(1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7)]

def cache_464_H_part2 : List Cell := [(3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3)]

def cache_464_H_part3 : List Cell := [(6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)]

def cache_464_H : List Cell := ((cache_464_H_part0 ++ cache_464_H_part1) ++ (cache_464_H_part2 ++ cache_464_H_part3))

def cache_464 : ListRow := ⟨cache_464_A, cache_464_H, 19⟩

def cache_465_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_465_A : List Cell := cache_465_A_part0

def cache_465_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1)]

def cache_465_H_part1 : List Cell := [(3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_465_H : List Cell := (cache_465_H_part0 ++ cache_465_H_part1)

def cache_465 : ListRow := ⟨cache_465_A, cache_465_H, 10⟩

def cache_466_A_part0 : List Cell := [(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2)]

def cache_466_A : List Cell := cache_466_A_part0

def cache_466_H_part0 : List Cell := [(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0)]

def cache_466_H_part1 : List Cell := [(-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3)]

def cache_466_H_part2 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1)]

def cache_466_H_part3 : List Cell := [(4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (5, 2)]

def cache_466_H : List Cell := ((cache_466_H_part0 ++ cache_466_H_part1) ++ (cache_466_H_part2 ++ cache_466_H_part3))

def cache_466 : ListRow := ⟨cache_466_A, cache_466_H, 14⟩

def cache_467_A_part0 : List Cell := [(0, 1), (0, 2), (0, 3)]

def cache_467_A : List Cell := cache_467_A_part0

def cache_467_H_part0 : List Cell := [(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4)]

def cache_467_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_467_H_part2 : List Cell := [(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_467_H_part3 : List Cell := [(7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)]

def cache_467_H : List Cell := ((cache_467_H_part0 ++ cache_467_H_part1) ++ (cache_467_H_part2 ++ cache_467_H_part3))

def cache_467 : ListRow := ⟨cache_467_A, cache_467_H, 21⟩

def cache_468_A_part0 : List Cell := [(0, 1), (0, 2), (1, 1), (2, 1), (3, 1)]

def cache_468_A : List Cell := cache_468_A_part0

def cache_468_H_part0 : List Cell := [(-2, 8), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_468_H_part1 : List Cell := [(1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9)]

def cache_468_H_part2 : List Cell := [(3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5)]

def cache_468_H_part3 : List Cell := [(6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (7, 8)]

def cache_468_H : List Cell := ((cache_468_H_part0 ++ cache_468_H_part1) ++ (cache_468_H_part2 ++ cache_468_H_part3))

def cache_468 : ListRow := ⟨cache_468_A, cache_468_H, 20⟩

def cache_469_A_part0 : List Cell := [(0, 1), (0, 2), (0, 3)]

def cache_469_A : List Cell := cache_469_A_part0

def cache_469_H_part0 : List Cell := [(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4)]

def cache_469_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_469_H_part2 : List Cell := [(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_469_H_part3 : List Cell := [(7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)]

def cache_469_H : List Cell := ((cache_469_H_part0 ++ cache_469_H_part1) ++ (cache_469_H_part2 ++ cache_469_H_part3))

def cache_469 : ListRow := ⟨cache_469_A, cache_469_H, 21⟩

def cache_470_A_part0 : List Cell := [(0, -1), (1, -1), (2, -1), (3, -1)]

def cache_470_A : List Cell := cache_470_A_part0

def cache_470_H_part0 : List Cell := [(-2, 6), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_470_H_part1 : List Cell := [(1, 5), (1, 6), (1, 7), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)]

def cache_470_H_part2 : List Cell := [(3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2)]

def cache_470_H_part3 : List Cell := [(6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6)]

def cache_470_H : List Cell := ((cache_470_H_part0 ++ cache_470_H_part1) ++ (cache_470_H_part2 ++ cache_470_H_part3))

def cache_470 : ListRow := ⟨cache_470_A, cache_470_H, 21⟩

def cache_471_A_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_471_A : List Cell := cache_471_A_part0

def cache_471_H_part0 : List Cell := [(-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 1), (-2, 2), (-2, 3), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2)]

def cache_471_H_part1 : List Cell := [(-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2)]

def cache_471_H_part2 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_471_H_part3 : List Cell := [(5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)]

def cache_471_H : List Cell := ((cache_471_H_part0 ++ cache_471_H_part1) ++ (cache_471_H_part2 ++ cache_471_H_part3))

def cache_471 : ListRow := ⟨cache_471_A, cache_471_H, 15⟩

def cache_472_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3)]

def cache_472_A : List Cell := cache_472_A_part0

def cache_472_H_part0 : List Cell := [(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1)]

def cache_472_H_part1 : List Cell := [(0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5)]

def cache_472_H_part2 : List Cell := [(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1)]

def cache_472_H_part3 : List Cell := [(6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)]

def cache_472_H : List Cell := ((cache_472_H_part0 ++ cache_472_H_part1) ++ (cache_472_H_part2 ++ cache_472_H_part3))

def cache_472 : ListRow := ⟨cache_472_A, cache_472_H, 15⟩

def cache_473_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 1)]

def cache_473_A : List Cell := cache_473_A_part0

def cache_473_H_part0 : List Cell := [(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, 0), (-2, 1), (-2, 2), (-2, 3)]

def cache_473_H_part1 : List Cell := [(-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]

def cache_473_H_part2 : List Cell := [(0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 2), (3, 3)]

def cache_473_H_part3 : List Cell := [(3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)]

def cache_473_H : List Cell := ((cache_473_H_part0 ++ cache_473_H_part1) ++ (cache_473_H_part2 ++ cache_473_H_part3))

def cache_473 : ListRow := ⟨cache_473_A, cache_473_H, 20⟩

def cache_474_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, 0), (3, 0)]

def cache_474_A : List Cell := cache_474_A_part0

def cache_474_H_part0 : List Cell := [(-3, 2), (-3, 4), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]

def cache_474_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]

def cache_474_H_part2 : List Cell := [(3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)]

def cache_474_H_part3 : List Cell := [(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)]

def cache_474_H : List Cell := ((cache_474_H_part0 ++ cache_474_H_part1) ++ (cache_474_H_part2 ++ cache_474_H_part3))

def cache_474 : ListRow := ⟨cache_474_A, cache_474_H, 21⟩

def cache_475_A_part0 : List Cell := [(-3, -2), (-3, 0), (-2, 0), (-1, 0)]

def cache_475_A : List Cell := cache_475_A_part0

def cache_475_H_part0 : List Cell := [(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7)]

def cache_475_H_part1 : List Cell := [(-3, 8), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1)]

def cache_475_H_part2 : List Cell := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)]

def cache_475_H_part3 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 4)]

def cache_475_H : List Cell := ((cache_475_H_part0 ++ cache_475_H_part1) ++ (cache_475_H_part2 ++ cache_475_H_part3))

def cache_475 : ListRow := ⟨cache_475_A, cache_475_H, 21⟩

def cache_476_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1), (1, 0)]

def cache_476_A : List Cell := cache_476_A_part0

def cache_476_H_part0 : List Cell := [(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1)]

def cache_476_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_476_H_part2 : List Cell := [(1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 1)]

def cache_476_H_part3 : List Cell := [(4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)]

def cache_476_H : List Cell := ((cache_476_H_part0 ++ cache_476_H_part1) ++ (cache_476_H_part2 ++ cache_476_H_part3))

def cache_476 : ListRow := ⟨cache_476_A, cache_476_H, 21⟩

def cache_477_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_477_A : List Cell := cache_477_A_part0

def cache_477_H_part0 : List Cell := [(-5, -3), (-5, -2), (-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-1, -7), (-1, -6), (-1, -5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -6), (0, -5)]

def cache_477_H_part1 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)]

def cache_477_H_part2 : List Cell := [(2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3)]

def cache_477_H_part3 : List Cell := [(5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -2), (6, -1), (7, -4), (7, -3), (7, -2), (7, -1)]

def cache_477_H : List Cell := ((cache_477_H_part0 ++ cache_477_H_part1) ++ (cache_477_H_part2 ++ cache_477_H_part3))

def cache_477 : ListRow := ⟨cache_477_A, cache_477_H, 16⟩

def cache_478_A_part0 : List Cell := [(1, -2), (1, -1), (1, 0), (2, 0)]

def cache_478_A : List Cell := cache_478_A_part0

def cache_478_H_part0 : List Cell := [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0)]

def cache_478_H_part1 : List Cell := [(5, 1)]

def cache_478_H : List Cell := (cache_478_H_part0 ++ cache_478_H_part1)

def cache_478 : ListRow := ⟨cache_478_A, cache_478_H, 8⟩

def cache_479_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_479_A : List Cell := cache_479_A_part0

def cache_479_H_part0 : List Cell := [(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6)]

def cache_479_H_part1 : List Cell := [(-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0)]

def cache_479_H_part2 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_479_H_part3 : List Cell := [(1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)]

def cache_479_H : List Cell := ((cache_479_H_part0 ++ cache_479_H_part1) ++ (cache_479_H_part2 ++ cache_479_H_part3))

def cache_479 : ListRow := ⟨cache_479_A, cache_479_H, 21⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_480_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (0, -1), (1, 1)]

def cache_480_A : List Cell := cache_480_A_part0

def cache_480_H_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_480_H : List Cell := cache_480_H_part0

def cache_480 : ListRow := ⟨cache_480_A, cache_480_H, 7⟩

def cache_481_A_part0 : List Cell := [(-3, -2), (-2, 0), (-2, 1), (-1, 0)]

def cache_481_A : List Cell := cache_481_A_part0

def cache_481_H_part0 : List Cell := [(-5, 0), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_481_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)]

def cache_481_H : List Cell := (cache_481_H_part0 ++ cache_481_H_part1)

def cache_481 : ListRow := ⟨cache_481_A, cache_481_H, 11⟩

def cache_482_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -3)]

def cache_482_A : List Cell := cache_482_A_part0

def cache_482_H_part0 : List Cell := [(-3, -1), (-2, -2), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1)]

def cache_482_H : List Cell := cache_482_H_part0

def cache_482 : ListRow := ⟨cache_482_A, cache_482_H, 7⟩

def cache_483_A_part0 : List Cell := [(-2, -3), (-2, -2), (-2, -1), (0, -2), (0, -1)]

def cache_483_A : List Cell := cache_483_A_part0

def cache_483_H_part0 : List Cell := [(-7, -1), (-6, -2), (-6, -1), (-5, -2), (-5, -1), (-4, -2), (-4, -1), (-3, -2), (-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4)]

def cache_483_H_part1 : List Cell := [(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0)]

def cache_483_H_part2 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_483_H_part3 : List Cell := [(4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2)]

def cache_483_H_part4 : List Cell := [(8, -1), (9, -3), (9, -1)]

def cache_483_H : List Cell := ((cache_483_H_part0 ++ cache_483_H_part1) ++ (cache_483_H_part2 ++ (cache_483_H_part3 ++ cache_483_H_part4)))

def cache_483 : ListRow := ⟨cache_483_A, cache_483_H, 22⟩

def cache_484_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0)]

def cache_484_A : List Cell := cache_484_A_part0

def cache_484_H_part0 : List Cell := [(-5, 1), (-4, -1), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_484_H_part1 : List Cell := [(0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_484_H : List Cell := (cache_484_H_part0 ++ cache_484_H_part1)

def cache_484 : ListRow := ⟨cache_484_A, cache_484_H, 12⟩

def cache_485_A_part0 : List Cell := [(-1, 0), (-1, 1), (0, -3), (0, -2)]

def cache_485_A : List Cell := cache_485_A_part0

def cache_485_H_part0 : List Cell := [(-4, 1), (-3, -1), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1)]

def cache_485_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_485_H : List Cell := (cache_485_H_part0 ++ cache_485_H_part1)

def cache_485 : ListRow := ⟨cache_485_A, cache_485_H, 13⟩

def cache_486_A_part0 : List Cell := [(0, -3), (0, -1), (1, -4), (1, -3)]

def cache_486_A : List Cell := cache_486_A_part0

def cache_486_H_part0 : List Cell := [(-3, 0), (-2, -2), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2)]

def cache_486_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)]

def cache_486_H : List Cell := (cache_486_H_part0 ++ cache_486_H_part1)

def cache_486 : ListRow := ⟨cache_486_A, cache_486_H, 14⟩

def cache_487_A_part0 : List Cell := [(-2, -2), (-1, 0), (-1, 1), (0, -3), (0, -2)]

def cache_487_A : List Cell := cache_487_A_part0

def cache_487_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2)]

def cache_487_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)]

def cache_487_H : List Cell := (cache_487_H_part0 ++ cache_487_H_part1)

def cache_487 : ListRow := ⟨cache_487_A, cache_487_H, 12⟩

def cache_488_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)]

def cache_488_A : List Cell := cache_488_A_part0

def cache_488_H_part0 : List Cell := [(-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (2, 1)]

def cache_488_H : List Cell := cache_488_H_part0

def cache_488 : ListRow := ⟨cache_488_A, cache_488_H, 9⟩

def cache_489_A_part0 : List Cell := [(-2, -2), (-2, 0), (-1, -2), (-1, 0)]

def cache_489_A : List Cell := cache_489_A_part0

def cache_489_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1)]

def cache_489_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)]

def cache_489_H : List Cell := (cache_489_H_part0 ++ cache_489_H_part1)

def cache_489 : ListRow := ⟨cache_489_A, cache_489_H, 9⟩

def cache_490_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_490_A : List Cell := cache_490_A_part0

def cache_490_H_part0 : List Cell := [(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3)]

def cache_490_H_part1 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_490_H_part2 : List Cell := [(3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2)]

def cache_490_H_part3 : List Cell := [(5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3)]

def cache_490_H_part4 : List Cell := [(7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)]

def cache_490_H : List Cell := ((cache_490_H_part0 ++ cache_490_H_part1) ++ (cache_490_H_part2 ++ (cache_490_H_part3 ++ cache_490_H_part4)))

def cache_490 : ListRow := ⟨cache_490_A, cache_490_H, 22⟩

def cache_491_A_part0 : List Cell := [(-1, 0), (0, -3), (0, -2), (0, -1)]

def cache_491_A : List Cell := cache_491_A_part0

def cache_491_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_491_H : List Cell := cache_491_H_part0

def cache_491 : ListRow := ⟨cache_491_A, cache_491_H, 9⟩

def cache_492_A_part0 : List Cell := [(1, 0), (1, 2), (1, 3), (2, -1), (2, 0)]

def cache_492_A : List Cell := cache_492_A_part0

def cache_492_H_part0 : List Cell := [(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_492_H_part1 : List Cell := [(2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 3), (6, 4)]

def cache_492_H_part2 : List Cell := [(7, 4)]

def cache_492_H : List Cell := (cache_492_H_part0 ++ (cache_492_H_part1 ++ cache_492_H_part2))

def cache_492 : ListRow := ⟨cache_492_A, cache_492_H, 13⟩

def cache_493_A_part0 : List Cell := [(-2, -2), (-2, -1), (-2, 0), (-1, 0)]

def cache_493_A : List Cell := cache_493_A_part0

def cache_493_H_part0 : List Cell := [(-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_493_H_part1 : List Cell := [(1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)]

def cache_493_H : List Cell := (cache_493_H_part0 ++ cache_493_H_part1)

def cache_493 : ListRow := ⟨cache_493_A, cache_493_H, 8⟩

def cache_494_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1)]

def cache_494_A : List Cell := cache_494_A_part0

def cache_494_H_part0 : List Cell := [(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1)]

def cache_494_H_part1 : List Cell := [(0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)]

def cache_494_H : List Cell := (cache_494_H_part0 ++ cache_494_H_part1)

def cache_494 : ListRow := ⟨cache_494_A, cache_494_H, 11⟩

def cache_495_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -1), (-1, 0)]

def cache_495_A : List Cell := cache_495_A_part0

def cache_495_H_part0 : List Cell := [(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_495_H_part1 : List Cell := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1)]

def cache_495_H : List Cell := (cache_495_H_part0 ++ cache_495_H_part1)

def cache_495 : ListRow := ⟨cache_495_A, cache_495_H, 13⟩

def cache_496_A_part0 : List Cell := [(1, 0), (2, 0), (2, 1)]

def cache_496_A : List Cell := cache_496_A_part0

def cache_496_H_part0 : List Cell := [(-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2)]

def cache_496_H_part1 : List Cell := [(1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)]

def cache_496_H : List Cell := (cache_496_H_part0 ++ cache_496_H_part1)

def cache_496 : ListRow := ⟨cache_496_A, cache_496_H, 12⟩

def cache_497_A_part0 : List Cell := [(1, -1), (1, 0), (2, -1), (2, 0)]

def cache_497_A : List Cell := cache_497_A_part0

def cache_497_H_part0 : List Cell := [(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_497_H_part1 : List Cell := [(1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2)]

def cache_497_H_part2 : List Cell := [(6, 3), (7, 1)]

def cache_497_H : List Cell := (cache_497_H_part0 ++ (cache_497_H_part1 ++ cache_497_H_part2))

def cache_497 : ListRow := ⟨cache_497_A, cache_497_H, 15⟩

def cache_498_A_part0 : List Cell := [(-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, 1)]

def cache_498_A : List Cell := cache_498_A_part0

def cache_498_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)]

def cache_498_H_part1 : List Cell := [(3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)]

def cache_498_H : List Cell := (cache_498_H_part0 ++ cache_498_H_part1)

def cache_498 : ListRow := ⟨cache_498_A, cache_498_H, 9⟩

def cache_499_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0)]

def cache_499_A : List Cell := cache_499_A_part0

def cache_499_H_part0 : List Cell := [(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_499_H_part1 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)]

def cache_499_H : List Cell := (cache_499_H_part0 ++ cache_499_H_part1)

def cache_499 : ListRow := ⟨cache_499_A, cache_499_H, 9⟩

def cache_500_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -1)]

def cache_500_A : List Cell := cache_500_A_part0

def cache_500_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0)]

def cache_500_H_part1 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_500_H : List Cell := (cache_500_H_part0 ++ cache_500_H_part1)

def cache_500 : ListRow := ⟨cache_500_A, cache_500_H, 12⟩

def cache_501_A_part0 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)]

def cache_501_A : List Cell := cache_501_A_part0

def cache_501_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_501_H_part1 : List Cell := [(1, 1), (1, 3), (1, 4), (1, 5)]

def cache_501_H : List Cell := (cache_501_H_part0 ++ cache_501_H_part1)

def cache_501 : ListRow := ⟨cache_501_A, cache_501_H, 10⟩

def cache_502_A_part0 : List Cell := [(-2, -2), (-2, 0), (-1, -2), (-1, 0), (0, -2)]

def cache_502_A : List Cell := cache_502_A_part0

def cache_502_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -5), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2)]

def cache_502_H_part1 : List Cell := [(-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_502_H : List Cell := (cache_502_H_part0 ++ cache_502_H_part1)

def cache_502 : ListRow := ⟨cache_502_A, cache_502_H, 8⟩

def cache_503_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2)]

def cache_503_A : List Cell := cache_503_A_part0

def cache_503_H_part0 : List Cell := [(-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)]

def cache_503_H_part1 : List Cell := [(2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1)]

def cache_503_H_part2 : List Cell := [(5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)]

def cache_503_H : List Cell := (cache_503_H_part0 ++ (cache_503_H_part1 ++ cache_503_H_part2))

def cache_503 : ListRow := ⟨cache_503_A, cache_503_H, 14⟩

def cache_504_A_part0 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1)]

def cache_504_A : List Cell := cache_504_A_part0

def cache_504_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1)]

def cache_504_H_part1 : List Cell := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_504_H_part2 : List Cell := [(5, 0), (5, 1), (6, 1)]

def cache_504_H : List Cell := (cache_504_H_part0 ++ (cache_504_H_part1 ++ cache_504_H_part2))

def cache_504 : ListRow := ⟨cache_504_A, cache_504_H, 13⟩

def cache_505_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_505_A : List Cell := cache_505_A_part0

def cache_505_H_part0 : List Cell := [(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_505_H_part1 : List Cell := [(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0)]

def cache_505_H_part2 : List Cell := [(6, 1), (7, 1)]

def cache_505_H : List Cell := (cache_505_H_part0 ++ (cache_505_H_part1 ++ cache_505_H_part2))

def cache_505 : ListRow := ⟨cache_505_A, cache_505_H, 11⟩

def cache_506_A_part0 : List Cell := [(-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0)]

def cache_506_A : List Cell := cache_506_A_part0

def cache_506_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3)]

def cache_506_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)]

def cache_506_H : List Cell := (cache_506_H_part0 ++ cache_506_H_part1)

def cache_506 : ListRow := ⟨cache_506_A, cache_506_H, 11⟩

def cache_507_A_part0 : List Cell := [(-2, -3), (-2, -2), (-1, 0), (-1, 1), (0, -2)]

def cache_507_A : List Cell := cache_507_A_part0

def cache_507_H_part0 : List Cell := [(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_507_H_part1 : List Cell := [(1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)]

def cache_507_H : List Cell := (cache_507_H_part0 ++ cache_507_H_part1)

def cache_507 : ListRow := ⟨cache_507_A, cache_507_H, 12⟩

def cache_508_A_part0 : List Cell := [(-3, -1), (-3, 0), (-2, -1), (-1, -2), (-1, -1), (0, -1)]

def cache_508_A : List Cell := cache_508_A_part0

def cache_508_H_part0 : List Cell := [(-5, 2), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)]

def cache_508_H_part1 : List Cell := [(-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)]

def cache_508_H : List Cell := (cache_508_H_part0 ++ cache_508_H_part1)

def cache_508 : ListRow := ⟨cache_508_A, cache_508_H, 13⟩

def cache_509_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (1, 0)]

def cache_509_A : List Cell := cache_509_A_part0

def cache_509_H_part0 : List Cell := [(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1)]

def cache_509_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_509_H : List Cell := (cache_509_H_part0 ++ cache_509_H_part1)

def cache_509 : ListRow := ⟨cache_509_A, cache_509_H, 8⟩

def cache_510_A_part0 : List Cell := [(0, -1), (1, -1), (2, -2), (2, -1), (3, -1)]

def cache_510_A : List Cell := cache_510_A_part0

def cache_510_H_part0 : List Cell := [(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_510_H_part1 : List Cell := [(2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)]

def cache_510_H : List Cell := (cache_510_H_part0 ++ cache_510_H_part1)

def cache_510 : ListRow := ⟨cache_510_A, cache_510_H, 14⟩

def cache_511_A_part0 : List Cell := [(-3, -2), (-2, -2), (-1, -2), (-1, -1), (-1, 0), (0, 2)]

def cache_511_A : List Cell := cache_511_A_part0

def cache_511_H_part0 : List Cell := [(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0)]

def cache_511_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_511_H : List Cell := (cache_511_H_part0 ++ cache_511_H_part1)

def cache_511 : ListRow := ⟨cache_511_A, cache_511_H, 10⟩

def cache_512_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, 0), (-1, 2), (-1, 3)]

def cache_512_A : List Cell := cache_512_A_part0

def cache_512_H_part0 : List Cell := [(-4, 2), (-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1)]

def cache_512_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 3), (4, 4), (5, 4)]

def cache_512_H : List Cell := (cache_512_H_part0 ++ cache_512_H_part1)

def cache_512 : ListRow := ⟨cache_512_A, cache_512_H, 13⟩

def cache_513_A_part0 : List Cell := [(0, -1), (1, -1), (2, -1), (3, -1)]

def cache_513_A : List Cell := cache_513_A_part0

def cache_513_H_part0 : List Cell := [(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_513_H_part1 : List Cell := [(2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)]

def cache_513_H : List Cell := (cache_513_H_part0 ++ cache_513_H_part1)

def cache_513 : ListRow := ⟨cache_513_A, cache_513_H, 14⟩

def cache_514_A_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)]

def cache_514_A : List Cell := cache_514_A_part0

def cache_514_H_part0 : List Cell := [(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_514_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_514_H_part2 : List Cell := [(-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_514_H_part3 : List Cell := [(2, 3), (3, 1), (3, 2), (3, 3)]

def cache_514_H : List Cell := ((cache_514_H_part0 ++ cache_514_H_part1) ++ (cache_514_H_part2 ++ cache_514_H_part3))

def cache_514 : ListRow := ⟨cache_514_A, cache_514_H, 21⟩

def cache_515_A_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-1, 0)]

def cache_515_A : List Cell := cache_515_A_part0

def cache_515_H_part0 : List Cell := [(-4, -2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1)]

def cache_515_H_part1 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3)]

def cache_515_H_part2 : List Cell := [(3, 4)]

def cache_515_H : List Cell := (cache_515_H_part0 ++ (cache_515_H_part1 ++ cache_515_H_part2))

def cache_515 : ListRow := ⟨cache_515_A, cache_515_H, 14⟩

def cache_516_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)]

def cache_516_A : List Cell := cache_516_A_part0

def cache_516_H_part0 : List Cell := [(-6, -2), (-5, -2), (-5, -1), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2)]

def cache_516_H_part1 : List Cell := [(-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_516_H : List Cell := (cache_516_H_part0 ++ cache_516_H_part1)

def cache_516 : ListRow := ⟨cache_516_A, cache_516_H, 12⟩

def cache_517_A_part0 : List Cell := [(-1, -3), (-1, -1), (0, -3), (0, -1)]

def cache_517_A : List Cell := cache_517_A_part0

def cache_517_H_part0 : List Cell := [(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1)]

def cache_517_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0)]

def cache_517_H_part2 : List Cell := [(4, -2), (4, -1), (4, 0), (5, 0)]

def cache_517_H : List Cell := (cache_517_H_part0 ++ (cache_517_H_part1 ++ cache_517_H_part2))

def cache_517 : ListRow := ⟨cache_517_A, cache_517_H, 13⟩

def cache_518_A_part0 : List Cell := [(1, -1), (1, 0), (2, -1), (2, 0)]

def cache_518_A : List Cell := cache_518_A_part0

def cache_518_H_part0 : List Cell := [(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)]

def cache_518_H_part1 : List Cell := [(-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1)]

def cache_518_H_part2 : List Cell := [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1)]

def cache_518_H_part3 : List Cell := [(5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3)]

def cache_518_H : List Cell := ((cache_518_H_part0 ++ cache_518_H_part1) ++ (cache_518_H_part2 ++ cache_518_H_part3))

def cache_518 : ListRow := ⟨cache_518_A, cache_518_H, 22⟩

def cache_519_A_part0 : List Cell := [(-2, 0), (-1, -3), (-1, -2), (-1, -1)]

def cache_519_A : List Cell := cache_519_A_part0

def cache_519_H_part0 : List Cell := [(-6, -1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2)]

def cache_519_H_part1 : List Cell := [(-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1)]

def cache_519_H_part2 : List Cell := [(3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (5, 0)]

def cache_519_H : List Cell := (cache_519_H_part0 ++ (cache_519_H_part1 ++ cache_519_H_part2))

def cache_519 : ListRow := ⟨cache_519_A, cache_519_H, 12⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_520_A_part0 : List Cell := [(-2, -3), (-1, 0), (1, -2), (1, 0)]

def cache_520_A : List Cell := cache_520_A_part0

def cache_520_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4)]

def cache_520_H_part1 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_520_H : List Cell := (cache_520_H_part0 ++ cache_520_H_part1)

def cache_520 : ListRow := ⟨cache_520_A, cache_520_H, 8⟩

def cache_521_A_part0 : List Cell := [(-1, -4), (-1, -3), (0, -3), (0, -1)]

def cache_521_A : List Cell := cache_521_A_part0

def cache_521_H_part0 : List Cell := [(-6, 1), (-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3)]

def cache_521_H_part1 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (3, -1)]

def cache_521_H_part2 : List Cell := [(4, -4), (4, -2)]

def cache_521_H : List Cell := (cache_521_H_part0 ++ (cache_521_H_part1 ++ cache_521_H_part2))

def cache_521 : ListRow := ⟨cache_521_A, cache_521_H, 14⟩

def cache_522_A_part0 : List Cell := [(-2, -1), (0, -1), (0, 1)]

def cache_522_A : List Cell := cache_522_A_part0

def cache_522_H_part0 : List Cell := [(-5, -2), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)]

def cache_522_H_part1 : List Cell := [(0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 2), (3, -2), (3, -1), (3, 0), (3, 2), (4, -2), (4, -1), (4, 0), (5, -2)]

def cache_522_H : List Cell := (cache_522_H_part0 ++ cache_522_H_part1)

def cache_522 : ListRow := ⟨cache_522_A, cache_522_H, 9⟩

def cache_523_A_part0 : List Cell := [(-3, 4), (-2, 0), (-2, 1), (-2, 2), (-1, 0)]

def cache_523_A : List Cell := cache_523_A_part0

def cache_523_H_part0 : List Cell := [(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2)]

def cache_523_H_part1 : List Cell := [(-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_523_H_part2 : List Cell := [(2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)]

def cache_523_H : List Cell := (cache_523_H_part0 ++ (cache_523_H_part1 ++ cache_523_H_part2))

def cache_523 : ListRow := ⟨cache_523_A, cache_523_H, 11⟩

def cache_524_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_524_A : List Cell := cache_524_A_part0

def cache_524_H_part0 : List Cell := [(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0)]

def cache_524_H_part1 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1)]

def cache_524_H_part2 : List Cell := [(2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)]

def cache_524_H : List Cell := (cache_524_H_part0 ++ (cache_524_H_part1 ++ cache_524_H_part2))

def cache_524 : ListRow := ⟨cache_524_A, cache_524_H, 14⟩

def cache_525_A_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-1, 0)]

def cache_525_A : List Cell := cache_525_A_part0

def cache_525_H_part0 : List Cell := [(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_525_H_part1 : List Cell := [(-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_525_H_part2 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (5, 1)]

def cache_525_H : List Cell := (cache_525_H_part0 ++ (cache_525_H_part1 ++ cache_525_H_part2))

def cache_525 : ListRow := ⟨cache_525_A, cache_525_H, 11⟩

def cache_526_A_part0 : List Cell := [(-1, -2), (-1, 0), (0, -2)]

def cache_526_A : List Cell := cache_526_A_part0

def cache_526_H_part0 : List Cell := [(-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3)]

def cache_526_H_part1 : List Cell := [(-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_526_H_part2 : List Cell := [(0, 5), (0, 6), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1)]

def cache_526_H_part3 : List Cell := [(4, -1), (4, 0), (4, 1), (5, -1)]

def cache_526_H : List Cell := ((cache_526_H_part0 ++ cache_526_H_part1) ++ (cache_526_H_part2 ++ cache_526_H_part3))

def cache_526 : ListRow := ⟨cache_526_A, cache_526_H, 17⟩

def cache_527_A_part0 : List Cell := [(1, -3), (1, -2), (1, -1)]

def cache_527_A : List Cell := cache_527_A_part0

def cache_527_H_part0 : List Cell := [(-5, 1), (-4, -2), (-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)]

def cache_527_H_part1 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)]

def cache_527_H_part2 : List Cell := [(4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (7, 0)]

def cache_527_H : List Cell := (cache_527_H_part0 ++ (cache_527_H_part1 ++ cache_527_H_part2))

def cache_527 : ListRow := ⟨cache_527_A, cache_527_H, 13⟩

def cache_528_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (0, 1)]

def cache_528_A : List Cell := cache_528_A_part0

def cache_528_H_part0 : List Cell := [(-7, 0), (-7, 2), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1)]

def cache_528_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3)]

def cache_528_H_part2 : List Cell := [(1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 3)]

def cache_528_H : List Cell := (cache_528_H_part0 ++ (cache_528_H_part1 ++ cache_528_H_part2))

def cache_528 : ListRow := ⟨cache_528_A, cache_528_H, 12⟩

def cache_529_A_part0 : List Cell := [(1, 0), (2, 0), (3, 0)]

def cache_529_A : List Cell := cache_529_A_part0

def cache_529_H_part0 : List Cell := [(-2, -1), (-2, 1), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1)]

def cache_529_H_part1 : List Cell := [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1)]

def cache_529_H_part2 : List Cell := [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_529_H : List Cell := (cache_529_H_part0 ++ (cache_529_H_part1 ++ cache_529_H_part2))

def cache_529 : ListRow := ⟨cache_529_A, cache_529_H, 16⟩

def cache_530_A_part0 : List Cell := [(0, -1), (0, 1), (2, -1), (2, 1)]

def cache_530_A : List Cell := cache_530_A_part0

def cache_530_H_part0 : List Cell := [(-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3)]

def cache_530_H_part1 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0)]

def cache_530_H_part2 : List Cell := [(6, 2)]

def cache_530_H : List Cell := (cache_530_H_part0 ++ (cache_530_H_part1 ++ cache_530_H_part2))

def cache_530 : ListRow := ⟨cache_530_A, cache_530_H, 13⟩

def cache_531_A_part0 : List Cell := [(0, -2), (1, -2)]

def cache_531_A : List Cell := cache_531_A_part0

def cache_531_H_part0 : List Cell := [(-5, -1), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6)]

def cache_531_H_part1 : List Cell := [(-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -7)]

def cache_531_H_part2 : List Cell := [(1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_531_H_part3 : List Cell := [(2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_531_H : List Cell := ((cache_531_H_part0 ++ cache_531_H_part1) ++ (cache_531_H_part2 ++ cache_531_H_part3))

def cache_531 : ListRow := ⟨cache_531_A, cache_531_H, 18⟩

def cache_532_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (0, -1)]

def cache_532_A : List Cell := cache_532_A_part0

def cache_532_H_part0 : List Cell := [(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)]

def cache_532_H_part1 : List Cell := [(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1)]

def cache_532_H_part2 : List Cell := [(4, 0), (4, 1), (5, -2), (5, 0), (5, 1)]

def cache_532_H : List Cell := (cache_532_H_part0 ++ (cache_532_H_part1 ++ cache_532_H_part2))

def cache_532 : ListRow := ⟨cache_532_A, cache_532_H, 14⟩

def cache_533_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_533_A : List Cell := cache_533_A_part0

def cache_533_H_part0 : List Cell := [(-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2)]

def cache_533_H_part1 : List Cell := [(-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_533_H_part2 : List Cell := [(2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, 0), (4, -4), (4, -3), (4, -2), (5, -2)]

def cache_533_H : List Cell := (cache_533_H_part0 ++ (cache_533_H_part1 ++ cache_533_H_part2))

def cache_533 : ListRow := ⟨cache_533_A, cache_533_H, 11⟩

def cache_534_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 2), (-1, -1), (-1, 0), (-1, 2)]

def cache_534_A : List Cell := cache_534_A_part0

def cache_534_H_part0 : List Cell := [(-5, 3), (-5, 5), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1)]

def cache_534_H_part1 : List Cell := [(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_534_H_part2 : List Cell := [(1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)]

def cache_534_H : List Cell := (cache_534_H_part0 ++ (cache_534_H_part1 ++ cache_534_H_part2))

def cache_534 : ListRow := ⟨cache_534_A, cache_534_H, 16⟩

def cache_535_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1)]

def cache_535_A : List Cell := cache_535_A_part0

def cache_535_H_part0 : List Cell := [(-5, -2), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4)]

def cache_535_H_part1 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2)]

def cache_535_H_part2 : List Cell := [(1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)]

def cache_535_H : List Cell := (cache_535_H_part0 ++ (cache_535_H_part1 ++ cache_535_H_part2))

def cache_535 : ListRow := ⟨cache_535_A, cache_535_H, 15⟩

def cache_536_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)]

def cache_536_A : List Cell := cache_536_A_part0

def cache_536_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, -3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3)]

def cache_536_H_part1 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_536_H_part2 : List Cell := [(2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)]

def cache_536_H : List Cell := (cache_536_H_part0 ++ (cache_536_H_part1 ++ cache_536_H_part2))

def cache_536 : ListRow := ⟨cache_536_A, cache_536_H, 17⟩

def cache_537_A_part0 : List Cell := [(-3, 1), (-2, -1), (-2, 1), (0, -1), (0, 1)]

def cache_537_A : List Cell := cache_537_A_part0

def cache_537_H_part0 : List Cell := [(-7, -2), (-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3)]

def cache_537_H_part1 : List Cell := [(-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_537_H_part2 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)]

def cache_537_H : List Cell := (cache_537_H_part0 ++ (cache_537_H_part1 ++ cache_537_H_part2))

def cache_537 : ListRow := ⟨cache_537_A, cache_537_H, 11⟩

def cache_538_A_part0 : List Cell := [(1, 0), (2, 0), (3, 0)]

def cache_538_A : List Cell := cache_538_A_part0

def cache_538_H_part0 : List Cell := [(-2, -1), (-2, 1), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 2)]

def cache_538_H_part1 : List Cell := [(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)]

def cache_538_H_part2 : List Cell := [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)]

def cache_538_H_part3 : List Cell := [(5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7)]

def cache_538_H : List Cell := ((cache_538_H_part0 ++ cache_538_H_part1) ++ (cache_538_H_part2 ++ cache_538_H_part3))

def cache_538 : ListRow := ⟨cache_538_A, cache_538_H, 22⟩

def cache_539_A_part0 : List Cell := [(0, -3), (0, -2), (1, -3), (1, -2)]

def cache_539_A : List Cell := cache_539_A_part0

def cache_539_H_part0 : List Cell := [(-5, -2), (-4, -4), (-4, -2), (-4, -1), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3)]

def cache_539_H_part1 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_539_H_part2 : List Cell := [(1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_539_H_part3 : List Cell := [(6, 1)]

def cache_539_H : List Cell := ((cache_539_H_part0 ++ cache_539_H_part1) ++ (cache_539_H_part2 ++ cache_539_H_part3))

def cache_539 : ListRow := ⟨cache_539_A, cache_539_H, 18⟩

def cache_540_A_part0 : List Cell := [(0, -3), (0, -2), (1, -3), (1, -2)]

def cache_540_A : List Cell := cache_540_A_part0

def cache_540_H_part0 : List Cell := [(-3, -3), (-3, 1), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)]

def cache_540_H_part1 : List Cell := [(0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1)]

def cache_540_H_part2 : List Cell := [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)]

def cache_540_H : List Cell := (cache_540_H_part0 ++ (cache_540_H_part1 ++ cache_540_H_part2))

def cache_540 : ListRow := ⟨cache_540_A, cache_540_H, 18⟩

def cache_541_A_part0 : List Cell := [(-2, -2), (-1, -2), (0, -2), (0, -1)]

def cache_541_A : List Cell := cache_541_A_part0

def cache_541_H_part0 : List Cell := [(-5, 0), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)]

def cache_541_H_part1 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_541_H_part2 : List Cell := [(2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)]

def cache_541_H : List Cell := (cache_541_H_part0 ++ (cache_541_H_part1 ++ cache_541_H_part2))

def cache_541 : ListRow := ⟨cache_541_A, cache_541_H, 14⟩

def cache_542_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3)]

def cache_542_A : List Cell := cache_542_A_part0

def cache_542_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_542_H_part1 : List Cell := [(1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)]

def cache_542_H_part2 : List Cell := [(4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_542_H : List Cell := (cache_542_H_part0 ++ (cache_542_H_part1 ++ cache_542_H_part2))

def cache_542 : ListRow := ⟨cache_542_A, cache_542_H, 17⟩

def cache_543_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0)]

def cache_543_A : List Cell := cache_543_A_part0

def cache_543_H_part0 : List Cell := [(-6, 3), (-5, -1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)]

def cache_543_H_part1 : List Cell := [(-2, 6), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2)]

def cache_543_H_part2 : List Cell := [(2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)]

def cache_543_H : List Cell := (cache_543_H_part0 ++ (cache_543_H_part1 ++ cache_543_H_part2))

def cache_543 : ListRow := ⟨cache_543_A, cache_543_H, 11⟩

def cache_544_A_part0 : List Cell := [(1, -1), (1, 0), (2, -1), (2, 0)]

def cache_544_A : List Cell := cache_544_A_part0

def cache_544_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0)]

def cache_544_H_part1 : List Cell := [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4)]

def cache_544_H_part2 : List Cell := [(6, 5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -2), (10, 0)]

def cache_544_H_part3 : List Cell := [(10, 2)]

def cache_544_H : List Cell := ((cache_544_H_part0 ++ cache_544_H_part1) ++ (cache_544_H_part2 ++ cache_544_H_part3))

def cache_544 : ListRow := ⟨cache_544_A, cache_544_H, 18⟩

def cache_545_A_part0 : List Cell := [(-1, -1), (0, -2), (0, -1), (1, -2), (1, -1)]

def cache_545_A : List Cell := cache_545_A_part0

def cache_545_H_part0 : List Cell := [(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)]

def cache_545_H_part1 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_545_H_part2 : List Cell := [(2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_545_H_part3 : List Cell := [(6, 1), (6, 3)]

def cache_545_H : List Cell := ((cache_545_H_part0 ++ cache_545_H_part1) ++ (cache_545_H_part2 ++ cache_545_H_part3))

def cache_545 : ListRow := ⟨cache_545_A, cache_545_H, 20⟩

def cache_546_A_part0 : List Cell := [(1, 0), (2, 0), (3, -2), (3, 0)]

def cache_546_A : List Cell := cache_546_A_part0

def cache_546_H_part0 : List Cell := [(-2, -1), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_546_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, 0), (3, 1), (3, 2), (3, 3)]

def cache_546_H_part2 : List Cell := [(3, 4), (3, 5), (3, 6), (3, 7), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5)]

def cache_546_H_part3 : List Cell := [(6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)]

def cache_546_H : List Cell := ((cache_546_H_part0 ++ cache_546_H_part1) ++ (cache_546_H_part2 ++ cache_546_H_part3))

def cache_546 : ListRow := ⟨cache_546_A, cache_546_H, 21⟩

def cache_547_A_part0 : List Cell := [(1, -1), (1, 0), (2, 0), (3, 0)]

def cache_547_A : List Cell := cache_547_A_part0

def cache_547_H_part0 : List Cell := [(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)]

def cache_547_H_part1 : List Cell := [(0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1)]

def cache_547_H_part2 : List Cell := [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)]

def cache_547_H_part3 : List Cell := [(6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)]

def cache_547_H : List Cell := ((cache_547_H_part0 ++ cache_547_H_part1) ++ (cache_547_H_part2 ++ cache_547_H_part3))

def cache_547 : ListRow := ⟨cache_547_A, cache_547_H, 21⟩

def cache_548_A_part0 : List Cell := [(-2, -1), (-1, -1), (0, -1)]

def cache_548_A : List Cell := cache_548_A_part0

def cache_548_H_part0 : List Cell := [(-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1)]

def cache_548_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_548_H_part2 : List Cell := [(1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)]

def cache_548_H : List Cell := (cache_548_H_part0 ++ (cache_548_H_part1 ++ cache_548_H_part2))

def cache_548 : ListRow := ⟨cache_548_A, cache_548_H, 15⟩

def cache_549_A_part0 : List Cell := [(-2, -3), (-1, 0), (1, 0)]

def cache_549_A : List Cell := cache_549_A_part0

def cache_549_H_part0 : List Cell := [(-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1)]

def cache_549_H_part1 : List Cell := [(-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_549_H_part2 : List Cell := [(1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0)]

def cache_549_H_part3 : List Cell := [(4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)]

def cache_549_H : List Cell := ((cache_549_H_part0 ++ cache_549_H_part1) ++ (cache_549_H_part2 ++ cache_549_H_part3))

def cache_549 : ListRow := ⟨cache_549_A, cache_549_H, 17⟩

def cache_550_A_part0 : List Cell := [(0, -1), (0, 1), (2, 1)]

def cache_550_A : List Cell := cache_550_A_part0

def cache_550_H_part0 : List Cell := [(-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3)]

def cache_550_H_part1 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_550_H_part2 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2)]

def cache_550_H_part3 : List Cell := [(7, 3)]

def cache_550_H : List Cell := ((cache_550_H_part0 ++ cache_550_H_part1) ++ (cache_550_H_part2 ++ cache_550_H_part3))

def cache_550 : ListRow := ⟨cache_550_A, cache_550_H, 13⟩

def cache_551_A_part0 : List Cell := [(0, 1), (0, 2)]

def cache_551_A : List Cell := cache_551_A_part0

def cache_551_H_part0 : List Cell := [(-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1)]

def cache_551_H_part1 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1)]

def cache_551_H_part2 : List Cell := [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 4), (6, 4)]

def cache_551_H : List Cell := (cache_551_H_part0 ++ (cache_551_H_part1 ++ cache_551_H_part2))

def cache_551 : ListRow := ⟨cache_551_A, cache_551_H, 14⟩

def cache_552_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_552_A : List Cell := cache_552_A_part0

def cache_552_H_part0 : List Cell := [(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_552_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5)]

def cache_552_H_part2 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]

def cache_552_H_part3 : List Cell := [(0, 6), (0, 7), (0, 8), (0, 9), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -3)]

def cache_552_H_part4 : List Cell := [(4, -2), (4, -1), (4, 1), (5, -1)]

def cache_552_H : List Cell := ((cache_552_H_part0 ++ cache_552_H_part1) ++ (cache_552_H_part2 ++ (cache_552_H_part3 ++ cache_552_H_part4)))

def cache_552 : ListRow := ⟨cache_552_A, cache_552_H, 21⟩

def cache_553_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_553_A : List Cell := cache_553_A_part0

def cache_553_H_part0 : List Cell := [(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1)]

def cache_553_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5)]

def cache_553_H_part2 : List Cell := [(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)]

def cache_553_H_part3 : List Cell := [(4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1)]

def cache_553_H_part4 : List Cell := [(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_553_H : List Cell := ((cache_553_H_part0 ++ cache_553_H_part1) ++ (cache_553_H_part2 ++ (cache_553_H_part3 ++ cache_553_H_part4)))

def cache_553 : ListRow := ⟨cache_553_A, cache_553_H, 17⟩

def cache_554_A_part0 : List Cell := [(0, -2), (0, -1), (1, -1), (1, 1), (2, 1), (3, 1)]

def cache_554_A : List Cell := cache_554_A_part0

def cache_554_H_part0 : List Cell := [(-3, 3), (-3, 5), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]

def cache_554_H_part1 : List Cell := [(0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3)]

def cache_554_H_part2 : List Cell := [(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7)]

def cache_554_H_part3 : List Cell := [(5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 5)]

def cache_554_H : List Cell := ((cache_554_H_part0 ++ cache_554_H_part1) ++ (cache_554_H_part2 ++ cache_554_H_part3))

def cache_554 : ListRow := ⟨cache_554_A, cache_554_H, 22⟩

def cache_555_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_555_A : List Cell := cache_555_A_part0

def cache_555_H_part0 : List Cell := [(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_555_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5)]

def cache_555_H_part2 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]

def cache_555_H_part3 : List Cell := [(0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1)]

def cache_555_H_part4 : List Cell := [(3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (5, 1)]

def cache_555_H : List Cell := ((cache_555_H_part0 ++ cache_555_H_part1) ++ (cache_555_H_part2 ++ (cache_555_H_part3 ++ cache_555_H_part4)))

def cache_555 : ListRow := ⟨cache_555_A, cache_555_H, 21⟩

def cache_556_A_part0 : List Cell := [(-3, -3), (-2, -3), (-2, 0), (-1, -4), (-1, -3), (0, -3)]

def cache_556_A : List Cell := cache_556_A_part0

def cache_556_H_part0 : List Cell := [(-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1)]

def cache_556_H_part1 : List Cell := [(-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3)]

def cache_556_H_part2 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_556_H_part3 : List Cell := [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_556_H : List Cell := ((cache_556_H_part0 ++ cache_556_H_part1) ++ (cache_556_H_part2 ++ cache_556_H_part3))

def cache_556 : ListRow := ⟨cache_556_A, cache_556_H, 18⟩

def cache_557_A_part0 : List Cell := [(-1, 0)]

def cache_557_A : List Cell := cache_557_A_part0

def cache_557_H_part0 : List Cell := [(-6, -1), (-6, 0), (-6, 1), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3)]

def cache_557_H_part1 : List Cell := [(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0)]

def cache_557_H_part2 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -4)]

def cache_557_H_part3 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)]

def cache_557_H_part4 : List Cell := [(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 3), (5, 4)]

def cache_557_H : List Cell := ((cache_557_H_part0 ++ cache_557_H_part1) ++ (cache_557_H_part2 ++ (cache_557_H_part3 ++ cache_557_H_part4)))

def cache_557 : ListRow := ⟨cache_557_A, cache_557_H, 19⟩

def cache_558_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_558_A : List Cell := cache_558_A_part0

def cache_558_H_part0 : List Cell := [(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_558_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1)]

def cache_558_H_part2 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_558_H_part3 : List Cell := [(1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2)]

def cache_558_H_part4 : List Cell := [(4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4)]

def cache_558_H : List Cell := ((cache_558_H_part0 ++ cache_558_H_part1) ++ (cache_558_H_part2 ++ (cache_558_H_part3 ++ cache_558_H_part4)))

def cache_558 : ListRow := ⟨cache_558_A, cache_558_H, 21⟩

def cache_559_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1)]

def cache_559_A : List Cell := cache_559_A_part0

def cache_559_H_part0 : List Cell := [(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -5), (2, -4), (2, -3)]

def cache_559_H_part1 : List Cell := [(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -6), (5, -5)]

def cache_559_H_part2 : List Cell := [(5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1)]

def cache_559_H_part3 : List Cell := [(7, 2), (7, 3), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 2), (9, -4), (9, -3), (9, -2), (9, -1), (10, -4), (10, -3), (10, -2), (10, -1)]

def cache_559_H : List Cell := ((cache_559_H_part0 ++ cache_559_H_part1) ++ (cache_559_H_part2 ++ cache_559_H_part3))

def cache_559 : ListRow := ⟨cache_559_A, cache_559_H, 23⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_560_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (0, 1)]

def cache_560_A : List Cell := cache_560_A_part0

def cache_560_H_part0 : List Cell := [(-7, 1), (-6, 0), (-6, 1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)]

def cache_560_H_part1 : List Cell := [(-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_560_H_part2 : List Cell := [(1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2)]

def cache_560_H_part3 : List Cell := [(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -1)]

def cache_560_H_part4 : List Cell := [(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (9, -1), (9, 1)]

def cache_560_H : List Cell := ((cache_560_H_part0 ++ cache_560_H_part1) ++ (cache_560_H_part2 ++ (cache_560_H_part3 ++ cache_560_H_part4)))

def cache_560 : ListRow := ⟨cache_560_A, cache_560_H, 23⟩

def cache_561_A_part0 : List Cell := [(-2, -2), (-2, 0), (-1, 0)]

def cache_561_A : List Cell := cache_561_A_part0

def cache_561_H_part0 : List Cell := [(-7, 2), (-7, 4), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5)]

def cache_561_H_part1 : List Cell := [(-4, 6), (-4, 7), (-3, -2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, 0), (-1, 1)]

def cache_561_H_part2 : List Cell := [(-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -3), (1, -2), (1, -1)]

def cache_561_H_part3 : List Cell := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]

def cache_561_H_part4 : List Cell := [(3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 4)]

def cache_561_H : List Cell := ((cache_561_H_part0 ++ cache_561_H_part1) ++ (cache_561_H_part2 ++ (cache_561_H_part3 ++ cache_561_H_part4)))

def cache_561 : ListRow := ⟨cache_561_A, cache_561_H, 22⟩

def cache_562_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (0, -1)]

def cache_562_A : List Cell := cache_562_A_part0

def cache_562_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -4)]

def cache_562_H_part1 : List Cell := [(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_562_H_part2 : List Cell := [(5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0)]

def cache_562_H_part3 : List Cell := [(7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)]

def cache_562_H : List Cell := ((cache_562_H_part0 ++ cache_562_H_part1) ++ (cache_562_H_part2 ++ cache_562_H_part3))

def cache_562 : ListRow := ⟨cache_562_A, cache_562_H, 24⟩

def cache_563_A_part0 : List Cell := [(1, -1), (1, 0), (2, -1), (2, 0)]

def cache_563_A : List Cell := cache_563_A_part0

def cache_563_H_part0 : List Cell := [(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)]

def cache_563_H_part1 : List Cell := [(-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1)]

def cache_563_H_part2 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2)]

def cache_563_H_part3 : List Cell := [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_563_H_part4 : List Cell := [(5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)]

def cache_563_H : List Cell := ((cache_563_H_part0 ++ cache_563_H_part1) ++ (cache_563_H_part2 ++ (cache_563_H_part3 ++ cache_563_H_part4)))

def cache_563 : ListRow := ⟨cache_563_A, cache_563_H, 23⟩

def cache_564_A_part0 : List Cell := [(-2, -2), (-2, -1), (-2, 0)]

def cache_564_A : List Cell := cache_564_A_part0

def cache_564_H_part0 : List Cell := [(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-1, -6), (-1, -5), (-1, -4)]

def cache_564_H_part1 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -6), (1, -5), (1, -4)]

def cache_564_H_part2 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -4), (3, -3), (3, -2)]

def cache_564_H_part3 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_564_H_part4 : List Cell := [(5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)]

def cache_564_H : List Cell := ((cache_564_H_part0 ++ cache_564_H_part1) ++ (cache_564_H_part2 ++ (cache_564_H_part3 ++ cache_564_H_part4)))

def cache_564 : ListRow := ⟨cache_564_A, cache_564_H, 24⟩

def cache_565_A_part0 : List Cell := [(1, -1), (1, 0), (2, 0), (3, 0)]

def cache_565_A : List Cell := cache_565_A_part0

def cache_565_H_part0 : List Cell := [(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1)]

def cache_565_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_565_H_part2 : List Cell := [(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)]

def cache_565_H_part3 : List Cell := [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)]

def cache_565_H_part4 : List Cell := [(5, 7), (6, -1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)]

def cache_565_H : List Cell := ((cache_565_H_part0 ++ cache_565_H_part1) ++ (cache_565_H_part2 ++ (cache_565_H_part3 ++ cache_565_H_part4)))

def cache_565 : ListRow := ⟨cache_565_A, cache_565_H, 23⟩

def cache_566_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3)]

def cache_566_A : List Cell := cache_566_A_part0

def cache_566_H_part0 : List Cell := [(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1)]

def cache_566_H_part1 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4)]

def cache_566_H_part2 : List Cell := [(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6)]

def cache_566_H_part3 : List Cell := [(4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0)]

def cache_566_H_part4 : List Cell := [(6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_566_H : List Cell := ((cache_566_H_part0 ++ cache_566_H_part1) ++ (cache_566_H_part2 ++ (cache_566_H_part3 ++ cache_566_H_part4)))

def cache_566 : ListRow := ⟨cache_566_A, cache_566_H, 17⟩

def cache_567_A_part0 : List Cell := [(-1, -4), (0, -4), (0, -3), (0, -2), (1, 0)]

def cache_567_A : List Cell := cache_567_A_part0

def cache_567_H_part0 : List Cell := [(-5, -4), (-5, -2), (-5, 2), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6)]

def cache_567_H_part1 : List Cell := [(-3, 7), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)]

def cache_567_H_part2 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)]

def cache_567_H_part3 : List Cell := [(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7)]

def cache_567_H_part4 : List Cell := [(3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -1), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2)]

def cache_567_H_part5 : List Cell := [(7, 4)]

def cache_567_H : List Cell := ((cache_567_H_part0 ++ (cache_567_H_part1 ++ cache_567_H_part2)) ++ (cache_567_H_part3 ++ (cache_567_H_part4 ++ cache_567_H_part5)))

def cache_567 : ListRow := ⟨cache_567_A, cache_567_H, 23⟩

def cache_568_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, 0)]

def cache_568_A : List Cell := cache_568_A_part0

def cache_568_H_part0 : List Cell := [(-7, 2), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1)]

def cache_568_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0)]

def cache_568_H_part2 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0), (1, 1)]

def cache_568_H_part3 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1)]

def cache_568_H_part4 : List Cell := [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)]

def cache_568_H : List Cell := ((cache_568_H_part0 ++ cache_568_H_part1) ++ (cache_568_H_part2 ++ (cache_568_H_part3 ++ cache_568_H_part4)))

def cache_568 : ListRow := ⟨cache_568_A, cache_568_H, 24⟩

def cache_569_A_part0 : List Cell := [(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3)]

def cache_569_A : List Cell := cache_569_A_part0

def cache_569_H_part0 : List Cell := [(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)]

def cache_569_H_part1 : List Cell := [(-2, 8), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]

def cache_569_H_part2 : List Cell := [(0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_569_H_part3 : List Cell := [(2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_569_H_part4 : List Cell := [(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -1), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)]

def cache_569_H_part5 : List Cell := [(6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)]

def cache_569_H : List Cell := ((cache_569_H_part0 ++ (cache_569_H_part1 ++ cache_569_H_part2)) ++ (cache_569_H_part3 ++ (cache_569_H_part4 ++ cache_569_H_part5)))

def cache_569 : ListRow := ⟨cache_569_A, cache_569_H, 25⟩

def cache_570_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)]

def cache_570_A : List Cell := cache_570_A_part0

def cache_570_H_part0 : List Cell := [(-7, 3), (-7, 5), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8)]

def cache_570_H_part1 : List Cell := [(-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)]

def cache_570_H_part2 : List Cell := [(-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)]

def cache_570_H_part3 : List Cell := [(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_570_H_part4 : List Cell := [(2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)]

def cache_570_H_part5 : List Cell := [(4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (6, 3), (6, 5)]

def cache_570_H : List Cell := ((cache_570_H_part0 ++ (cache_570_H_part1 ++ cache_570_H_part2)) ++ (cache_570_H_part3 ++ (cache_570_H_part4 ++ cache_570_H_part5)))

def cache_570 : ListRow := ⟨cache_570_A, cache_570_H, 26⟩

def cache_571_A_part0 : List Cell := [(-2, -3), (-1, -4), (-1, -3), (0, -3), (1, -3)]

def cache_571_A : List Cell := cache_571_A_part0

def cache_571_H_part0 : List Cell := [(-7, 2), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_571_H_part1 : List Cell := [(-4, 8), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6)]

def cache_571_H_part2 : List Cell := [(-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)]

def cache_571_H_part3 : List Cell := [(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -3)]

def cache_571_H_part4 : List Cell := [(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)]

def cache_571_H_part5 : List Cell := [(3, 7), (3, 8), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)]

def cache_571_H : List Cell := ((cache_571_H_part0 ++ (cache_571_H_part1 ++ cache_571_H_part2)) ++ (cache_571_H_part3 ++ (cache_571_H_part4 ++ cache_571_H_part5)))

def cache_571 : ListRow := ⟨cache_571_A, cache_571_H, 27⟩

def cache_572_A_part0 : List Cell := [(1, 0), (2, 0)]

def cache_572_A : List Cell := cache_572_A_part0

def cache_572_H_part0 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)]

def cache_572_H_part1 : List Cell := [(-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_572_H_part2 : List Cell := [(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -5), (3, -4)]

def cache_572_H_part3 : List Cell := [(3, -3), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -1)]

def cache_572_H_part4 : List Cell := [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)]

def cache_572_H_part5 : List Cell := [(8, 1), (8, 3), (8, 4), (8, 6)]

def cache_572_H : List Cell := ((cache_572_H_part0 ++ (cache_572_H_part1 ++ cache_572_H_part2)) ++ (cache_572_H_part3 ++ (cache_572_H_part4 ++ cache_572_H_part5)))

def cache_572 : ListRow := ⟨cache_572_A, cache_572_H, 25⟩

def cache_573_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_573_A : List Cell := cache_573_A_part0

def cache_573_H_part0 : List Cell := [(-8, -3), (-8, -1), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -6)]

def cache_573_H_part1 : List Cell := [(-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5)]

def cache_573_H_part2 : List Cell := [(-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)]

def cache_573_H_part3 : List Cell := [(0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)]

def cache_573_H_part4 : List Cell := [(2, 2), (2, 3), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (5, -4), (5, -3)]

def cache_573_H_part5 : List Cell := [(5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -1), (6, 0), (6, 1), (7, 1)]

def cache_573_H : List Cell := ((cache_573_H_part0 ++ (cache_573_H_part1 ++ cache_573_H_part2)) ++ (cache_573_H_part3 ++ (cache_573_H_part4 ++ cache_573_H_part5)))

def cache_573 : ListRow := ⟨cache_573_A, cache_573_H, 19⟩

def cache_574_A_part0 : List Cell := [(-1, -1), (-1, 0), (0, -1)]

def cache_574_A : List Cell := cache_574_A_part0

def cache_574_H_part0 : List Cell := [(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_574_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0)]

def cache_574_H_part2 : List Cell := [(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -2), (1, -1)]

def cache_574_H_part3 : List Cell := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -4)]

def cache_574_H_part4 : List Cell := [(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -4)]

def cache_574_H_part5 : List Cell := [(5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (8, -2), (8, 0), (8, 2)]

def cache_574_H : List Cell := ((cache_574_H_part0 ++ (cache_574_H_part1 ++ cache_574_H_part2)) ++ (cache_574_H_part3 ++ (cache_574_H_part4 ++ cache_574_H_part5)))

def cache_574 : ListRow := ⟨cache_574_A, cache_574_H, 24⟩

def cache_575_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_575_A : List Cell := cache_575_A_part0

def cache_575_H_part0 : List Cell := [(-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6)]

def cache_575_H_part1 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)]

def cache_575_H_part2 : List Cell := [(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)]

def cache_575_H_part3 : List Cell := [(2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1)]

def cache_575_H_part4 : List Cell := [(5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3)]

def cache_575_H_part5 : List Cell := [(8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)]

def cache_575_H : List Cell := ((cache_575_H_part0 ++ (cache_575_H_part1 ++ cache_575_H_part2)) ++ (cache_575_H_part3 ++ (cache_575_H_part4 ++ cache_575_H_part5)))

def cache_575 : ListRow := ⟨cache_575_A, cache_575_H, 24⟩

def cache_576_A_part0 : List Cell := [(-1, -1), (-1, 0), (0, -1)]

def cache_576_A : List Cell := cache_576_A_part0

def cache_576_H_part0 : List Cell := [(-9, -2), (-9, 0), (-9, 2), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4)]

def cache_576_H_part1 : List Cell := [(-6, 5), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_576_H_part2 : List Cell := [(-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)]

def cache_576_H_part3 : List Cell := [(-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)]

def cache_576_H_part4 : List Cell := [(0, 9), (0, 10), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10)]

def cache_576_H_part5 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4)]

def cache_576_H : List Cell := ((cache_576_H_part0 ++ (cache_576_H_part1 ++ cache_576_H_part2)) ++ (cache_576_H_part3 ++ (cache_576_H_part4 ++ cache_576_H_part5)))

def cache_576 : ListRow := ⟨cache_576_A, cache_576_H, 24⟩

def cache_577_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1)]

def cache_577_A : List Cell := cache_577_A_part0

def cache_577_H_part0 : List Cell := [(-9, -2), (-9, 0), (-8, -2), (-8, -1), (-8, 0), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2)]

def cache_577_H_part1 : List Cell := [(-5, -1), (-5, 0), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -8), (-2, -7), (-2, -6)]

def cache_577_H_part2 : List Cell := [(-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2)]

def cache_577_H_part3 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_577_H_part4 : List Cell := [(4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3)]

def cache_577_H_part5 : List Cell := [(8, -2), (8, -1), (9, -3), (9, -1)]

def cache_577_H : List Cell := ((cache_577_H_part0 ++ (cache_577_H_part1 ++ cache_577_H_part2)) ++ (cache_577_H_part3 ++ (cache_577_H_part4 ++ cache_577_H_part5)))

def cache_577 : ListRow := ⟨cache_577_A, cache_577_H, 21⟩

def cache_578_A_part0 : List Cell := [(0, -3), (0, -2), (1, 0), (1, 1)]

def cache_578_A : List Cell := cache_578_A_part0

def cache_578_H_part0 : List Cell := [(-8, -1), (-8, 1), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5)]

def cache_578_H_part1 : List Cell := [(-5, 6), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8)]

def cache_578_H_part2 : List Cell := [(-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8)]

def cache_578_H_part3 : List Cell := [(-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_578_H_part4 : List Cell := [(1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)]

def cache_578_H_part5 : List Cell := [(3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)]

def cache_578_H_part6 : List Cell := [(7, 3), (7, 4), (7, 5)]

def cache_578_H : List Cell := ((cache_578_H_part0 ++ (cache_578_H_part1 ++ cache_578_H_part2)) ++ ((cache_578_H_part3 ++ cache_578_H_part4) ++ (cache_578_H_part5 ++ cache_578_H_part6)))

def cache_578 : ListRow := ⟨cache_578_A, cache_578_H, 25⟩

def cache_579_A_part0 : List Cell := [(0, -3), (0, -2), (1, 0), (1, 1)]

def cache_579_A : List Cell := cache_579_A_part0

def cache_579_H_part0 : List Cell := [(-6, 3), (-6, 4), (-6, 5), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8)]

def cache_579_H_part1 : List Cell := [(-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2)]

def cache_579_H_part2 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)]

def cache_579_H_part3 : List Cell := [(1, 11), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)]

def cache_579_H_part4 : List Cell := [(3, 9), (3, 10), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)]

def cache_579_H_part5 : List Cell := [(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)]

def cache_579_H_part6 : List Cell := [(9, -1), (9, 1), (9, 3)]

def cache_579_H : List Cell := ((cache_579_H_part0 ++ (cache_579_H_part1 ++ cache_579_H_part2)) ++ ((cache_579_H_part3 ++ cache_579_H_part4) ++ (cache_579_H_part5 ++ cache_579_H_part6)))

def cache_579 : ListRow := ⟨cache_579_A, cache_579_H, 25⟩

def cache_580_A_part0 : List Cell := [(-1, -4), (-1, -3), (0, -3), (0, -1)]

def cache_580_A : List Cell := cache_580_A_part0

def cache_580_H_part0 : List Cell := [(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7)]

def cache_580_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -4), (-1, -3)]

def cache_580_H_part2 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]

def cache_580_H_part3 : List Cell := [(0, 8), (0, 9), (0, 10), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_580_H_part4 : List Cell := [(2, 6), (2, 7), (2, 8), (2, 9), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_580_H_part5 : List Cell := [(4, 4), (4, 5), (4, 6), (4, 7), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0)]

def cache_580_H_part6 : List Cell := [(7, 1), (7, 2), (8, -2), (8, 0), (8, 2)]

def cache_580_H : List Cell := ((cache_580_H_part0 ++ (cache_580_H_part1 ++ cache_580_H_part2)) ++ ((cache_580_H_part3 ++ cache_580_H_part4) ++ (cache_580_H_part5 ++ cache_580_H_part6)))

def cache_580 : ListRow := ⟨cache_580_A, cache_580_H, 26⟩

def cache_581_A_part0 : List Cell := [(0, -3), (0, -1), (1, -4), (1, -3)]

def cache_581_A : List Cell := cache_581_A_part0

def cache_581_H_part0 : List Cell := [(-6, 2), (-6, 3), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7)]

def cache_581_H_part1 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2)]

def cache_581_H_part2 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_581_H_part3 : List Cell := [(1, 8), (1, 9), (1, 10), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]

def cache_581_H_part4 : List Cell := [(3, 6), (3, 7), (3, 8), (3, 9), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_581_H_part5 : List Cell := [(5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0)]

def cache_581_H_part6 : List Cell := [(8, 1), (8, 2), (9, -2), (9, 0), (9, 2)]

def cache_581_H : List Cell := ((cache_581_H_part0 ++ (cache_581_H_part1 ++ cache_581_H_part2)) ++ ((cache_581_H_part3 ++ cache_581_H_part4) ++ (cache_581_H_part5 ++ cache_581_H_part6)))

def cache_581 : ListRow := ⟨cache_581_A, cache_581_H, 26⟩

def cache_582_A_part0 : List Cell := [(1, -4), (1, -3), (1, -2), (2, -4)]

def cache_582_A : List Cell := cache_582_A_part0

def cache_582_H_part0 : List Cell := [(-6, 1), (-6, 2), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)]

def cache_582_H_part1 : List Cell := [(-3, 5), (-3, 6), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)]

def cache_582_H_part2 : List Cell := [(-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_582_H_part3 : List Cell := [(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2)]

def cache_582_H_part4 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)]

def cache_582_H_part5 : List Cell := [(4, 7), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 2), (6, 4)]

def cache_582_H_part6 : List Cell := [(7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (9, -3), (9, -2), (9, -1), (10, -3), (10, -1)]

def cache_582_H : List Cell := ((cache_582_H_part0 ++ (cache_582_H_part1 ++ cache_582_H_part2)) ++ ((cache_582_H_part3 ++ cache_582_H_part4) ++ (cache_582_H_part5 ++ cache_582_H_part6)))

def cache_582 : ListRow := ⟨cache_582_A, cache_582_H, 24⟩

def cache_583_A_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2)]

def cache_583_A : List Cell := cache_583_A_part0

def cache_583_H_part0 : List Cell := [(-8, 5), (-8, 6), (-8, 8), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-6, 1), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)]

def cache_583_H_part1 : List Cell := [(-5, 9), (-5, 10), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8)]

def cache_583_H_part2 : List Cell := [(-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)]

def cache_583_H_part3 : List Cell := [(-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5), (1, -4), (1, -3), (1, -2)]

def cache_583_H_part4 : List Cell := [(1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6)]

def cache_583_H_part5 : List Cell := [(2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)]

def cache_583_H_part6 : List Cell := [(4, 2), (4, 3), (4, 6), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 2), (7, 3), (8, 1), (8, 3)]

def cache_583_H : List Cell := ((cache_583_H_part0 ++ (cache_583_H_part1 ++ cache_583_H_part2)) ++ ((cache_583_H_part3 ++ cache_583_H_part4) ++ (cache_583_H_part5 ++ cache_583_H_part6)))

def cache_583 : ListRow := ⟨cache_583_A, cache_583_H, 25⟩

def cache_584_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_584_A : List Cell := cache_584_A_part0

def cache_584_H_part0 : List Cell := [(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -5), (-5, -4)]

def cache_584_H_part1 : List Cell := [(-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -6), (-3, -5), (-3, -4), (-3, -3)]

def cache_584_H_part2 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -2)]

def cache_584_H_part3 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2)]

def cache_584_H_part4 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_584_H_part5 : List Cell := [(4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_584_H_part6 : List Cell := [(8, -2), (8, -1), (8, 0), (9, -2), (9, 0)]

def cache_584_H : List Cell := ((cache_584_H_part0 ++ (cache_584_H_part1 ++ cache_584_H_part2)) ++ ((cache_584_H_part3 ++ cache_584_H_part4) ++ (cache_584_H_part5 ++ cache_584_H_part6)))

def cache_584 : ListRow := ⟨cache_584_A, cache_584_H, 22⟩

def cache_585_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_585_A : List Cell := cache_585_A_part0

def cache_585_H_part0 : List Cell := [(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1)]

def cache_585_H_part1 : List Cell := [(-5, 0), (-5, 1), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -7), (-2, -6)]

def cache_585_H_part2 : List Cell := [(-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4)]

def cache_585_H_part3 : List Cell := [(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4)]

def cache_585_H_part4 : List Cell := [(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -5)]

def cache_585_H_part5 : List Cell := [(5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1)]

def cache_585_H_part6 : List Cell := [(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)]

def cache_585_H : List Cell := ((cache_585_H_part0 ++ (cache_585_H_part1 ++ cache_585_H_part2)) ++ ((cache_585_H_part3 ++ cache_585_H_part4) ++ (cache_585_H_part5 ++ cache_585_H_part6)))

def cache_585 : ListRow := ⟨cache_585_A, cache_585_H, 22⟩

def cache_586_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_586_A : List Cell := cache_586_A_part0

def cache_586_H_part0 : List Cell := [(-7, 3), (-7, 4), (-7, 6), (-6, 1), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)]

def cache_586_H_part1 : List Cell := [(-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3)]

def cache_586_H_part2 : List Cell := [(-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1)]

def cache_586_H_part3 : List Cell := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)]

def cache_586_H_part4 : List Cell := [(2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0)]

def cache_586_H_part5 : List Cell := [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)]

def cache_586_H_part6 : List Cell := [(5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)]

def cache_586_H_part7 : List Cell := [(7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3)]

def cache_586_H_part8 : List Cell := [(9, 4), (10, -2), (10, -1), (10, 0), (11, -2), (11, 0)]

def cache_586_H : List Cell := (((cache_586_H_part0 ++ cache_586_H_part1) ++ (cache_586_H_part2 ++ cache_586_H_part3)) ++ ((cache_586_H_part4 ++ cache_586_H_part5) ++ (cache_586_H_part6 ++ (cache_586_H_part7 ++ cache_586_H_part8))))

def cache_586 : ListRow := ⟨cache_586_A, cache_586_H, 26⟩

def cache_587_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_587_A : List Cell := cache_587_A_part0

def cache_587_H_part0 : List Cell := [(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)]

def cache_587_H_part1 : List Cell := [(-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -5), (-1, -4), (-1, -3)]

def cache_587_H_part2 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -7)]

def cache_587_H_part3 : List Cell := [(2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)]

def cache_587_H_part4 : List Cell := [(3, 5), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_587_H_part5 : List Cell := [(5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0)]

def cache_587_H_part6 : List Cell := [(8, 1), (9, -2), (9, -1), (9, 0), (9, 1)]

def cache_587_H : List Cell := ((cache_587_H_part0 ++ (cache_587_H_part1 ++ cache_587_H_part2)) ++ ((cache_587_H_part3 ++ cache_587_H_part4) ++ (cache_587_H_part5 ++ cache_587_H_part6)))

def cache_587 : ListRow := ⟨cache_587_A, cache_587_H, 22⟩

def cache_588_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (0, -1)]

def cache_588_A : List Cell := cache_588_A_part0

def cache_588_H_part0 : List Cell := [(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4)]

def cache_588_H_part1 : List Cell := [(-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4)]

def cache_588_H_part2 : List Cell := [(-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12)]

def cache_588_H_part3 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_588_H_part4 : List Cell := [(1, 7), (1, 8), (1, 9), (1, 10), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3)]

def cache_588_H_part5 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_588_H_part6 : List Cell := [(4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)]

def cache_588_H_part7 : List Cell := [(6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -1), (9, 0)]

def cache_588_H_part8 : List Cell := [(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)]

def cache_588_H : List Cell := (((cache_588_H_part0 ++ cache_588_H_part1) ++ (cache_588_H_part2 ++ cache_588_H_part3)) ++ ((cache_588_H_part4 ++ cache_588_H_part5) ++ (cache_588_H_part6 ++ (cache_588_H_part7 ++ cache_588_H_part8))))

def cache_588 : ListRow := ⟨cache_588_A, cache_588_H, 27⟩

def cache_589_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1)]

def cache_589_A : List Cell := cache_589_A_part0

def cache_589_H_part0 : List Cell := [(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5)]

def cache_589_H_part1 : List Cell := [(-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)]

def cache_589_H_part2 : List Cell := [(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12)]

def cache_589_H_part3 : List Cell := [(-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_589_H_part4 : List Cell := [(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4)]

def cache_589_H_part5 : List Cell := [(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_589_H_part6 : List Cell := [(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2)]

def cache_589_H_part7 : List Cell := [(6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)]

def cache_589_H_part8 : List Cell := [(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)]

def cache_589_H : List Cell := (((cache_589_H_part0 ++ cache_589_H_part1) ++ (cache_589_H_part2 ++ cache_589_H_part3)) ++ ((cache_589_H_part4 ++ cache_589_H_part5) ++ (cache_589_H_part6 ++ (cache_589_H_part7 ++ cache_589_H_part8))))

def cache_589 : ListRow := ⟨cache_589_A, cache_589_H, 28⟩

def cache_590_A_part0 : List Cell := [(0, 1), (0, 2)]

def cache_590_A : List Cell := cache_590_A_part0

def cache_590_H_part0 : List Cell := [(-9, 1), (-9, 3), (-8, 1), (-8, 2), (-8, 3), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1)]

def cache_590_H_part1 : List Cell := [(-5, 2), (-5, 3), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -5), (-2, -4), (-2, -3)]

def cache_590_H_part2 : List Cell := [(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_590_H_part3 : List Cell := [(0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)]

def cache_590_H_part4 : List Cell := [(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1)]

def cache_590_H_part5 : List Cell := [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_590_H_part6 : List Cell := [(7, 5), (7, 6), (7, 7), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 0), (9, 2), (9, 3), (9, 4), (9, 5), (10, 2), (10, 3), (10, 4), (10, 5)]

def cache_590_H : List Cell := ((cache_590_H_part0 ++ (cache_590_H_part1 ++ cache_590_H_part2)) ++ ((cache_590_H_part3 ++ cache_590_H_part4) ++ (cache_590_H_part5 ++ cache_590_H_part6)))

def cache_590 : ListRow := ⟨cache_590_A, cache_590_H, 23⟩

def cache_591_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_591_A : List Cell := cache_591_A_part0

def cache_591_H_part0 : List Cell := [(-10, -1), (-10, 0), (-10, 1), (-10, 2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-8, -4), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4)]

def cache_591_H_part1 : List Cell := [(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0)]

def cache_591_H_part2 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)]

def cache_591_H_part3 : List Cell := [(-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1)]

def cache_591_H_part4 : List Cell := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)]

def cache_591_H_part5 : List Cell := [(3, 3), (3, 4), (3, 5), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3)]

def cache_591_H_part6 : List Cell := [(6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1)]

def cache_591_H_part7 : List Cell := [(9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)]

def cache_591_H : List Cell := (((cache_591_H_part0 ++ cache_591_H_part1) ++ (cache_591_H_part2 ++ cache_591_H_part3)) ++ ((cache_591_H_part4 ++ cache_591_H_part5) ++ (cache_591_H_part6 ++ cache_591_H_part7)))

def cache_591 : ListRow := ⟨cache_591_A, cache_591_H, 23⟩

def cache_592_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1)]

def cache_592_A : List Cell := cache_592_A_part0

def cache_592_H_part0 : List Cell := [(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5)]

def cache_592_H_part1 : List Cell := [(-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -6), (-2, -5), (-2, -4), (-2, 0), (-2, 1), (-2, 2)]

def cache_592_H_part2 : List Cell := [(-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8)]

def cache_592_H_part3 : List Cell := [(-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2)]

def cache_592_H_part4 : List Cell := [(1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_592_H_part5 : List Cell := [(2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4)]

def cache_592_H_part6 : List Cell := [(4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7)]

def cache_592_H_part7 : List Cell := [(5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)]

def cache_592_H_part8 : List Cell := [(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)]

def cache_592_H : List Cell := (((cache_592_H_part0 ++ cache_592_H_part1) ++ (cache_592_H_part2 ++ cache_592_H_part3)) ++ ((cache_592_H_part4 ++ cache_592_H_part5) ++ (cache_592_H_part6 ++ (cache_592_H_part7 ++ cache_592_H_part8))))

def cache_592 : ListRow := ⟨cache_592_A, cache_592_H, 28⟩

def cache_593_A_part0 : List Cell := [(-1, -4), (-1, -3), (0, -3), (0, -1)]

def cache_593_A : List Cell := cache_593_A_part0

def cache_593_H_part0 : List Cell := [(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4)]

def cache_593_H_part1 : List Cell := [(-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4)]

def cache_593_H_part2 : List Cell := [(-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (0, -3), (0, -2)]

def cache_593_H_part3 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_593_H_part4 : List Cell := [(1, 7), (1, 8), (1, 9), (1, 10), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3)]

def cache_593_H_part5 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def cache_593_H_part6 : List Cell := [(4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)]

def cache_593_H_part7 : List Cell := [(6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -1), (9, 0)]

def cache_593_H_part8 : List Cell := [(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)]

def cache_593_H : List Cell := (((cache_593_H_part0 ++ cache_593_H_part1) ++ (cache_593_H_part2 ++ cache_593_H_part3)) ++ ((cache_593_H_part4 ++ cache_593_H_part5) ++ (cache_593_H_part6 ++ (cache_593_H_part7 ++ cache_593_H_part8))))

def cache_593 : ListRow := ⟨cache_593_A, cache_593_H, 27⟩

def cache_594_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1)]

def cache_594_A : List Cell := cache_594_A_part0

def cache_594_H_part0 : List Cell := [(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5)]

def cache_594_H_part1 : List Cell := [(-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)]

def cache_594_H_part2 : List Cell := [(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12)]

def cache_594_H_part3 : List Cell := [(-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_594_H_part4 : List Cell := [(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9)]

def cache_594_H_part5 : List Cell := [(2, 10), (2, 11), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2)]

def cache_594_H_part6 : List Cell := [(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)]

def cache_594_H_part7 : List Cell := [(6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)]

def cache_594_H_part8 : List Cell := [(8, -3), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)]

def cache_594_H : List Cell := (((cache_594_H_part0 ++ cache_594_H_part1) ++ (cache_594_H_part2 ++ cache_594_H_part3)) ++ ((cache_594_H_part4 ++ cache_594_H_part5) ++ (cache_594_H_part6 ++ (cache_594_H_part7 ++ cache_594_H_part8))))

def cache_594 : ListRow := ⟨cache_594_A, cache_594_H, 28⟩

def cache_595_A_part0 : List Cell := [(-1, 0)]

def cache_595_A : List Cell := cache_595_A_part0

def cache_595_H_part0 : List Cell := [(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1)]

def cache_595_H_part1 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -5), (-1, -4), (-1, -3)]

def cache_595_H_part2 : List Cell := [(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_595_H_part3 : List Cell := [(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)]

def cache_595_H_part4 : List Cell := [(1, 11), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1)]

def cache_595_H_part5 : List Cell := [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)]

def cache_595_H_part6 : List Cell := [(4, 9), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1)]

def cache_595_H_part7 : List Cell := [(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -5), (8, -4)]

def cache_595_H_part8 : List Cell := [(8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2)]

def cache_595_H_part9 : List Cell := [(10, 3), (11, -3), (11, -2), (11, -1), (12, -3), (12, -1)]

def cache_595_H : List Cell := (((cache_595_H_part0 ++ cache_595_H_part1) ++ (cache_595_H_part2 ++ (cache_595_H_part3 ++ cache_595_H_part4))) ++ ((cache_595_H_part5 ++ cache_595_H_part6) ++ (cache_595_H_part7 ++ (cache_595_H_part8 ++ cache_595_H_part9))))

def cache_595 : ListRow := ⟨cache_595_A, cache_595_H, 27⟩

def cache_596_A_part0 : List Cell := [(0, -1), (0, 1)]

def cache_596_A : List Cell := cache_596_A_part0

def cache_596_H_part0 : List Cell := [(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7)]

def cache_596_H_part1 : List Cell := [(-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3)]

def cache_596_H_part2 : List Cell := [(-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)]

def cache_596_H_part3 : List Cell := [(0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11)]

def cache_596_H_part4 : List Cell := [(1, 12), (1, 13), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, -5), (3, -4), (3, -3)]

def cache_596_H_part5 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)]

def cache_596_H_part6 : List Cell := [(4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)]

def cache_596_H_part7 : List Cell := [(5, 10), (5, 11), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)]

def cache_596_H_part8 : List Cell := [(7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8)]

def cache_596_H_part9 : List Cell := [(10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)]

def cache_596_H : List Cell := (((cache_596_H_part0 ++ cache_596_H_part1) ++ (cache_596_H_part2 ++ (cache_596_H_part3 ++ cache_596_H_part4))) ++ ((cache_596_H_part5 ++ cache_596_H_part6) ++ (cache_596_H_part7 ++ (cache_596_H_part8 ++ cache_596_H_part9))))

def cache_596 : ListRow := ⟨cache_596_A, cache_596_H, 29⟩

def cache_597_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, 0)]

def cache_597_A : List Cell := cache_597_A_part0

def cache_597_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -2), (-1, -1), (-1, 0), (-1, 2)]

def cache_597_H_part1 : List Cell := [(-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_597_H_part2 : List Cell := [(1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)]

def cache_597_H_part3 : List Cell := [(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11)]

def cache_597_H_part4 : List Cell := [(4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2)]

def cache_597_H_part5 : List Cell := [(6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9)]

def cache_597_H_part6 : List Cell := [(7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0)]

def cache_597_H_part7 : List Cell := [(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3)]

def cache_597_H_part8 : List Cell := [(11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -4), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3)]

def cache_597_H_part9 : List Cell := [(13, 4), (14, -2), (14, -1), (14, 0), (15, -2), (15, 0)]

def cache_597_H : List Cell := (((cache_597_H_part0 ++ cache_597_H_part1) ++ (cache_597_H_part2 ++ (cache_597_H_part3 ++ cache_597_H_part4))) ++ ((cache_597_H_part5 ++ cache_597_H_part6) ++ (cache_597_H_part7 ++ (cache_597_H_part8 ++ cache_597_H_part9))))

def cache_597 : ListRow := ⟨cache_597_A, cache_597_H, 29⟩

def cache_598_A_part0 : List Cell := [(-3, -2), (-2, -2), (-2, -1), (0, -1), (0, 1)]

def cache_598_A : List Cell := cache_598_A_part0

def cache_598_H_part0 : List Cell := [(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, -2), (-3, 2), (-3, 3), (-3, 4), (-3, 5)]

def cache_598_H_part1 : List Cell := [(-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -2), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4)]

def cache_598_H_part2 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)]

def cache_598_H_part3 : List Cell := [(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)]

def cache_598_H_part4 : List Cell := [(1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13)]

def cache_598_H_part5 : List Cell := [(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0)]

def cache_598_H_part6 : List Cell := [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7)]

def cache_598_H_part7 : List Cell := [(5, 8), (5, 9), (5, 10), (5, 11), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2)]

def cache_598_H_part8 : List Cell := [(7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, -1), (9, 1), (9, 2), (9, 3), (9, 4)]

def cache_598_H_part9 : List Cell := [(9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)]

def cache_598_H : List Cell := (((cache_598_H_part0 ++ cache_598_H_part1) ++ (cache_598_H_part2 ++ (cache_598_H_part3 ++ cache_598_H_part4))) ++ ((cache_598_H_part5 ++ cache_598_H_part6) ++ (cache_598_H_part7 ++ (cache_598_H_part8 ++ cache_598_H_part9))))

def cache_598 : ListRow := ⟨cache_598_A, cache_598_H, 29⟩

def cache_599_A_part0 : List Cell := [(0, -3), (0, -1), (1, -4), (1, -3)]

def cache_599_A : List Cell := cache_599_A_part0

def cache_599_H_part0 : List Cell := [(-11, -1), (-11, 1), (-10, -1), (-10, 0), (-10, 1), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-7, -4), (-7, -3), (-7, -2), (-7, -1)]

def cache_599_H_part1 : List Cell := [(-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0)]

def cache_599_H_part2 : List Cell := [(-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -5), (-3, -4)]

def cache_599_H_part3 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3)]

def cache_599_H_part4 : List Cell := [(-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3)]

def cache_599_H_part5 : List Cell := [(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_599_H_part6 : List Cell := [(1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -3), (3, -2), (3, -1), (3, 0)]

def cache_599_H_part7 : List Cell := [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)]

def cache_599_H_part8 : List Cell := [(4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)]

def cache_599_H_part9 : List Cell := [(6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)]

def cache_599_H : List Cell := (((cache_599_H_part0 ++ cache_599_H_part1) ++ (cache_599_H_part2 ++ (cache_599_H_part3 ++ cache_599_H_part4))) ++ ((cache_599_H_part5 ++ cache_599_H_part6) ++ (cache_599_H_part7 ++ (cache_599_H_part8 ++ cache_599_H_part9))))

def cache_599 : ListRow := ⟨cache_599_A, cache_599_H, 27⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_CacheData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cache_600_A_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1)]

def cache_600_A : List Cell := cache_600_A_part0

def cache_600_H_part0 : List Cell := [(-5, -1), (-5, 1), (-5, 2), (-5, 4), (-4, -5), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6)]

def cache_600_H_part1 : List Cell := [(-3, 7), (-3, 8), (-3, 9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3)]

def cache_600_H_part2 : List Cell := [(-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_600_H_part3 : List Cell := [(0, 5), (0, 6), (0, 7), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -11)]

def cache_600_H_part4 : List Cell := [(2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7)]

def cache_600_H_part5 : List Cell := [(3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1)]

def cache_600_H_part6 : List Cell := [(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -10), (6, -9), (6, -8)]

def cache_600_H_part7 : List Cell := [(6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1)]

def cache_600_H_part8 : List Cell := [(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -7), (9, -6), (9, -5)]

def cache_600_H_part9 : List Cell := [(9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (11, -4), (11, -3), (11, -2)]

def cache_600_H_part10 : List Cell := [(11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 4), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)]

def cache_600_H : List Cell := (((cache_600_H_part0 ++ cache_600_H_part1) ++ (cache_600_H_part2 ++ (cache_600_H_part3 ++ cache_600_H_part4))) ++ ((cache_600_H_part5 ++ (cache_600_H_part6 ++ cache_600_H_part7)) ++ (cache_600_H_part8 ++ (cache_600_H_part9 ++ cache_600_H_part10))))

def cache_600 : ListRow := ⟨cache_600_A, cache_600_H, 29⟩

def cache_601_A_part0 : List Cell := [(0, -2), (0, -1)]

def cache_601_A : List Cell := cache_601_A_part0

def cache_601_H_part0 : List Cell := [(-9, -3), (-9, -1), (-8, -3), (-8, -2), (-8, -1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 6)]

def cache_601_H_part1 : List Cell := [(-6, 7), (-6, 9), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0)]

def cache_601_H_part2 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)]

def cache_601_H_part3 : List Cell := [(-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9)]

def cache_601_H_part4 : List Cell := [(-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -5)]

def cache_601_H_part5 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2)]

def cache_601_H_part6 : List Cell := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

def cache_601_H_part7 : List Cell := [(2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11)]

def cache_601_H_part8 : List Cell := [(3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)]

def cache_601_H_part9 : List Cell := [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, -2), (7, -1)]

def cache_601_H_part10 : List Cell := [(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3)]

def cache_601_H_part11 : List Cell := [(9, 4), (9, 5), (9, 6), (9, 7), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, 1), (11, 2), (11, 3), (12, 1), (12, 3)]

def cache_601_H : List Cell := (((cache_601_H_part0 ++ (cache_601_H_part1 ++ cache_601_H_part2)) ++ (cache_601_H_part3 ++ (cache_601_H_part4 ++ cache_601_H_part5))) ++ ((cache_601_H_part6 ++ (cache_601_H_part7 ++ cache_601_H_part8)) ++ (cache_601_H_part9 ++ (cache_601_H_part10 ++ cache_601_H_part11))))

def cache_601 : ListRow := ⟨cache_601_A, cache_601_H, 29⟩

def cache_602_A_part0 : List Cell := [(0, 1), (0, 2)]

def cache_602_A : List Cell := cache_602_A_part0

def cache_602_H_part0 : List Cell := [(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 8)]

def cache_602_H_part1 : List Cell := [(-6, 9), (-6, 11), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2)]

def cache_602_H_part2 : List Cell := [(-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6)]

def cache_602_H_part3 : List Cell := [(-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11)]

def cache_602_H_part4 : List Cell := [(-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -3)]

def cache_602_H_part5 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_602_H_part6 : List Cell := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)]

def cache_602_H_part7 : List Cell := [(2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13)]

def cache_602_H_part8 : List Cell := [(3, 14), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)]

def cache_602_H_part9 : List Cell := [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1)]

def cache_602_H_part10 : List Cell := [(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5)]

def cache_602_H_part11 : List Cell := [(9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 3), (11, 4), (11, 5), (12, 3), (12, 5)]

def cache_602_H : List Cell := (((cache_602_H_part0 ++ (cache_602_H_part1 ++ cache_602_H_part2)) ++ (cache_602_H_part3 ++ (cache_602_H_part4 ++ cache_602_H_part5))) ++ ((cache_602_H_part6 ++ (cache_602_H_part7 ++ cache_602_H_part8)) ++ (cache_602_H_part9 ++ (cache_602_H_part10 ++ cache_602_H_part11))))

def cache_602 : ListRow := ⟨cache_602_A, cache_602_H, 29⟩

def cache_603_A_part0 : List Cell := [(-1, 0)]

def cache_603_A : List Cell := cache_603_A_part0

def cache_603_H_part0 : List Cell := [(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 1)]

def cache_603_H_part1 : List Cell := [(-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -8), (-2, -7), (-2, -6)]

def cache_603_H_part2 : List Cell := [(-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1)]

def cache_603_H_part3 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)]

def cache_603_H_part4 : List Cell := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_603_H_part5 : List Cell := [(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6)]

def cache_603_H_part6 : List Cell := [(2, 7), (2, 8), (2, 9), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -9), (4, -8)]

def cache_603_H_part7 : List Cell := [(4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3)]

def cache_603_H_part8 : List Cell := [(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4)]

def cache_603_H_part9 : List Cell := [(6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0)]

def cache_603_H_part10 : List Cell := [(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3)]

def cache_603_H_part11 : List Cell := [(10, 5), (11, -3), (11, -2), (11, -1), (11, 1), (11, 2), (11, 3), (12, -3), (12, -1), (12, 1), (12, 3)]

def cache_603_H : List Cell := (((cache_603_H_part0 ++ (cache_603_H_part1 ++ cache_603_H_part2)) ++ (cache_603_H_part3 ++ (cache_603_H_part4 ++ cache_603_H_part5))) ++ ((cache_603_H_part6 ++ (cache_603_H_part7 ++ cache_603_H_part8)) ++ (cache_603_H_part9 ++ (cache_603_H_part10 ++ cache_603_H_part11))))

def cache_603 : ListRow := ⟨cache_603_A, cache_603_H, 27⟩

def cache_604_A_part0 : List Cell := [(-2, -1), (-2, 0), (-1, -2), (0, -2)]

def cache_604_A : List Cell := cache_604_A_part0

def cache_604_H_part0 : List Cell := [(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6)]

def cache_604_H_part1 : List Cell := [(-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3)]

def cache_604_H_part2 : List Cell := [(-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)]

def cache_604_H_part3 : List Cell := [(-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10)]

def cache_604_H_part4 : List Cell := [(0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4)]

def cache_604_H_part5 : List Cell := [(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)]

def cache_604_H_part6 : List Cell := [(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9)]

def cache_604_H_part7 : List Cell := [(4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1)]

def cache_604_H_part8 : List Cell := [(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)]

def cache_604_H_part9 : List Cell := [(7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1)]

def cache_604_H_part10 : List Cell := [(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1)]

def cache_604_H_part11 : List Cell := [(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)]

def cache_604_H : List Cell := (((cache_604_H_part0 ++ (cache_604_H_part1 ++ cache_604_H_part2)) ++ (cache_604_H_part3 ++ (cache_604_H_part4 ++ cache_604_H_part5))) ++ ((cache_604_H_part6 ++ (cache_604_H_part7 ++ cache_604_H_part8)) ++ (cache_604_H_part9 ++ (cache_604_H_part10 ++ cache_604_H_part11))))

def cache_604 : ListRow := ⟨cache_604_A, cache_604_H, 30⟩

def cache_605_A_part0 : List Cell := [(-3, -3), (-2, -3), (-2, -2), (-2, 0), (0, -2)]

def cache_605_A : List Cell := cache_605_A_part0

def cache_605_H_part0 : List Cell := [(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1)]

def cache_605_H_part1 : List Cell := [(-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8)]

def cache_605_H_part2 : List Cell := [(-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4)]

def cache_605_H_part3 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0)]

def cache_605_H_part4 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)]

def cache_605_H_part5 : List Cell := [(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)]

def cache_605_H_part6 : List Cell := [(2, 9), (2, 10), (2, 11), (2, 12), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -6), (4, -5)]

def cache_605_H_part7 : List Cell := [(4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)]

def cache_605_H_part8 : List Cell := [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)]

def cache_605_H_part9 : List Cell := [(6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0)]

def cache_605_H_part10 : List Cell := [(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3)]

def cache_605_H_part11 : List Cell := [(10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1)]

def cache_605_H_part12 : List Cell := [(12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)]

def cache_605_H : List Cell := (((cache_605_H_part0 ++ (cache_605_H_part1 ++ cache_605_H_part2)) ++ (cache_605_H_part3 ++ (cache_605_H_part4 ++ cache_605_H_part5))) ++ ((cache_605_H_part6 ++ (cache_605_H_part7 ++ cache_605_H_part8)) ++ ((cache_605_H_part9 ++ cache_605_H_part10) ++ (cache_605_H_part11 ++ cache_605_H_part12))))

def cache_605 : ListRow := ⟨cache_605_A, cache_605_H, 30⟩

def cache_606_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (2, -2)]

def cache_606_A : List Cell := cache_606_A_part0

def cache_606_H_part0 : List Cell := [(-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1)]

def cache_606_H_part1 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)]

def cache_606_H_part2 : List Cell := [(-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6)]

def cache_606_H_part3 : List Cell := [(1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2)]

def cache_606_H_part4 : List Cell := [(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1)]

def cache_606_H_part5 : List Cell := [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)]

def cache_606_H_part6 : List Cell := [(4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12)]

def cache_606_H_part7 : List Cell := [(6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0)]

def cache_606_H_part8 : List Cell := [(7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7)]

def cache_606_H_part9 : List Cell := [(8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2)]

def cache_606_H_part10 : List Cell := [(10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7)]

def cache_606_H_part11 : List Cell := [(12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1)]

def cache_606_H_part12 : List Cell := [(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)]

def cache_606_H : List Cell := (((cache_606_H_part0 ++ (cache_606_H_part1 ++ cache_606_H_part2)) ++ (cache_606_H_part3 ++ (cache_606_H_part4 ++ cache_606_H_part5))) ++ ((cache_606_H_part6 ++ (cache_606_H_part7 ++ cache_606_H_part8)) ++ ((cache_606_H_part9 ++ cache_606_H_part10) ++ (cache_606_H_part11 ++ cache_606_H_part12))))

def cache_606 : ListRow := ⟨cache_606_A, cache_606_H, 31⟩

def cache_607_A_part0 : List Cell := [(-1, -2), (0, -3), (0, -2), (0, -1)]

def cache_607_A : List Cell := cache_607_A_part0

def cache_607_H_part0 : List Cell := [(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 6), (-6, 7), (-6, 9), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -5), (-4, -4), (-4, -3)]

def cache_607_H_part1 : List Cell := [(-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)]

def cache_607_H_part2 : List Cell := [(-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13)]

def cache_607_H_part3 : List Cell := [(-2, 14), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def cache_607_H_part4 : List Cell := [(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)]

def cache_607_H_part5 : List Cell := [(1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -6), (3, -5), (3, -4)]

def cache_607_H_part6 : List Cell := [(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0)]

def cache_607_H_part7 : List Cell := [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)]

def cache_607_H_part8 : List Cell := [(5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)]

def cache_607_H_part9 : List Cell := [(7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1)]

def cache_607_H_part10 : List Cell := [(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -6)]

def cache_607_H_part11 : List Cell := [(10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (12, -4), (12, -3)]

def cache_607_H_part12 : List Cell := [(12, -2), (12, -1), (12, 0), (12, 1), (12, 3), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1)]

def cache_607_H : List Cell := (((cache_607_H_part0 ++ (cache_607_H_part1 ++ cache_607_H_part2)) ++ (cache_607_H_part3 ++ (cache_607_H_part4 ++ cache_607_H_part5))) ++ ((cache_607_H_part6 ++ (cache_607_H_part7 ++ cache_607_H_part8)) ++ ((cache_607_H_part9 ++ cache_607_H_part10) ++ (cache_607_H_part11 ++ cache_607_H_part12))))

def cache_607 : ListRow := ⟨cache_607_A, cache_607_H, 29⟩

def cache_608_A_part0 : List Cell := [(-1, -3), (-1, -2), (0, -2)]

def cache_608_A : List Cell := cache_608_A_part0

def cache_608_H_part0 : List Cell := [(-9, -1), (-9, 1), (-9, 3), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 8), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3)]

def cache_608_H_part1 : List Cell := [(-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1)]

def cache_608_H_part2 : List Cell := [(-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12)]

def cache_608_H_part3 : List Cell := [(-3, 13), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)]

def cache_608_H_part4 : List Cell := [(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12)]

def cache_608_H_part5 : List Cell := [(0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -7)]

def cache_608_H_part6 : List Cell := [(2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -7), (3, -6), (3, -5)]

def cache_608_H_part7 : List Cell := [(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1)]

def cache_608_H_part8 : List Cell := [(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)]

def cache_608_H_part9 : List Cell := [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)]

def cache_608_H_part10 : List Cell := [(6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1)]

def cache_608_H_part11 : List Cell := [(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6)]

def cache_608_H_part12 : List Cell := [(9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1)]

def cache_608_H_part13 : List Cell := [(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1)]

def cache_608_H_part14 : List Cell := [(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)]

def cache_608_H : List Cell := (((cache_608_H_part0 ++ (cache_608_H_part1 ++ cache_608_H_part2)) ++ ((cache_608_H_part3 ++ cache_608_H_part4) ++ (cache_608_H_part5 ++ cache_608_H_part6))) ++ (((cache_608_H_part7 ++ cache_608_H_part8) ++ (cache_608_H_part9 ++ cache_608_H_part10)) ++ ((cache_608_H_part11 ++ cache_608_H_part12) ++ (cache_608_H_part13 ++ cache_608_H_part14))))

def cache_608 : ListRow := ⟨cache_608_A, cache_608_H, 32⟩

def cache_609_A_part0 : List Cell := [(0, -2), (0, -1), (1, -2), (2, -2)]

def cache_609_A : List Cell := cache_609_A_part0

def cache_609_H_part0 : List Cell := [(-10, -2), (-10, -1), (-10, 0), (-10, 1), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 4), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5)]

def cache_609_H_part1 : List Cell := [(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1)]

def cache_609_H_part2 : List Cell := [(-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1)]

def cache_609_H_part3 : List Cell := [(-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11)]

def cache_609_H_part4 : List Cell := [(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0)]

def cache_609_H_part5 : List Cell := [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_609_H_part6 : List Cell := [(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)]

def cache_609_H_part7 : List Cell := [(3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3)]

def cache_609_H_part8 : List Cell := [(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)]

def cache_609_H_part9 : List Cell := [(6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10)]

def cache_609_H_part10 : List Cell := [(8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0)]

def cache_609_H_part11 : List Cell := [(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8)]

def cache_609_H_part12 : List Cell := [(11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5)]

def cache_609_H_part13 : List Cell := [(12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)]

def cache_609_H : List Cell := (((cache_609_H_part0 ++ (cache_609_H_part1 ++ cache_609_H_part2)) ++ ((cache_609_H_part3 ++ cache_609_H_part4) ++ (cache_609_H_part5 ++ cache_609_H_part6))) ++ ((cache_609_H_part7 ++ (cache_609_H_part8 ++ cache_609_H_part9)) ++ ((cache_609_H_part10 ++ cache_609_H_part11) ++ (cache_609_H_part12 ++ cache_609_H_part13))))

def cache_609 : ListRow := ⟨cache_609_A, cache_609_H, 31⟩

def cache_610_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, 0)]

def cache_610_A : List Cell := cache_610_A_part0

def cache_610_H_part0 : List Cell := [(-12, 0), (-12, 1), (-12, 2), (-12, 3), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 6), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7)]

def cache_610_H_part1 : List Cell := [(-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3)]

def cache_610_H_part2 : List Cell := [(-6, 4), (-6, 5), (-6, 6), (-6, 8), (-6, 9), (-6, 11), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)]

def cache_610_H_part3 : List Cell := [(-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13)]

def cache_610_H_part4 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2)]

def cache_610_H_part5 : List Cell := [(-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]

def cache_610_H_part6 : List Cell := [(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]

def cache_610_H_part7 : List Cell := [(1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11)]

def cache_610_H_part8 : List Cell := [(2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, -3), (4, -2), (4, -1)]

def cache_610_H_part9 : List Cell := [(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5)]

def cache_610_H_part10 : List Cell := [(5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12)]

def cache_610_H_part11 : List Cell := [(7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)]

def cache_610_H_part12 : List Cell := [(8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, -2), (10, -1), (10, 0)]

def cache_610_H_part13 : List Cell := [(10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (12, -2), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4)]

def cache_610_H_part14 : List Cell := [(12, 5), (12, 6), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)]

def cache_610_H : List Cell := (((cache_610_H_part0 ++ (cache_610_H_part1 ++ cache_610_H_part2)) ++ ((cache_610_H_part3 ++ cache_610_H_part4) ++ (cache_610_H_part5 ++ cache_610_H_part6))) ++ (((cache_610_H_part7 ++ cache_610_H_part8) ++ (cache_610_H_part9 ++ cache_610_H_part10)) ++ ((cache_610_H_part11 ++ cache_610_H_part12) ++ (cache_610_H_part13 ++ cache_610_H_part14))))

def cache_610 : ListRow := ⟨cache_610_A, cache_610_H, 32⟩

def cache_611_A_part0 : List Cell := [(-2, 0), (-1, 0)]

def cache_611_A : List Cell := cache_611_A_part0

def cache_611_H_part0 : List Cell := [(-16, 0), (-16, 2), (-15, 0), (-15, 1), (-15, 2), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 4), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4)]

def cache_611_H_part1 : List Cell := [(-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-10, -8), (-10, -7)]

def cache_611_H_part2 : List Cell := [(-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1)]

def cache_611_H_part3 : List Cell := [(-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -10), (-7, -9)]

def cache_611_H_part4 : List Cell := [(-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0)]

def cache_611_H_part5 : List Cell := [(-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -11), (-4, -10)]

def cache_611_H_part6 : List Cell := [(-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4)]

def cache_611_H_part7 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4)]

def cache_611_H_part8 : List Cell := [(-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -9), (0, -8)]

def cache_611_H_part9 : List Cell := [(0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_611_H_part10 : List Cell := [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6)]

def cache_611_H_part11 : List Cell := [(2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4)]

def cache_611_H_part12 : List Cell := [(4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5)]

def cache_611_H_part13 : List Cell := [(5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5)]

def cache_611_H_part14 : List Cell := [(7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)]

def cache_611_H_part15 : List Cell := [(8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0)]

def cache_611_H_part16 : List Cell := [(10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1)]

def cache_611_H_part17 : List Cell := [(13, 0), (14, -2), (14, 0)]

def cache_611_H : List Cell := ((((cache_611_H_part0 ++ cache_611_H_part1) ++ (cache_611_H_part2 ++ cache_611_H_part3)) ++ ((cache_611_H_part4 ++ cache_611_H_part5) ++ (cache_611_H_part6 ++ (cache_611_H_part7 ++ cache_611_H_part8)))) ++ (((cache_611_H_part9 ++ cache_611_H_part10) ++ (cache_611_H_part11 ++ cache_611_H_part12)) ++ ((cache_611_H_part13 ++ cache_611_H_part14) ++ (cache_611_H_part15 ++ (cache_611_H_part16 ++ cache_611_H_part17)))))

def cache_611 : ListRow := ⟨cache_611_A, cache_611_H, 29⟩

def cache_612_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_612_A : List Cell := cache_612_A_part0

def cache_612_H_part0 : List Cell := [(-17, 0), (-17, 2), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2), (-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 3), (-14, 4), (-13, -5), (-13, -4)]

def cache_612_H_part1 : List Cell := [(-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -8), (-11, -7)]

def cache_612_H_part2 : List Cell := [(-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -10), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1)]

def cache_612_H_part3 : List Cell := [(-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9)]

def cache_612_H_part4 : List Cell := [(-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0)]

def cache_612_H_part5 : List Cell := [(-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -12), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -11), (-5, -10)]

def cache_612_H_part6 : List Cell := [(-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3)]

def cache_612_H_part7 : List Cell := [(-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 3), (-4, 5), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4)]

def cache_612_H_part8 : List Cell := [(-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)]

def cache_612_H_part9 : List Cell := [(-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]

def cache_612_H_part10 : List Cell := [(1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3)]

def cache_612_H_part11 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)]

def cache_612_H_part12 : List Cell := [(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5)]

def cache_612_H_part13 : List Cell := [(6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2)]

def cache_612_H_part14 : List Cell := [(7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5)]

def cache_612_H_part15 : List Cell := [(9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3)]

def cache_612_H_part16 : List Cell := [(11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)]

def cache_612_H : List Cell := ((((cache_612_H_part0 ++ cache_612_H_part1) ++ (cache_612_H_part2 ++ cache_612_H_part3)) ++ ((cache_612_H_part4 ++ cache_612_H_part5) ++ (cache_612_H_part6 ++ cache_612_H_part7))) ++ (((cache_612_H_part8 ++ cache_612_H_part9) ++ (cache_612_H_part10 ++ cache_612_H_part11)) ++ ((cache_612_H_part12 ++ cache_612_H_part13) ++ (cache_612_H_part14 ++ (cache_612_H_part15 ++ cache_612_H_part16)))))

def cache_612 : ListRow := ⟨cache_612_A, cache_612_H, 29⟩

def cache_613_A_part0 : List Cell := [(-2, 0), (-1, 0), (-1, 1)]

def cache_613_A : List Cell := cache_613_A_part0

def cache_613_H_part0 : List Cell := [(-17, -2), (-17, 0), (-17, 2), (-16, -2), (-16, -1), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2), (-15, 3), (-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2)]

def cache_613_H_part1 : List Cell := [(-14, 3), (-14, 4), (-13, -5), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-13, 5), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3)]

def cache_613_H_part2 : List Cell := [(-12, 4), (-12, 5), (-12, 6), (-12, 7), (-11, -8), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-11, 7), (-11, 8), (-10, -10), (-10, -9), (-10, -8)]

def cache_613_H_part3 : List Cell := [(-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-10, 10), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5)]

def cache_613_H_part4 : List Cell := [(-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-9, 10), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2)]

def cache_613_H_part5 : List Cell := [(-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1)]

def cache_613_H_part6 : List Cell := [(-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-6, -12), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2)]

def cache_613_H_part7 : List Cell := [(-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-6, 12), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1)]

def cache_613_H_part8 : List Cell := [(-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -13), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0)]

def cache_613_H_part9 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2)]

def cache_613_H_part10 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0)]

def cache_613_H_part11 : List Cell := [(-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)]

def cache_613_H_part12 : List Cell := [(-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]

def cache_613_H_part13 : List Cell := [(0, 8), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -13)]

def cache_613_H_part14 : List Cell := [(2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11)]

def cache_613_H_part15 : List Cell := [(2, 12), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10)]

def cache_613_H_part16 : List Cell := [(3, 11), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10)]

def cache_613_H_part17 : List Cell := [(4, 11), (4, 12), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -10)]

def cache_613_H_part18 : List Cell := [(6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -10), (7, -9), (7, -8), (7, -7)]

def cache_613_H_part19 : List Cell := [(7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4)]

def cache_613_H_part20 : List Cell := [(8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1)]

def cache_613_H_part21 : List Cell := [(9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4)]

def cache_613_H_part22 : List Cell := [(11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1)]

def cache_613_H_part23 : List Cell := [(13, 2), (13, 3), (13, 4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (15, -2), (15, 0), (15, 2)]

def cache_613_H : List Cell := ((((cache_613_H_part0 ++ (cache_613_H_part1 ++ cache_613_H_part2)) ++ (cache_613_H_part3 ++ (cache_613_H_part4 ++ cache_613_H_part5))) ++ ((cache_613_H_part6 ++ (cache_613_H_part7 ++ cache_613_H_part8)) ++ (cache_613_H_part9 ++ (cache_613_H_part10 ++ cache_613_H_part11)))) ++ (((cache_613_H_part12 ++ (cache_613_H_part13 ++ cache_613_H_part14)) ++ (cache_613_H_part15 ++ (cache_613_H_part16 ++ cache_613_H_part17))) ++ ((cache_613_H_part18 ++ (cache_613_H_part19 ++ cache_613_H_part20)) ++ (cache_613_H_part21 ++ (cache_613_H_part22 ++ cache_613_H_part23)))))

def cache_613 : ListRow := ⟨cache_613_A, cache_613_H, 30⟩

def cache_614_A_part0 : List Cell := [(1, 0), (1, 1)]

def cache_614_A : List Cell := cache_614_A_part0

def cache_614_H_part0 : List Cell := [(-15, -2), (-15, 0), (-15, 2), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-13, 5), (-13, 6), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0)]

def cache_614_H_part1 : List Cell := [(-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-11, 7), (-11, 8), (-11, 9), (-10, -7), (-10, -6), (-10, -5)]

def cache_614_H_part2 : List Cell := [(-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1)]

def cache_614_H_part3 : List Cell := [(-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-9, 10), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4)]

def cache_614_H_part4 : List Cell := [(-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-8, 11), (-8, 12), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5)]

def cache_614_H_part5 : List Cell := [(-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-7, 11), (-7, 12), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6)]

def cache_614_H_part6 : List Cell := [(-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-6, 12), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7)]

def cache_614_H_part7 : List Cell := [(-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-5, 13), (-5, 14), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4)]

def cache_614_H_part8 : List Cell := [(-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1)]

def cache_614_H_part9 : List Cell := [(-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3)]

def cache_614_H_part10 : List Cell := [(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7)]

def cache_614_H_part11 : List Cell := [(-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (-1, 16), (0, -13)]

def cache_614_H_part12 : List Cell := [(0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12)]

def cache_614_H_part13 : List Cell := [(0, 13), (0, 14), (0, 15), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)]

def cache_614_H_part14 : List Cell := [(1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)]

def cache_614_H_part15 : List Cell := [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5)]

def cache_614_H_part16 : List Cell := [(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (4, -13), (4, -12)]

def cache_614_H_part17 : List Cell := [(4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12)]

def cache_614_H_part18 : List Cell := [(4, 13), (4, 14), (4, 15), (5, -12), (5, -11), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)]

def cache_614_H_part19 : List Cell := [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4)]

def cache_614_H_part20 : List Cell := [(6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2)]

def cache_614_H_part21 : List Cell := [(7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0)]

def cache_614_H_part22 : List Cell := [(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0)]

def cache_614_H_part23 : List Cell := [(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0)]

def cache_614_H_part24 : List Cell := [(10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2)]

def cache_614_H_part25 : List Cell := [(11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7)]

def cache_614_H_part26 : List Cell := [(12, 8), (12, 9), (12, 10), (13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (14, -4), (14, -3), (14, -2), (14, -1), (14, 0)]

def cache_614_H_part27 : List Cell := [(14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (15, -4), (15, -3), (15, -2), (15, -1), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (16, -2), (16, -1), (16, 0), (16, 1), (16, 2)]

def cache_614_H_part28 : List Cell := [(16, 3), (17, -2), (17, 0), (17, 1), (17, 2), (17, 3)]

def cache_614_H : List Cell := ((((cache_614_H_part0 ++ (cache_614_H_part1 ++ cache_614_H_part2)) ++ ((cache_614_H_part3 ++ cache_614_H_part4) ++ (cache_614_H_part5 ++ cache_614_H_part6))) ++ ((cache_614_H_part7 ++ (cache_614_H_part8 ++ cache_614_H_part9)) ++ ((cache_614_H_part10 ++ cache_614_H_part11) ++ (cache_614_H_part12 ++ cache_614_H_part13)))) ++ (((cache_614_H_part14 ++ (cache_614_H_part15 ++ cache_614_H_part16)) ++ ((cache_614_H_part17 ++ cache_614_H_part18) ++ (cache_614_H_part19 ++ cache_614_H_part20))) ++ (((cache_614_H_part21 ++ cache_614_H_part22) ++ (cache_614_H_part23 ++ cache_614_H_part24)) ++ ((cache_614_H_part25 ++ cache_614_H_part26) ++ (cache_614_H_part27 ++ cache_614_H_part28)))))

def cache_614 : ListRow := ⟨cache_614_A, cache_614_H, 33⟩

def cache_615_A_part0 : List Cell := [(1, 0)]

def cache_615_A : List Cell := cache_615_A_part0

def cache_615_H_part0 : List Cell := [(-15, 0), (-15, 2), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4)]

def cache_615_H_part1 : List Cell := [(-12, 5), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2)]

def cache_615_H_part2 : List Cell := [(-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7)]

def cache_615_H_part3 : List Cell := [(-9, 8), (-9, 9), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-7, -11)]

def cache_615_H_part4 : List Cell := [(-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-7, 11), (-6, -11), (-6, -10)]

def cache_615_H_part5 : List Cell := [(-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, -12), (-5, -11), (-5, -10)]

def cache_615_H_part6 : List Cell := [(-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-4, -14), (-4, -13)]

def cache_615_H_part7 : List Cell := [(-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11)]

def cache_615_H_part8 : List Cell := [(-4, 12), (-4, 13), (-4, 14), (-3, -14), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6)]

def cache_615_H_part9 : List Cell := [(-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14), (-2, -16), (-2, -15), (-2, -14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1)]

def cache_615_H_part10 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -15), (-1, -14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9)]

def cache_615_H_part11 : List Cell := [(-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15)]

def cache_615_H_part12 : List Cell := [(0, -16), (0, -15), (0, -14), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]

def cache_615_H_part13 : List Cell := [(0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -15), (1, -14), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0)]

def cache_615_H_part14 : List Cell := [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (2, -16), (2, -15), (2, -14), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9)]

def cache_615_H_part15 : List Cell := [(2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15)]

def cache_615_H_part16 : List Cell := [(2, 16), (3, -14), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)]

def cache_615_H_part17 : List Cell := [(3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (4, -14), (4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)]

def cache_615_H_part18 : List Cell := [(4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -14), (5, -13), (5, -12), (5, -11), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4)]

def cache_615_H_part19 : List Cell := [(5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, -14), (6, -13), (6, -12), (6, -11), (6, -10), (6, -9)]

def cache_615_H_part20 : List Cell := [(6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, -12)]

def cache_615_H_part21 : List Cell := [(7, -11), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12)]

def cache_615_H_part22 : List Cell := [(7, 13), (7, 14), (8, -12), (8, -11), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9)]

def cache_615_H_part23 : List Cell := [(8, 10), (8, 11), (8, 12), (9, -12), (9, -11), (9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8)]

def cache_615_H_part24 : List Cell := [(9, 9), (9, 10), (9, 11), (9, 12), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9)]

def cache_615_H_part25 : List Cell := [(10, 10), (10, 11), (10, 12), (11, -9), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (12, -9)]

def cache_615_H_part26 : List Cell := [(12, -8), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (13, -6), (13, -5), (13, -4), (13, -3), (13, -2), (13, -1)]

def cache_615_H_part27 : List Cell := [(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (14, -6), (14, -5), (14, -4), (14, -3), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (15, -2)]

def cache_615_H_part28 : List Cell := [(15, -1), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (16, -2), (16, 0), (16, 1), (16, 2), (17, 0), (17, 2)]

def cache_615_H : List Cell := ((((cache_615_H_part0 ++ (cache_615_H_part1 ++ cache_615_H_part2)) ++ ((cache_615_H_part3 ++ cache_615_H_part4) ++ (cache_615_H_part5 ++ cache_615_H_part6))) ++ ((cache_615_H_part7 ++ (cache_615_H_part8 ++ cache_615_H_part9)) ++ ((cache_615_H_part10 ++ cache_615_H_part11) ++ (cache_615_H_part12 ++ cache_615_H_part13)))) ++ (((cache_615_H_part14 ++ (cache_615_H_part15 ++ cache_615_H_part16)) ++ ((cache_615_H_part17 ++ cache_615_H_part18) ++ (cache_615_H_part19 ++ cache_615_H_part20))) ++ (((cache_615_H_part21 ++ cache_615_H_part22) ++ (cache_615_H_part23 ++ cache_615_H_part24)) ++ ((cache_615_H_part25 ++ cache_615_H_part26) ++ (cache_615_H_part27 ++ cache_615_H_part28)))))

def cache_615 : ListRow := ⟨cache_615_A, cache_615_H, 34⟩

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Cache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

def cacheChunk_0 : Array ListRow := #[cache_0, cache_1, cache_2, cache_3, cache_4, cache_5, cache_6, cache_7, cache_8, cache_9, cache_10, cache_11, cache_12, cache_13, cache_14, cache_15, cache_16, cache_17, cache_18, cache_19]

def cacheChunk_1 : Array ListRow := #[cache_20, cache_21, cache_22, cache_23, cache_24, cache_25, cache_26, cache_27, cache_28, cache_29, cache_30, cache_31, cache_32, cache_33, cache_34, cache_35, cache_36, cache_37, cache_38, cache_39]

def cacheChunk_2 : Array ListRow := #[cache_40, cache_41, cache_42, cache_43, cache_44, cache_45, cache_46, cache_47, cache_48, cache_49, cache_50, cache_51, cache_52, cache_53, cache_54, cache_55, cache_56, cache_57, cache_58, cache_59]

def cacheChunk_3 : Array ListRow := #[cache_60, cache_61, cache_62, cache_63, cache_64, cache_65, cache_66, cache_67, cache_68, cache_69, cache_70, cache_71, cache_72, cache_73, cache_74, cache_75, cache_76, cache_77, cache_78, cache_79]

def cacheChunk_4 : Array ListRow := #[cache_80, cache_81, cache_82, cache_83, cache_84, cache_85, cache_86, cache_87, cache_88, cache_89, cache_90, cache_91, cache_92, cache_93, cache_94, cache_95, cache_96, cache_97, cache_98, cache_99]

def cacheChunk_5 : Array ListRow := #[cache_100, cache_101, cache_102, cache_103, cache_104, cache_105, cache_106, cache_107, cache_108, cache_109, cache_110, cache_111, cache_112, cache_113, cache_114, cache_115, cache_116, cache_117, cache_118, cache_119]

def cacheChunk_6 : Array ListRow := #[cache_120, cache_121, cache_122, cache_123, cache_124, cache_125, cache_126, cache_127, cache_128, cache_129, cache_130, cache_131, cache_132, cache_133, cache_134, cache_135, cache_136, cache_137, cache_138, cache_139]

def cacheChunk_7 : Array ListRow := #[cache_140, cache_141, cache_142, cache_143, cache_144, cache_145, cache_146, cache_147, cache_148, cache_149, cache_150, cache_151, cache_152, cache_153, cache_154, cache_155, cache_156, cache_157, cache_158, cache_159]

def cacheChunk_8 : Array ListRow := #[cache_160, cache_161, cache_162, cache_163, cache_164, cache_165, cache_166, cache_167, cache_168, cache_169, cache_170, cache_171, cache_172, cache_173, cache_174, cache_175, cache_176, cache_177, cache_178, cache_179]

def cacheChunk_9 : Array ListRow := #[cache_180, cache_181, cache_182, cache_183, cache_184, cache_185, cache_186, cache_187, cache_188, cache_189, cache_190, cache_191, cache_192, cache_193, cache_194, cache_195, cache_196, cache_197, cache_198, cache_199]

def cacheChunk_10 : Array ListRow := #[cache_200, cache_201, cache_202, cache_203, cache_204, cache_205, cache_206, cache_207, cache_208, cache_209, cache_210, cache_211, cache_212, cache_213, cache_214, cache_215, cache_216, cache_217, cache_218, cache_219]

def cacheChunk_11 : Array ListRow := #[cache_220, cache_221, cache_222, cache_223, cache_224, cache_225, cache_226, cache_227, cache_228, cache_229, cache_230, cache_231, cache_232, cache_233, cache_234, cache_235, cache_236, cache_237, cache_238, cache_239]

def cacheChunk_12 : Array ListRow := #[cache_240, cache_241, cache_242, cache_243, cache_244, cache_245, cache_246, cache_247, cache_248, cache_249, cache_250, cache_251, cache_252, cache_253, cache_254, cache_255, cache_256, cache_257, cache_258, cache_259]

def cacheChunk_13 : Array ListRow := #[cache_260, cache_261, cache_262, cache_263, cache_264, cache_265, cache_266, cache_267, cache_268, cache_269, cache_270, cache_271, cache_272, cache_273, cache_274, cache_275, cache_276, cache_277, cache_278, cache_279]

def cacheChunk_14 : Array ListRow := #[cache_280, cache_281, cache_282, cache_283, cache_284, cache_285, cache_286, cache_287, cache_288, cache_289, cache_290, cache_291, cache_292, cache_293, cache_294, cache_295, cache_296, cache_297, cache_298, cache_299]

def cacheChunk_15 : Array ListRow := #[cache_300, cache_301, cache_302, cache_303, cache_304, cache_305, cache_306, cache_307, cache_308, cache_309, cache_310, cache_311, cache_312, cache_313, cache_314, cache_315, cache_316, cache_317, cache_318, cache_319]

def cacheChunk_16 : Array ListRow := #[cache_320, cache_321, cache_322, cache_323, cache_324, cache_325, cache_326, cache_327, cache_328, cache_329, cache_330, cache_331, cache_332, cache_333, cache_334, cache_335, cache_336, cache_337, cache_338, cache_339]

def cacheChunk_17 : Array ListRow := #[cache_340, cache_341, cache_342, cache_343, cache_344, cache_345, cache_346, cache_347, cache_348, cache_349, cache_350, cache_351, cache_352, cache_353, cache_354, cache_355, cache_356, cache_357, cache_358, cache_359]

def cacheChunk_18 : Array ListRow := #[cache_360, cache_361, cache_362, cache_363, cache_364, cache_365, cache_366, cache_367, cache_368, cache_369, cache_370, cache_371, cache_372, cache_373, cache_374, cache_375, cache_376, cache_377, cache_378, cache_379]

def cacheChunk_19 : Array ListRow := #[cache_380, cache_381, cache_382, cache_383, cache_384, cache_385, cache_386, cache_387, cache_388, cache_389, cache_390, cache_391, cache_392, cache_393, cache_394, cache_395, cache_396, cache_397, cache_398, cache_399]

def cacheChunk_20 : Array ListRow := #[cache_400, cache_401, cache_402, cache_403, cache_404, cache_405, cache_406, cache_407, cache_408, cache_409, cache_410, cache_411, cache_412, cache_413, cache_414, cache_415, cache_416, cache_417, cache_418, cache_419]

def cacheChunk_21 : Array ListRow := #[cache_420, cache_421, cache_422, cache_423, cache_424, cache_425, cache_426, cache_427, cache_428, cache_429, cache_430, cache_431, cache_432, cache_433, cache_434, cache_435, cache_436, cache_437, cache_438, cache_439]

def cacheChunk_22 : Array ListRow := #[cache_440, cache_441, cache_442, cache_443, cache_444, cache_445, cache_446, cache_447, cache_448, cache_449, cache_450, cache_451, cache_452, cache_453, cache_454, cache_455, cache_456, cache_457, cache_458, cache_459]

def cacheChunk_23 : Array ListRow := #[cache_460, cache_461, cache_462, cache_463, cache_464, cache_465, cache_466, cache_467, cache_468, cache_469, cache_470, cache_471, cache_472, cache_473, cache_474, cache_475, cache_476, cache_477, cache_478, cache_479]

def cacheChunk_24 : Array ListRow := #[cache_480, cache_481, cache_482, cache_483, cache_484, cache_485, cache_486, cache_487, cache_488, cache_489, cache_490, cache_491, cache_492, cache_493, cache_494, cache_495, cache_496, cache_497, cache_498, cache_499]

def cacheChunk_25 : Array ListRow := #[cache_500, cache_501, cache_502, cache_503, cache_504, cache_505, cache_506, cache_507, cache_508, cache_509, cache_510, cache_511, cache_512, cache_513, cache_514, cache_515, cache_516, cache_517, cache_518, cache_519]

def cacheChunk_26 : Array ListRow := #[cache_520, cache_521, cache_522, cache_523, cache_524, cache_525, cache_526, cache_527, cache_528, cache_529, cache_530, cache_531, cache_532, cache_533, cache_534, cache_535, cache_536, cache_537, cache_538, cache_539]

def cacheChunk_27 : Array ListRow := #[cache_540, cache_541, cache_542, cache_543, cache_544, cache_545, cache_546, cache_547, cache_548, cache_549, cache_550, cache_551, cache_552, cache_553, cache_554, cache_555, cache_556, cache_557, cache_558, cache_559]

def cacheChunk_28 : Array ListRow := #[cache_560, cache_561, cache_562, cache_563, cache_564, cache_565, cache_566, cache_567, cache_568, cache_569, cache_570, cache_571, cache_572, cache_573, cache_574, cache_575, cache_576, cache_577, cache_578, cache_579]

def cacheChunk_29 : Array ListRow := #[cache_580, cache_581, cache_582, cache_583, cache_584, cache_585, cache_586, cache_587, cache_588, cache_589, cache_590, cache_591, cache_592, cache_593, cache_594, cache_595, cache_596, cache_597, cache_598, cache_599]

def cacheChunk_30 : Array ListRow := #[cache_600, cache_601, cache_602, cache_603, cache_604, cache_605, cache_606, cache_607, cache_608, cache_609, cache_610, cache_611, cache_612, cache_613, cache_614, cache_615]

def cacheChunks : Array (Array ListRow) := #[cacheChunk_0, cacheChunk_1, cacheChunk_2, cacheChunk_3, cacheChunk_4, cacheChunk_5, cacheChunk_6, cacheChunk_7, cacheChunk_8, cacheChunk_9, cacheChunk_10, cacheChunk_11, cacheChunk_12, cacheChunk_13, cacheChunk_14, cacheChunk_15, cacheChunk_16, cacheChunk_17, cacheChunk_18, cacheChunk_19, cacheChunk_20, cacheChunk_21, cacheChunk_22, cacheChunk_23, cacheChunk_24, cacheChunk_25, cacheChunk_26, cacheChunk_27, cacheChunk_28, cacheChunk_29, cacheChunk_30]

def emptyListRow : ListRow := ⟨[], [], 0⟩

def cached (i : ℕ) : ListRow :=
  ((cacheChunks[i / 20]?.getD #[])[i % 20]?).getD emptyListRow

def CacheEquation (i : ℕ) : Prop :=
  if h : i < 6 then baseRow ⟨i, h⟩ = denote (cached i) else
    forkRow ((entryAt i).terms.map fun t => placeRow t (denote (cached t.child))) =
      denote (cached i)

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Invariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

def RowSubset (d : RowData) : Prop := d.A ⊆ d.H

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_TableList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

def tableListChunk_0 : List Entry := [entry_6, entry_7, entry_8, entry_9, entry_10, entry_11, entry_12, entry_13, entry_14, entry_15, entry_16, entry_17, entry_18, entry_19, entry_20, entry_21, entry_22, entry_23, entry_24, entry_25]

def tableListChunk_1 : List Entry := [entry_26, entry_27, entry_28, entry_29, entry_30, entry_31, entry_32, entry_33, entry_34, entry_35, entry_36, entry_37, entry_38, entry_39, entry_40, entry_41, entry_42, entry_43, entry_44, entry_45]

def tableListChunk_2 : List Entry := [entry_46, entry_47, entry_48, entry_49, entry_50, entry_51, entry_52, entry_53, entry_54, entry_55, entry_56, entry_57, entry_58, entry_59, entry_60, entry_61, entry_62, entry_63, entry_64, entry_65]

def tableListChunk_3 : List Entry := [entry_66, entry_67, entry_68, entry_69, entry_70, entry_71, entry_72, entry_73, entry_74, entry_75, entry_76, entry_77, entry_78, entry_79, entry_80, entry_81, entry_82, entry_83, entry_84, entry_85]

def tableListChunk_4 : List Entry := [entry_86, entry_87, entry_88, entry_89, entry_90, entry_91, entry_92, entry_93, entry_94, entry_95, entry_96, entry_97, entry_98, entry_99, entry_100, entry_101, entry_102, entry_103, entry_104, entry_105]

def tableListChunk_5 : List Entry := [entry_106, entry_107, entry_108, entry_109, entry_110, entry_111, entry_112, entry_113, entry_114, entry_115, entry_116, entry_117, entry_118, entry_119, entry_120, entry_121, entry_122, entry_123, entry_124, entry_125]

def tableListChunk_6 : List Entry := [entry_126, entry_127, entry_128, entry_129, entry_130, entry_131, entry_132, entry_133, entry_134, entry_135, entry_136, entry_137, entry_138, entry_139, entry_140, entry_141, entry_142, entry_143, entry_144, entry_145]

def tableListChunk_7 : List Entry := [entry_146, entry_147, entry_148, entry_149, entry_150, entry_151, entry_152, entry_153, entry_154, entry_155, entry_156, entry_157, entry_158, entry_159, entry_160, entry_161, entry_162, entry_163, entry_164, entry_165]

def tableListChunk_8 : List Entry := [entry_166, entry_167, entry_168, entry_169, entry_170, entry_171, entry_172, entry_173, entry_174, entry_175, entry_176, entry_177, entry_178, entry_179, entry_180, entry_181, entry_182, entry_183, entry_184, entry_185]

def tableListChunk_9 : List Entry := [entry_186, entry_187, entry_188, entry_189, entry_190, entry_191, entry_192, entry_193, entry_194, entry_195, entry_196, entry_197, entry_198, entry_199, entry_200, entry_201, entry_202, entry_203, entry_204, entry_205]

def tableListChunk_10 : List Entry := [entry_206, entry_207, entry_208, entry_209, entry_210, entry_211, entry_212, entry_213, entry_214, entry_215, entry_216, entry_217, entry_218, entry_219, entry_220, entry_221, entry_222, entry_223, entry_224, entry_225]

def tableListChunk_11 : List Entry := [entry_226, entry_227, entry_228, entry_229, entry_230, entry_231, entry_232, entry_233, entry_234, entry_235, entry_236, entry_237, entry_238, entry_239, entry_240, entry_241, entry_242, entry_243, entry_244, entry_245]

def tableListChunk_12 : List Entry := [entry_246, entry_247, entry_248, entry_249, entry_250, entry_251, entry_252, entry_253, entry_254, entry_255, entry_256, entry_257, entry_258, entry_259, entry_260, entry_261, entry_262, entry_263, entry_264, entry_265]

def tableListChunk_13 : List Entry := [entry_266, entry_267, entry_268, entry_269, entry_270, entry_271, entry_272, entry_273, entry_274, entry_275, entry_276, entry_277, entry_278, entry_279, entry_280, entry_281, entry_282, entry_283, entry_284, entry_285]

def tableListChunk_14 : List Entry := [entry_286, entry_287, entry_288, entry_289, entry_290, entry_291, entry_292, entry_293, entry_294, entry_295, entry_296, entry_297, entry_298, entry_299, entry_300, entry_301, entry_302, entry_303, entry_304, entry_305]

def tableListChunk_15 : List Entry := [entry_306, entry_307, entry_308, entry_309, entry_310, entry_311, entry_312, entry_313, entry_314, entry_315, entry_316, entry_317, entry_318, entry_319, entry_320, entry_321, entry_322, entry_323, entry_324, entry_325]

def tableListChunk_16 : List Entry := [entry_326, entry_327, entry_328, entry_329, entry_330, entry_331, entry_332, entry_333, entry_334, entry_335, entry_336, entry_337, entry_338, entry_339, entry_340, entry_341, entry_342, entry_343, entry_344, entry_345]

def tableListChunk_17 : List Entry := [entry_346, entry_347, entry_348, entry_349, entry_350, entry_351, entry_352, entry_353, entry_354, entry_355, entry_356, entry_357, entry_358, entry_359, entry_360, entry_361, entry_362, entry_363, entry_364, entry_365]

def tableListChunk_18 : List Entry := [entry_366, entry_367, entry_368, entry_369, entry_370, entry_371, entry_372, entry_373, entry_374, entry_375, entry_376, entry_377, entry_378, entry_379, entry_380, entry_381, entry_382, entry_383, entry_384, entry_385]

def tableListChunk_19 : List Entry := [entry_386, entry_387, entry_388, entry_389, entry_390, entry_391, entry_392, entry_393, entry_394, entry_395, entry_396, entry_397, entry_398, entry_399, entry_400, entry_401, entry_402, entry_403, entry_404, entry_405]

def tableListChunk_20 : List Entry := [entry_406, entry_407, entry_408, entry_409, entry_410, entry_411, entry_412, entry_413, entry_414, entry_415, entry_416, entry_417, entry_418, entry_419, entry_420, entry_421, entry_422, entry_423, entry_424, entry_425]

def tableListChunk_21 : List Entry := [entry_426, entry_427, entry_428, entry_429, entry_430, entry_431, entry_432, entry_433, entry_434, entry_435, entry_436, entry_437, entry_438, entry_439, entry_440, entry_441, entry_442, entry_443, entry_444, entry_445]

def tableListChunk_22 : List Entry := [entry_446, entry_447, entry_448, entry_449, entry_450, entry_451, entry_452, entry_453, entry_454, entry_455, entry_456, entry_457, entry_458, entry_459, entry_460, entry_461, entry_462, entry_463, entry_464, entry_465]

def tableListChunk_23 : List Entry := [entry_466, entry_467, entry_468, entry_469, entry_470, entry_471, entry_472, entry_473, entry_474, entry_475, entry_476, entry_477, entry_478, entry_479, entry_480, entry_481, entry_482, entry_483, entry_484, entry_485]

def tableListChunk_24 : List Entry := [entry_486, entry_487, entry_488, entry_489, entry_490, entry_491, entry_492, entry_493, entry_494, entry_495, entry_496, entry_497, entry_498, entry_499, entry_500, entry_501, entry_502, entry_503, entry_504, entry_505]

def tableListChunk_25 : List Entry := [entry_506, entry_507, entry_508, entry_509, entry_510, entry_511, entry_512, entry_513, entry_514, entry_515, entry_516, entry_517, entry_518, entry_519, entry_520, entry_521, entry_522, entry_523, entry_524, entry_525]

def tableListChunk_26 : List Entry := [entry_526, entry_527, entry_528, entry_529, entry_530, entry_531, entry_532, entry_533, entry_534, entry_535, entry_536, entry_537, entry_538, entry_539, entry_540, entry_541, entry_542, entry_543, entry_544, entry_545]

def tableListChunk_27 : List Entry := [entry_546, entry_547, entry_548, entry_549, entry_550, entry_551, entry_552, entry_553, entry_554, entry_555, entry_556, entry_557, entry_558, entry_559, entry_560, entry_561, entry_562, entry_563, entry_564, entry_565]

def tableListChunk_28 : List Entry := [entry_566, entry_567, entry_568, entry_569, entry_570, entry_571, entry_572, entry_573, entry_574, entry_575, entry_576, entry_577, entry_578, entry_579, entry_580, entry_581, entry_582, entry_583, entry_584, entry_585]

def tableListChunk_29 : List Entry := [entry_586, entry_587, entry_588, entry_589, entry_590, entry_591, entry_592, entry_593, entry_594, entry_595, entry_596, entry_597, entry_598, entry_599, entry_600, entry_601, entry_602, entry_603, entry_604, entry_605]

def tableListChunk_30 : List Entry := [entry_606, entry_607, entry_608, entry_609, entry_610, entry_611, entry_612, entry_613, entry_614, entry_615]

def tableList : List Entry := ((((tableListChunk_0 ++ (tableListChunk_1 ++ tableListChunk_2)) ++ ((tableListChunk_3 ++ tableListChunk_4) ++ (tableListChunk_5 ++ tableListChunk_6))) ++ (((tableListChunk_7 ++ tableListChunk_8) ++ (tableListChunk_9 ++ tableListChunk_10)) ++ ((tableListChunk_11 ++ tableListChunk_12) ++ (tableListChunk_13 ++ tableListChunk_14)))) ++ ((((tableListChunk_15 ++ tableListChunk_16) ++ (tableListChunk_17 ++ tableListChunk_18)) ++ ((tableListChunk_19 ++ tableListChunk_20) ++ (tableListChunk_21 ++ tableListChunk_22))) ++ (((tableListChunk_23 ++ tableListChunk_24) ++ (tableListChunk_25 ++ tableListChunk_26)) ++ ((tableListChunk_27 ++ tableListChunk_28) ++ (tableListChunk_29 ++ tableListChunk_30)))))

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_TableValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

abbrev TableEntryOk (k : ℕ) : Prop :=
  let e := table[k]?.getD emptyEntry
  e.index = k + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < e.index

end SnakyCertificate

end OAI
end


