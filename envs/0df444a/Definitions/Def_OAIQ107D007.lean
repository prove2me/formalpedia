-- Prove2me | Definitions.Def_OAIQ107D007
-- name    : OAIQ107D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:39:27.714107+00:00
-- url     : https://prove2.me/theorems/7a9b9df9-3b57-40ba-b522-87842c7f939d
-- title:
--   Definitions bundle OAIQ107D007 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 757 declarations of OpenAI's Lean: 737 definitions, 9 instances and 11 theorems. The definitions and types are `OAI.CycleClique.certificate_816_edges`, `OAI.CycleClique.certificate_817_edges`, `OAI.CycleClique.certificate_817_q`, `OAI.CycleClique.certificate_818_edges`, `OAI.CycleClique.certificate_818_q`, `OAI.CycleClique.certificate_819_edges`, `OAI.CycleClique.certificate_819_q`, `OAI.CycleClique.certificate_81_edges`, `OAI.CycleClique.certificate_81_q`, `OAI.CycleClique.certificate_820_edges`, `OAI.CycleClique.certificate_820_q`, `OAI.CycleClique.certificate_821_edges`, `OAI.CycleClique.certificate_821_q`, `OAI.CycleClique.certificate_822_edges`, `OAI.CycleClique.certificate_822_q`, `OAI.CycleClique.certificate_823_edges`, `OAI.CycleClique.certificate_823_q`, `OAI.CycleClique.certificate_824_edges`, `OAI.CycleClique.certificate_824_q`, `OAI.CycleClique.certificate_825_edges`, `OAI.CycleClique.certificate_825_q`, `OAI.CycleClique.certificate_826_edges`, `OAI.CycleClique.certificate_826_q`, `OAI.CycleClique.certificate_827_edges`, `OAI.CycleClique.certificate_827_q`, `OAI.CycleClique.certificate_828_edges`, `OAI.CycleClique.certificate_828_q`, `OAI.CycleClique.certificate_829_edges`, `OAI.CycleClique.certificate_829_q`, `OAI.CycleClique.certificate_82_edges`, `OAI.CycleClique.certificate_82_q`, `OAI.CycleClique.certificate_830_edges`, `OAI.CycleClique.certificate_830_q`, `OAI.CycleClique.certificate_831_edges`, `OAI.CycleClique.certificate_831_q`, `OAI.CycleClique.certificate_832_edges`, `OAI.CycleClique.certificate_832_q`, `OAI.CycleClique.certificate_833_edges`, `OAI.CycleClique.certificate_833_q`, `OAI.CycleClique.certificate_834_edges` and 697 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_CachedDecisions`, `Ramsey_CycleClique_CertificateDecisions`, `Ramsey_CycleClique_CertificateModel`, `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates003`, `Ramsey_CycleClique_Certificates004`, `Ramsey_CycleClique_Certificates026`, `Ramsey_CycleClique_Certificates027`, `Ramsey_CycleClique_Certificates028`, `Ramsey_CycleClique_Certificates029`, `Ramsey_CycleClique_Certificates030`, `Ramsey_CycleClique_Certificates031`, `Ramsey_CycleClique_Certificates032`, `Ramsey_CycleClique_ColouredPaths`, `Ramsey_CycleClique_CycleShortening`, `Ramsey_CycleClique_DistanceLayers`, `Ramsey_CycleClique_LabelDecisions`, `Ramsey_CycleClique_LowerBound`, `Ramsey_CycleClique_MarkedChains`, `Ramsey_CycleClique_Patterns10x5`, `Ramsey_CycleClique_Patterns10x6`, `Ramsey_CycleClique_Patterns10x7`, `Ramsey_CycleClique_Patterns10x8`, `Ramsey_CycleClique_Patterns11x5`, `Ramsey_CycleClique_Patterns11x6`, `Ramsey_CycleClique_Patterns11x7`, `Ramsey_CycleClique_Patterns11x8`, `Ramsey_CycleClique_Patterns12x6`, `Ramsey_CycleClique_Patterns12x7`, `Ramsey_CycleClique_Patterns12x8`, `Ramsey_CycleClique_Patterns13x6`, `Ramsey_CycleClique_Patterns13x7`, `Ramsey_CycleClique_Patterns13x8`, `Ramsey_CycleClique_Patterns14x7`, `Ramsey_CycleClique_Patterns14x8`, `Ramsey_CycleClique_Patterns15x7`, `Ramsey_CycleClique_Patterns15x8`, `Ramsey_CycleClique_Patterns16x8`, `Ramsey_CycleClique_Patterns17x8`, `Ramsey_CycleClique_Patterns5x3`, `Ramsey_CycleClique_Patterns5x4`, `Ramsey_CycleClique_Patterns5x5`, `Ramsey_CycleClique_Patterns6x3`, `Ramsey_CycleClique_Patterns6x4`, `Ramsey_CycleClique_Patterns6x5`, `Ramsey_CycleClique_Patterns6x6`, `Ramsey_CycleClique_Patterns7x3`, `Ramsey_CycleClique_Patterns7x4`, `Ramsey_CycleClique_Patterns7x5`, `Ramsey_CycleClique_Patterns7x6`, `Ramsey_CycleClique_Patterns7x7`, `Ramsey_CycleClique_Patterns8x4`, `Ramsey_CycleClique_Patterns8x5`, `Ramsey_CycleClique_Patterns8x6`, `Ramsey_CycleClique_Patterns8x7`, `Ramsey_CycleClique_Patterns8x8`, `Ramsey_CycleClique_Patterns9x4`, `Ramsey_CycleClique_Patterns9x5`, `Ramsey_CycleClique_Patterns9x6`, `Ramsey_CycleClique_Patterns9x7`, `Ramsey_CycleClique_Patterns9x8`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D058`, `OAIQ107D113`, `OAIQ107D114`, `OAIQ107D117`, `OAIQ107D120`, `OAIQ107D121`, `OAIQ107D122`, `OAIQ107D124` and `OAIQ107D125`; the statements `OAI.CycleClique.finite_patterns_10_5`, `OAI.CycleClique.finite_patterns_11_5`, `OAI.CycleClique.finite_patterns_11_6`, `OAI.CycleClique.finite_patterns_12_6`, `OAI.CycleClique.finite_patterns_13_6`, `OAI.CycleClique.finite_patterns_13_7`, `OAI.CycleClique.finite_patterns_14_7`, `OAI.CycleClique.finite_patterns_14_8`, `OAI.CycleClique.finite_patterns_15_7`, `OAI.CycleClique.finite_patterns_15_8`, `OAI.CycleClique.finite_patterns_16_8`, `OAI.CycleClique.finite_patterns_17_8`, `OAI.CycleClique.finite_patterns_9_4`, `OAI.CycleClique.finite_range_verified`, `OAI.CycleClique.patterns_13_6_0_verified`, `OAI.CycleClique.patterns_15_7_0_verified`, `OAI.CycleClique.patterns_15_7_13_verified`, `OAI.CycleClique.patterns_15_7_1_verified`, `OAI.CycleClique.patterns_15_7_4_verified`, `OAI.CycleClique.patterns_16_8_7_verified`, `OAI.CycleClique.patterns_16_8_8_verified`, `OAI.CycleClique.patterns_17_8_0_verified`, `OAI.CycleClique.patterns_17_8_11_verified`, `OAI.CycleClique.patterns_17_8_12_verified`, `OAI.CycleClique.patterns_17_8_15_verified`, `OAI.CycleClique.patterns_17_8_16_verified`, `OAI.CycleClique.patterns_17_8_17_verified`, `OAI.CycleClique.patterns_17_8_1_verified`, `OAI.CycleClique.patterns_17_8_23_verified`, `OAI.CycleClique.patterns_17_8_24_verified`, `OAI.CycleClique.patterns_17_8_25_verified`, `OAI.CycleClique.patterns_17_8_26_verified`, `OAI.CycleClique.patterns_17_8_32_verified`, `OAI.CycleClique.patterns_17_8_35_verified`, `OAI.CycleClique.patterns_17_8_36_verified`, `OAI.CycleClique.patterns_17_8_39_verified`, `OAI.CycleClique.patterns_17_8_40_verified`, `OAI.CycleClique.patterns_17_8_41_verified`, `OAI.CycleClique.patterns_17_8_42_verified`, `OAI.CycleClique.patterns_17_8_51_verified`, `OAI.CycleClique.patterns_17_8_52_verified`, `OAI.CycleClique.patterns_17_8_53_verified` and `OAI.CycleClique.patterns_17_8_6_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ107_CC.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ColouredPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def pathEnds {V : Type*} (G : SimpleGraph V) (x : V) (W : List V) : Set V :=
  {v | ∃ p : G.Walk x v, p.IsPath ∧ p.support.Perm W}



def within {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩


def walkWithin {V : Type*} {G : SimpleGraph V} {S : Set V} {x v : V}
    (p : G.Walk x v) (hS : ∀ w ∈ p.support, w ∈ S) : (within G S).Walk x v :=
  match p with
  | .nil => .nil
  | .cons h p => .cons ⟨h, hS _ (by simp), hS _ (by simp)⟩
    (walkWithin p (fun w hw => hS w (by simp [hw])))

@[simp] theorem walkWithin_support {V : Type*} {G : SimpleGraph V} {S : Set V} {x v : V}
    (p : G.Walk x v) (hS : ∀ w ∈ p.support, w ∈ S) : (walkWithin p hS).support = p.support := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    change a :: (walkWithin p _).support = a :: p.support
    rw [ih]


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_DistanceLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def distanceLayer {V : Type*} (G : SimpleGraph V) (r : V) (i : ℕ) : Set V :=
  {v | G.Reachable r v ∧ G.dist r v = i}

@[simp] theorem distanceLayer_zero {V : Type*} (G : SimpleGraph V) (r : V) :
    distanceLayer G r 0 = {r} := by
  ext v
  constructor
  · rintro ⟨hr, hd⟩
    exact (hr.dist_eq_zero_iff.mp hd).symm
  · rintro rfl
    exact ⟨.refl _, G.dist_self⟩


def parityIndices (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2)

 
def paritySum (α : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ parityIndices i, α j

@[simp] theorem paritySum_zero (α : ℕ → ℕ) : paritySum α 0 = α 0 := by
  simp [paritySum, parityIndices, Finset.sum_filter]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CycleShortening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def fourStepIndex {n : ℕ} (hn : 7 ≤ n) (i : Fin (n - 1)) : Fin n :=
  ⟨if i.val < n - 6 then i.val + 1 else
    if i.val < n - 4 then i.val + 4 else i.val - 1,
    by split_ifs <;> omega⟩



abbrev exteriorEdges {V : Type*} (G : SimpleGraph V) (X : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∉ X ∨ v ∉ X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_MarkedChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def prefixChains {V : Type*} (A : List V) : List (List V) :=
  if A = [] then [] else [A]

@[simp] theorem prefixChains_flatten {V : Type*} (A : List V) :
    (prefixChains A).flatten = A := by
  by_cases h : A = [] <;> simp [prefixChains, h]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CertificateModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph


def patternSize (D : List (List ℕ)) : ℕ := D.flatten.length + D.length


def chainChoices : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | l+1, B => [] :: (List.range B).flatMap (fun a =>
      (chainChoices l (B-(a+1))).map (fun A => (a+1)::A))



def patternChoices (t B : ℕ) (lower : List ℕ) : List (List (List ℕ)) :=
  if _ht : t = 0 then [[]] else
    (chainChoices (t-1) B).flatMap (fun A =>
      if A ≤ A.reverse ∧ lower ≤ A then
        (patternChoices (t-(A.length+1)) (B-A.sum) A).map (A::·)
      else [])
termination_by t
decreasing_by omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_LabelDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def globalEdgeBits : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a,b) :: E => 2^(Nat.pair a b) ||| globalEdgeBits E

theorem globalEdgeBits_spec (E : List (ℕ × ℕ)) (a b : ℕ) :
    (globalEdgeBits E).testBit (Nat.pair a b) = true ↔ (a,b) ∈ E := by
  induction E with
  | nil => simp [globalEdgeBits]
  | cons e E ih =>
    rcases e with ⟨i,j⟩
    simp only [globalEdgeBits, Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, Nat.pair_eq_pair, ih, List.mem_cons, Prod.mk.injEq]
    tauto

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CertificateDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def compactTriple (a b d : ℕ) : ℕ :=
  Nat.pair (Nat.pair (a / 32) (b / 32)) (d / 8) * 8192 +
    (a % 32) * 256 + (b % 32) * 8 + d % 8

theorem compactTriple_injective {a b d i j e : ℕ} :
    compactTriple a b d = compactTriple i j e ↔ a = i ∧ b = j ∧ d = e := by
  constructor
  · intro h
    unfold compactTriple at h
    have hbig : Nat.pair (Nat.pair (a / 32) (b / 32)) (d / 8) =
        Nat.pair (Nat.pair (i / 32) (j / 32)) (e / 8) := by omega
    obtain ⟨hp, hd⟩ := Nat.pair_eq_pair.mp hbig
    obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp hp
    omega
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CachedDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem qCacheEdgeBits_append (E F : List (ℕ × ℕ)) :
    globalEdgeBits (E ++ F) = globalEdgeBits E ||| globalEdgeBits F := by
  induction E with
  | nil => simp [globalEdgeBits]
  | cons ab E ih =>
    rcases ab with ⟨a,b⟩
    simp only [List.cons_append, globalEdgeBits, ih, Nat.lor_assoc]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_8_q : Finset ℕ := ([0,1,3] : List ℕ).toFinset
noncomputable def certificate_8_edges : List (ℕ × ℕ) := [(1,2),(2,3),(0,1),(0,3),(1,3)]

noncomputable def certificate_9_q : Finset ℕ := ([0,1,4] : List ℕ).toFinset

noncomputable def certificate_9_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(0,1),(0,4),(1,4)]

noncomputable def certificate_9_E : List (ℕ × ℕ) := certificate_9_edges

noncomputable def certificate_9_part_1_E : List (ℕ × ℕ) := certificate_9_E

noncomputable def certificate_9_part_2_E : List (ℕ × ℕ) := certificate_9_part_1_E

noncomputable def certificate_9_part_3_E : List (ℕ × ℕ) := certificate_9_part_2_E

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_81_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_81_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_82_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_82_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_83_q : Finset ℕ := ([0,1,2,5] : List ℕ).toFinset
noncomputable def certificate_83_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(0,1),(0,2),(0,5),(1,2),(1,5),(2,5)]

noncomputable def certificate_84_q : Finset ℕ := ([0,1,2,6] : List ℕ).toFinset
noncomputable def certificate_84_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,6),(1,2),(1,6),(2,6)]

noncomputable def certificate_85_q : Finset ℕ := ([0,1,2,7] : List ℕ).toFinset

noncomputable def certificate_85_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,7),(1,2),(1,7),(2,7)]

noncomputable def certificate_85_E : List (ℕ × ℕ) := certificate_85_edges

noncomputable def certificate_85_part_1_E : List (ℕ × ℕ) := certificate_85_E

noncomputable def certificate_85_part_2_E : List (ℕ × ℕ) := certificate_85_part_1_E

noncomputable def certificate_85_part_3_E : List (ℕ × ℕ) := certificate_85_part_2_E

noncomputable def certificate_85_part_5_E : List (ℕ × ℕ) := certificate_85_part_3_E

noncomputable def certificate_85_part_6_E : List (ℕ × ℕ) := certificate_85_part_5_E

noncomputable def certificate_85_part_7_E : List (ℕ × ℕ) := certificate_85_part_6_E

noncomputable def certificate_85_part_10_E : List (ℕ × ℕ) := certificate_85_part_7_E

noncomputable def certificate_85_part_13_E : List (ℕ × ℕ) := certificate_85_part_10_E

noncomputable def certificate_86_q : Finset ℕ := ([0,1,2,8] : List ℕ).toFinset

noncomputable def certificate_86_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,8),(1,2),(1,8),(2,8)]

noncomputable def certificate_86_E : List (ℕ × ℕ) := certificate_86_edges

noncomputable def certificate_86_part_1_E : List (ℕ × ℕ) := certificate_86_E

noncomputable def certificate_86_part_2_E : List (ℕ × ℕ) := certificate_86_part_1_E

noncomputable def certificate_86_part_7_E : List (ℕ × ℕ) := certificate_86_part_2_E

noncomputable def certificate_86_part_9_E : List (ℕ × ℕ) := certificate_86_part_7_E

noncomputable def certificate_86_part_14_E : List (ℕ × ℕ) := certificate_86_part_9_E

noncomputable def certificate_86_part_15_E : List (ℕ × ℕ) := certificate_86_part_14_E

noncomputable def certificate_86_part_22_E : List (ℕ × ℕ) := certificate_86_part_15_E

noncomputable def certificate_86_part_26_E : List (ℕ × ℕ) := certificate_86_part_22_E

noncomputable def certificate_86_part_29_E : List (ℕ × ℕ) := certificate_86_part_26_E

noncomputable def certificate_86_part_34_E : List (ℕ × ℕ) := certificate_86_part_29_E

noncomputable def certificate_86_part_38_E : List (ℕ × ℕ) := certificate_86_part_34_E

noncomputable def certificate_86_part_41_E : List (ℕ × ℕ) := certificate_86_part_38_E

noncomputable def certificate_86_part_44_E : List (ℕ × ℕ) := certificate_86_part_41_E

noncomputable def certificate_86_part_49_E : List (ℕ × ℕ) := certificate_86_part_44_E

noncomputable def certificate_87_q : Finset ℕ := ([0,1,3,5] : List ℕ).toFinset
noncomputable def certificate_87_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,3),(0,5),(1,3),(1,5),(3,5)]

noncomputable def certificate_88_q : Finset ℕ := ([0,1,3,6] : List ℕ).toFinset
noncomputable def certificate_88_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(0,1),(0,3),(0,6),(1,3),(1,6),(3,6)]

noncomputable def certificate_89_q : Finset ℕ := ([0,1,3,7] : List ℕ).toFinset
noncomputable def certificate_89_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,3),(0,7),(1,3),(1,7),(3,7)]

noncomputable def certificate_90_q : Finset ℕ := ([0,1,3,8] : List ℕ).toFinset

noncomputable def certificate_90_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,8),(1,3),(1,8),(3,8)]

noncomputable def certificate_90_E : List (ℕ × ℕ) := certificate_90_edges

noncomputable def certificate_90_part_1_E : List (ℕ × ℕ) := certificate_90_E

noncomputable def certificate_90_part_2_E : List (ℕ × ℕ) := certificate_90_part_1_E

noncomputable def certificate_90_part_3_E : List (ℕ × ℕ) := certificate_90_part_2_E

noncomputable def certificate_90_part_4_E : List (ℕ × ℕ) := certificate_90_part_3_E

noncomputable def certificate_90_part_9_E : List (ℕ × ℕ) := certificate_90_part_4_E

noncomputable def certificate_90_part_12_E : List (ℕ × ℕ) := certificate_90_part_9_E

noncomputable def certificate_90_part_16_E : List (ℕ × ℕ) := certificate_90_part_12_E

noncomputable def certificate_90_part_17_E : List (ℕ × ℕ) := certificate_90_part_16_E

noncomputable def certificate_90_part_20_E : List (ℕ × ℕ) := certificate_90_part_17_E

noncomputable def certificate_90_part_21_E : List (ℕ × ℕ) := certificate_90_part_20_E

noncomputable def certificate_90_part_25_E : List (ℕ × ℕ) := certificate_90_part_21_E

noncomputable def certificate_91_q : Finset ℕ := ([0,1,4,7] : List ℕ).toFinset
noncomputable def certificate_91_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,4),(0,7),(1,4),(1,7),(4,7)]

noncomputable def certificate_92_q : Finset ℕ := ([0,1,4,8] : List ℕ).toFinset
noncomputable def certificate_92_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,4),(0,8),(1,4),(1,8),(4,8)]

noncomputable def certificate_93_q : Finset ℕ := ([0,2,3,5] : List ℕ).toFinset
noncomputable def certificate_93_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(0,2),(0,3),(0,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_94_q : Finset ℕ := ([0,2,3,6] : List ℕ).toFinset
noncomputable def certificate_94_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(0,2),(0,3),(0,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_95_q : Finset ℕ := ([0,2,3,7] : List ℕ).toFinset
noncomputable def certificate_95_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(0,2),(0,3),(0,7),(2,3),(2,7),(3,7)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_96_q : Finset ℕ := ([0,2,3,8] : List ℕ).toFinset

noncomputable def certificate_96_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,3),(0,8),(2,3),(2,8),(3,8)]

noncomputable def certificate_96_E : List (ℕ × ℕ) := certificate_96_edges

noncomputable def certificate_96_part_1_E : List (ℕ × ℕ) := certificate_96_E

noncomputable def certificate_96_part_2_E : List (ℕ × ℕ) := certificate_96_part_1_E

noncomputable def certificate_96_part_3_E : List (ℕ × ℕ) := certificate_96_part_2_E

noncomputable def certificate_96_part_4_E : List (ℕ × ℕ) := certificate_96_part_3_E

noncomputable def certificate_96_part_6_E : List (ℕ × ℕ) := certificate_96_part_4_E

noncomputable def certificate_96_part_7_E : List (ℕ × ℕ) := certificate_96_part_6_E

noncomputable def certificate_96_part_10_E : List (ℕ × ℕ) := certificate_96_part_7_E

noncomputable def certificate_96_part_11_E : List (ℕ × ℕ) := certificate_96_part_10_E

noncomputable def certificate_96_part_12_E : List (ℕ × ℕ) := certificate_96_part_11_E

noncomputable def certificate_96_part_14_E : List (ℕ × ℕ) := certificate_96_part_12_E

noncomputable def certificate_96_part_15_E : List (ℕ × ℕ) := certificate_96_part_14_E

noncomputable def certificate_96_part_18_E : List (ℕ × ℕ) := certificate_96_part_15_E

noncomputable def certificate_96_part_20_E : List (ℕ × ℕ) := certificate_96_part_18_E

noncomputable def certificate_96_part_23_E : List (ℕ × ℕ) := certificate_96_part_20_E

noncomputable def certificate_97_q : Finset ℕ := ([0,2,4,6] : List ℕ).toFinset
noncomputable def certificate_97_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,2),(0,4),(0,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_98_q : Finset ℕ := ([0,2,4,7] : List ℕ).toFinset
noncomputable def certificate_98_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,2),(0,4),(0,7),(2,4),(2,7),(4,7)]

noncomputable def certificate_99_q : Finset ℕ := ([0,2,4,8] : List ℕ).toFinset
noncomputable def certificate_99_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,4),(0,8),(2,4),(2,8),(4,8)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates026
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_816_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_817_q : Finset ℕ := ([0,1,2,4,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_817_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,11),(1,2),(1,4),(1,5),(1,7),(1,8),(1,11),(2,4),(2,5),(2,7),(2,8),(2,11),(4,5),(4,7),(4,8),(4,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_818_q : Finset ℕ := ([0,1,2,4,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_818_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,12),(1,2),(1,4),(1,5),(1,7),(1,8),(1,12),(2,4),(2,5),(2,7),(2,8),(2,12),(4,5),(4,7),(4,8),(4,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_819_q : Finset ℕ := ([0,1,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_819_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(1,2),(1,4),(1,5),(1,7),(1,9),(1,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_820_q : Finset ℕ := ([0,1,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_820_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(1,2),(1,4),(1,5),(1,7),(1,9),(1,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_821_q : Finset ℕ := ([0,1,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_821_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(1,2),(1,4),(1,5),(1,7),(1,10),(1,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_822_q : Finset ℕ := ([0,1,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_822_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(1,2),(1,4),(1,5),(1,8),(1,9),(1,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_823_q : Finset ℕ := ([0,1,2,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_823_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(1,2),(1,4),(1,6),(1,7),(1,9),(1,11),(2,4),(2,6),(2,7),(2,9),(2,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_824_q : Finset ℕ := ([0,1,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_824_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(1,2),(1,4),(1,6),(1,7),(1,9),(1,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_825_q : Finset ℕ := ([0,1,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_825_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(1,2),(1,4),(1,6),(1,8),(1,9),(1,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_826_q : Finset ℕ := ([0,1,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_826_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(1,2),(1,4),(1,6),(1,8),(1,10),(1,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_827_q : Finset ℕ := ([0,1,3,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_827_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,11),(1,3),(1,4),(1,6),(1,7),(1,9),(1,11),(3,4),(3,6),(3,7),(3,9),(3,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_828_q : Finset ℕ := ([0,1,3,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_828_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,12),(1,3),(1,4),(1,6),(1,7),(1,9),(1,12),(3,4),(3,6),(3,7),(3,9),(3,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_829_q : Finset ℕ := ([0,1,3,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_829_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,12),(1,3),(1,4),(1,6),(1,8),(1,9),(1,12),(3,4),(3,6),(3,8),(3,9),(3,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_830_q : Finset ℕ := ([0,1,3,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_830_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,12),(1,3),(1,4),(1,6),(1,8),(1,10),(1,12),(3,4),(3,6),(3,8),(3,10),(3,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_831_q : Finset ℕ := ([0,1,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_831_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(1,3),(1,5),(1,6),(1,8),(1,10),(1,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates027
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_832_q : Finset ℕ := ([0,2,3,5,6,8,9,11] : List ℕ).toFinset
noncomputable def certificate_832_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,11),(2,3),(2,5),(2,6),(2,8),(2,9),(2,11),(3,5),(3,6),(3,8),(3,9),(3,11),(5,6),(5,8),(5,9),(5,11),(6,8),(6,9),(6,11),(8,9),(8,11),(9,11)]

noncomputable def certificate_833_q : Finset ℕ := ([0,2,3,5,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_833_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,12),(2,3),(2,5),(2,6),(2,8),(2,9),(2,12),(3,5),(3,6),(3,8),(3,9),(3,12),(5,6),(5,8),(5,9),(5,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_834_q : Finset ℕ := ([0,2,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_834_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(2,3),(2,5),(2,6),(2,8),(2,10),(2,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_835_q : Finset ℕ := ([0,2,3,5,7,8,10,12] : List ℕ).toFinset
noncomputable def certificate_835_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,12),(2,3),(2,5),(2,7),(2,8),(2,10),(2,12),(3,5),(3,7),(3,8),(3,10),(3,12),(5,7),(5,8),(5,10),(5,12),(7,8),(7,10),(7,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_836_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_836_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_837_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_837_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_838_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_838_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_839_q : Finset ℕ := ([0,1,2,3,4,5,9] : List ℕ).toFinset
noncomputable def certificate_839_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(1,2),(1,3),(1,4),(1,5),(1,9),(2,3),(2,4),(2,5),(2,9),(3,4),(3,5),(3,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_840_q : Finset ℕ := ([0,1,2,3,4,5,10] : List ℕ).toFinset
noncomputable def certificate_840_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(1,2),(1,3),(1,4),(1,5),(1,10),(2,3),(2,4),(2,5),(2,10),(3,4),(3,5),(3,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_841_q : Finset ℕ := ([0,1,2,3,4,5,11] : List ℕ).toFinset
noncomputable def certificate_841_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,11),(1,2),(1,3),(1,4),(1,5),(1,11),(2,3),(2,4),(2,5),(2,11),(3,4),(3,5),(3,11),(4,5),(4,11),(5,11)]

noncomputable def certificate_842_q : Finset ℕ := ([0,1,2,3,4,5,12] : List ℕ).toFinset
noncomputable def certificate_842_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,12),(1,2),(1,3),(1,4),(1,5),(1,12),(2,3),(2,4),(2,5),(2,12),(3,4),(3,5),(3,12),(4,5),(4,12),(5,12)]

noncomputable def certificate_843_q : Finset ℕ := ([0,1,2,3,4,5,13] : List ℕ).toFinset
noncomputable def certificate_843_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,13),(1,2),(1,3),(1,4),(1,5),(1,13),(2,3),(2,4),(2,5),(2,13),(3,4),(3,5),(3,13),(4,5),(4,13),(5,13)]

noncomputable def certificate_844_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_844_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_845_q : Finset ℕ := ([0,1,2,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_845_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(1,2),(1,3),(1,4),(1,6),(1,9),(2,3),(2,4),(2,6),(2,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_846_q : Finset ℕ := ([0,1,2,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_846_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(1,2),(1,3),(1,4),(1,6),(1,10),(2,3),(2,4),(2,6),(2,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_847_q : Finset ℕ := ([0,1,2,3,4,6,11] : List ℕ).toFinset
noncomputable def certificate_847_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(1,2),(1,3),(1,4),(1,6),(1,11),(2,3),(2,4),(2,6),(2,11),(3,4),(3,6),(3,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_848_q : Finset ℕ := ([0,1,2,3,4,6,12] : List ℕ).toFinset
noncomputable def certificate_848_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(1,2),(1,3),(1,4),(1,6),(1,12),(2,3),(2,4),(2,6),(2,12),(3,4),(3,6),(3,12),(4,6),(4,12),(6,12)]

noncomputable def certificate_849_q : Finset ℕ := ([0,1,2,3,4,6,13] : List ℕ).toFinset
noncomputable def certificate_849_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,13),(1,2),(1,3),(1,4),(1,6),(1,13),(2,3),(2,4),(2,6),(2,13),(3,4),(3,6),(3,13),(4,6),(4,13),(6,13)]

noncomputable def certificate_850_q : Finset ℕ := ([0,1,2,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_850_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(1,2),(1,3),(1,4),(1,7),(1,10),(2,3),(2,4),(2,7),(2,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_851_q : Finset ℕ := ([0,1,2,3,4,7,11] : List ℕ).toFinset
noncomputable def certificate_851_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(1,2),(1,3),(1,4),(1,7),(1,11),(2,3),(2,4),(2,7),(2,11),(3,4),(3,7),(3,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_852_q : Finset ℕ := ([0,1,2,3,4,7,12] : List ℕ).toFinset
noncomputable def certificate_852_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,12),(1,2),(1,3),(1,4),(1,7),(1,12),(2,3),(2,4),(2,7),(2,12),(3,4),(3,7),(3,12),(4,7),(4,12),(7,12)]

noncomputable def certificate_853_q : Finset ℕ := ([0,1,2,3,4,7,13] : List ℕ).toFinset
noncomputable def certificate_853_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,13),(1,2),(1,3),(1,4),(1,7),(1,13),(2,3),(2,4),(2,7),(2,13),(3,4),(3,7),(3,13),(4,7),(4,13),(7,13)]

noncomputable def certificate_854_q : Finset ℕ := ([0,1,2,3,4,8,12] : List ℕ).toFinset
noncomputable def certificate_854_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,8),(0,12),(1,2),(1,3),(1,4),(1,8),(1,12),(2,3),(2,4),(2,8),(2,12),(3,4),(3,8),(3,12),(4,8),(4,12),(8,12)]

noncomputable def certificate_855_q : Finset ℕ := ([0,1,2,3,4,8,13] : List ℕ).toFinset
noncomputable def certificate_855_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,8),(0,13),(1,2),(1,3),(1,4),(1,8),(1,13),(2,3),(2,4),(2,8),(2,13),(3,4),(3,8),(3,13),(4,8),(4,13),(8,13)]

noncomputable def certificate_856_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_856_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_857_q : Finset ℕ := ([0,1,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_857_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(1,2),(1,3),(1,5),(1,6),(1,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_858_q : Finset ℕ := ([0,1,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_858_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(1,2),(1,3),(1,5),(1,6),(1,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_859_q : Finset ℕ := ([0,1,2,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_859_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,11),(1,2),(1,3),(1,5),(1,6),(1,11),(2,3),(2,5),(2,6),(2,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_860_q : Finset ℕ := ([0,1,2,3,5,6,12] : List ℕ).toFinset
noncomputable def certificate_860_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,12),(1,2),(1,3),(1,5),(1,6),(1,12),(2,3),(2,5),(2,6),(2,12),(3,5),(3,6),(3,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_861_q : Finset ℕ := ([0,1,2,3,5,6,13] : List ℕ).toFinset
noncomputable def certificate_861_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,13),(1,2),(1,3),(1,5),(1,6),(1,13),(2,3),(2,5),(2,6),(2,13),(3,5),(3,6),(3,13),(5,6),(5,13),(6,13)]

noncomputable def certificate_862_q : Finset ℕ := ([0,1,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_862_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(1,2),(1,3),(1,5),(1,7),(1,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_863_q : Finset ℕ := ([0,1,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_863_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(1,2),(1,3),(1,5),(1,7),(1,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates028
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_864_q : Finset ℕ := ([0,1,2,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_864_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(1,2),(1,3),(1,5),(1,7),(1,11),(2,3),(2,5),(2,7),(2,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_865_q : Finset ℕ := ([0,1,2,3,5,7,12] : List ℕ).toFinset
noncomputable def certificate_865_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(1,2),(1,3),(1,5),(1,7),(1,12),(2,3),(2,5),(2,7),(2,12),(3,5),(3,7),(3,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_866_q : Finset ℕ := ([0,1,2,3,5,7,13] : List ℕ).toFinset
noncomputable def certificate_866_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,13),(1,2),(1,3),(1,5),(1,7),(1,13),(2,3),(2,5),(2,7),(2,13),(3,5),(3,7),(3,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_867_q : Finset ℕ := ([0,1,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_867_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(1,2),(1,3),(1,5),(1,8),(1,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_868_q : Finset ℕ := ([0,1,2,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_868_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(1,2),(1,3),(1,5),(1,8),(1,11),(2,3),(2,5),(2,8),(2,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_869_q : Finset ℕ := ([0,1,2,3,5,8,12] : List ℕ).toFinset
noncomputable def certificate_869_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(1,2),(1,3),(1,5),(1,8),(1,12),(2,3),(2,5),(2,8),(2,12),(3,5),(3,8),(3,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_870_q : Finset ℕ := ([0,1,2,3,5,8,13] : List ℕ).toFinset
noncomputable def certificate_870_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,13),(1,2),(1,3),(1,5),(1,8),(1,13),(2,3),(2,5),(2,8),(2,13),(3,5),(3,8),(3,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_871_q : Finset ℕ := ([0,1,2,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_871_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(1,2),(1,3),(1,5),(1,9),(1,11),(2,3),(2,5),(2,9),(2,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_872_q : Finset ℕ := ([0,1,2,3,5,9,12] : List ℕ).toFinset
noncomputable def certificate_872_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,9),(0,12),(1,2),(1,3),(1,5),(1,9),(1,12),(2,3),(2,5),(2,9),(2,12),(3,5),(3,9),(3,12),(5,9),(5,12),(9,12)]

noncomputable def certificate_873_q : Finset ℕ := ([0,1,2,3,5,9,13] : List ℕ).toFinset
noncomputable def certificate_873_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,9),(0,13),(1,2),(1,3),(1,5),(1,9),(1,13),(2,3),(2,5),(2,9),(2,13),(3,5),(3,9),(3,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_874_q : Finset ℕ := ([0,1,2,3,5,10,12] : List ℕ).toFinset
noncomputable def certificate_874_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,10),(0,12),(1,2),(1,3),(1,5),(1,10),(1,12),(2,3),(2,5),(2,10),(2,12),(3,5),(3,10),(3,12),(5,10),(5,12),(10,12)]

noncomputable def certificate_875_q : Finset ℕ := ([0,1,2,3,5,10,13] : List ℕ).toFinset
noncomputable def certificate_875_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,10),(0,13),(1,2),(1,3),(1,5),(1,10),(1,13),(2,3),(2,5),(2,10),(2,13),(3,5),(3,10),(3,13),(5,10),(5,13),(10,13)]

noncomputable def certificate_876_q : Finset ℕ := ([0,1,2,3,5,11,13] : List ℕ).toFinset
noncomputable def certificate_876_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,11),(0,13),(1,2),(1,3),(1,5),(1,11),(1,13),(2,3),(2,5),(2,11),(2,13),(3,5),(3,11),(3,13),(5,11),(5,13),(11,13)]

noncomputable def certificate_877_q : Finset ℕ := ([0,1,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_877_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(1,2),(1,3),(1,6),(1,7),(1,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_878_q : Finset ℕ := ([0,1,2,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_878_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(1,2),(1,3),(1,6),(1,7),(1,11),(2,3),(2,6),(2,7),(2,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_879_q : Finset ℕ := ([0,1,2,3,6,7,12] : List ℕ).toFinset
noncomputable def certificate_879_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,7),(0,12),(1,2),(1,3),(1,6),(1,7),(1,12),(2,3),(2,6),(2,7),(2,12),(3,6),(3,7),(3,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_880_q : Finset ℕ := ([0,1,2,3,6,7,13] : List ℕ).toFinset
noncomputable def certificate_880_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,7),(0,13),(1,2),(1,3),(1,6),(1,7),(1,13),(2,3),(2,6),(2,7),(2,13),(3,6),(3,7),(3,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_881_q : Finset ℕ := ([0,1,2,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_881_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(1,2),(1,3),(1,6),(1,8),(1,11),(2,3),(2,6),(2,8),(2,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_882_q : Finset ℕ := ([0,1,2,3,6,8,12] : List ℕ).toFinset
noncomputable def certificate_882_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(1,2),(1,3),(1,6),(1,8),(1,12),(2,3),(2,6),(2,8),(2,12),(3,6),(3,8),(3,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_883_q : Finset ℕ := ([0,1,2,3,6,8,13] : List ℕ).toFinset
noncomputable def certificate_883_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,8),(0,13),(1,2),(1,3),(1,6),(1,8),(1,13),(2,3),(2,6),(2,8),(2,13),(3,6),(3,8),(3,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_884_q : Finset ℕ := ([0,1,2,3,6,9,12] : List ℕ).toFinset
noncomputable def certificate_884_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,9),(0,12),(1,2),(1,3),(1,6),(1,9),(1,12),(2,3),(2,6),(2,9),(2,12),(3,6),(3,9),(3,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_885_q : Finset ℕ := ([0,1,2,3,6,9,13] : List ℕ).toFinset
noncomputable def certificate_885_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,9),(0,13),(1,2),(1,3),(1,6),(1,9),(1,13),(2,3),(2,6),(2,9),(2,13),(3,6),(3,9),(3,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_886_q : Finset ℕ := ([0,1,2,3,6,10,13] : List ℕ).toFinset
noncomputable def certificate_886_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,10),(0,13),(1,2),(1,3),(1,6),(1,10),(1,13),(2,3),(2,6),(2,10),(2,13),(3,6),(3,10),(3,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_887_q : Finset ℕ := ([0,1,2,3,7,8,12] : List ℕ).toFinset
noncomputable def certificate_887_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,7),(0,8),(0,12),(1,2),(1,3),(1,7),(1,8),(1,12),(2,3),(2,7),(2,8),(2,12),(3,7),(3,8),(3,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_888_q : Finset ℕ := ([0,1,2,3,7,8,13] : List ℕ).toFinset
noncomputable def certificate_888_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,7),(0,8),(0,13),(1,2),(1,3),(1,7),(1,8),(1,13),(2,3),(2,7),(2,8),(2,13),(3,7),(3,8),(3,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_889_q : Finset ℕ := ([0,1,2,3,7,9,13] : List ℕ).toFinset
noncomputable def certificate_889_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,7),(0,9),(0,13),(1,2),(1,3),(1,7),(1,9),(1,13),(2,3),(2,7),(2,9),(2,13),(3,7),(3,9),(3,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_890_q : Finset ℕ := ([0,1,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_890_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(1,2),(1,4),(1,5),(1,7),(1,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_891_q : Finset ℕ := ([0,1,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_891_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(1,2),(1,4),(1,5),(1,7),(1,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_892_q : Finset ℕ := ([0,1,2,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_892_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(1,2),(1,4),(1,5),(1,7),(1,11),(2,4),(2,5),(2,7),(2,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_893_q : Finset ℕ := ([0,1,2,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_893_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(1,2),(1,4),(1,5),(1,7),(1,12),(2,4),(2,5),(2,7),(2,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_894_q : Finset ℕ := ([0,1,2,4,5,7,13] : List ℕ).toFinset
noncomputable def certificate_894_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,13),(1,2),(1,4),(1,5),(1,7),(1,13),(2,4),(2,5),(2,7),(2,13),(4,5),(4,7),(4,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_895_q : Finset ℕ := ([0,1,2,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_895_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(1,2),(1,4),(1,5),(1,8),(1,11),(2,4),(2,5),(2,8),(2,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates029
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_896_q : Finset ℕ := ([0,1,2,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_896_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,12),(1,2),(1,4),(1,5),(1,8),(1,12),(2,4),(2,5),(2,8),(2,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_897_q : Finset ℕ := ([0,1,2,4,5,8,13] : List ℕ).toFinset
noncomputable def certificate_897_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,13),(1,2),(1,4),(1,5),(1,8),(1,13),(2,4),(2,5),(2,8),(2,13),(4,5),(4,8),(4,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_898_q : Finset ℕ := ([0,1,2,4,5,9,13] : List ℕ).toFinset
noncomputable def certificate_898_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,9),(0,13),(1,2),(1,4),(1,5),(1,9),(1,13),(2,4),(2,5),(2,9),(2,13),(4,5),(4,9),(4,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_899_q : Finset ℕ := ([0,1,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_899_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(1,2),(1,4),(1,6),(1,7),(1,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_900_q : Finset ℕ := ([0,1,2,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_900_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(1,2),(1,4),(1,6),(1,7),(1,11),(2,4),(2,6),(2,7),(2,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_901_q : Finset ℕ := ([0,1,2,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_901_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,12),(1,2),(1,4),(1,6),(1,7),(1,12),(2,4),(2,6),(2,7),(2,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_902_q : Finset ℕ := ([0,1,2,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_902_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,13),(1,2),(1,4),(1,6),(1,7),(1,13),(2,4),(2,6),(2,7),(2,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_903_q : Finset ℕ := ([0,1,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_903_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(1,2),(1,4),(1,6),(1,8),(1,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_904_q : Finset ℕ := ([0,1,2,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_904_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(1,2),(1,4),(1,6),(1,8),(1,11),(2,4),(2,6),(2,8),(2,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_905_q : Finset ℕ := ([0,1,2,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_905_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(1,2),(1,4),(1,6),(1,8),(1,12),(2,4),(2,6),(2,8),(2,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_906_q : Finset ℕ := ([0,1,2,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_906_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,13),(1,2),(1,4),(1,6),(1,8),(1,13),(2,4),(2,6),(2,8),(2,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_907_q : Finset ℕ := ([0,1,2,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_907_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(1,2),(1,4),(1,6),(1,9),(1,11),(2,4),(2,6),(2,9),(2,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_908_q : Finset ℕ := ([0,1,2,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_908_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(1,2),(1,4),(1,6),(1,9),(1,12),(2,4),(2,6),(2,9),(2,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_909_q : Finset ℕ := ([0,1,2,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_909_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,13),(1,2),(1,4),(1,6),(1,9),(1,13),(2,4),(2,6),(2,9),(2,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_910_q : Finset ℕ := ([0,1,2,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_910_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(1,2),(1,4),(1,6),(1,10),(1,12),(2,4),(2,6),(2,10),(2,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_911_q : Finset ℕ := ([0,1,2,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_911_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,10),(0,13),(1,2),(1,4),(1,6),(1,10),(1,13),(2,4),(2,6),(2,10),(2,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_912_q : Finset ℕ := ([0,1,2,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_912_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,11),(0,13),(1,2),(1,4),(1,6),(1,11),(1,13),(2,4),(2,6),(2,11),(2,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_913_q : Finset ℕ := ([0,1,2,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_913_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(1,2),(1,4),(1,7),(1,8),(1,11),(2,4),(2,7),(2,8),(2,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_914_q : Finset ℕ := ([0,1,2,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_914_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,8),(0,12),(1,2),(1,4),(1,7),(1,8),(1,12),(2,4),(2,7),(2,8),(2,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_915_q : Finset ℕ := ([0,1,2,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_915_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,8),(0,13),(1,2),(1,4),(1,7),(1,8),(1,13),(2,4),(2,7),(2,8),(2,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_916_q : Finset ℕ := ([0,1,2,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_916_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(1,2),(1,4),(1,7),(1,9),(1,12),(2,4),(2,7),(2,9),(2,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_917_q : Finset ℕ := ([0,1,2,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_917_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,9),(0,13),(1,2),(1,4),(1,7),(1,9),(1,13),(2,4),(2,7),(2,9),(2,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_918_q : Finset ℕ := ([0,1,2,4,7,10,12] : List ℕ).toFinset
noncomputable def certificate_918_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,10),(0,12),(1,2),(1,4),(1,7),(1,10),(1,12),(2,4),(2,7),(2,10),(2,12),(4,7),(4,10),(4,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_919_q : Finset ℕ := ([0,1,2,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_919_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,10),(0,13),(1,2),(1,4),(1,7),(1,10),(1,13),(2,4),(2,7),(2,10),(2,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_920_q : Finset ℕ := ([0,1,2,4,7,11,13] : List ℕ).toFinset
noncomputable def certificate_920_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,11),(0,13),(1,2),(1,4),(1,7),(1,11),(1,13),(2,4),(2,7),(2,11),(2,13),(4,7),(4,11),(4,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_921_q : Finset ℕ := ([0,1,2,4,8,9,12] : List ℕ).toFinset
noncomputable def certificate_921_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,8),(0,9),(0,12),(1,2),(1,4),(1,8),(1,9),(1,12),(2,4),(2,8),(2,9),(2,12),(4,8),(4,9),(4,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_922_q : Finset ℕ := ([0,1,2,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_922_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,8),(0,9),(0,13),(1,2),(1,4),(1,8),(1,9),(1,13),(2,4),(2,8),(2,9),(2,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_923_q : Finset ℕ := ([0,1,2,4,8,10,13] : List ℕ).toFinset
noncomputable def certificate_923_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,8),(0,10),(0,13),(1,2),(1,4),(1,8),(1,10),(1,13),(2,4),(2,8),(2,10),(2,13),(4,8),(4,10),(4,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_924_q : Finset ℕ := ([0,1,2,4,9,10,13] : List ℕ).toFinset
noncomputable def certificate_924_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,9),(0,10),(0,13),(1,2),(1,4),(1,9),(1,10),(1,13),(2,4),(2,9),(2,10),(2,13),(4,9),(4,10),(4,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_925_q : Finset ℕ := ([0,1,2,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_925_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,6),(0,9),(0,12),(1,2),(1,5),(1,6),(1,9),(1,12),(2,5),(2,6),(2,9),(2,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_926_q : Finset ℕ := ([0,1,2,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_926_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,6),(0,9),(0,13),(1,2),(1,5),(1,6),(1,9),(1,13),(2,5),(2,6),(2,9),(2,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_927_q : Finset ℕ := ([0,1,2,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_927_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,7),(0,9),(0,12),(1,2),(1,5),(1,7),(1,9),(1,12),(2,5),(2,7),(2,9),(2,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates030
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_928_q : Finset ℕ := ([0,1,2,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_928_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,7),(0,9),(0,13),(1,2),(1,5),(1,7),(1,9),(1,13),(2,5),(2,7),(2,9),(2,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_929_q : Finset ℕ := ([0,1,2,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_929_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,7),(0,10),(0,13),(1,2),(1,5),(1,7),(1,10),(1,13),(2,5),(2,7),(2,10),(2,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_930_q : Finset ℕ := ([0,1,2,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_930_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,8),(0,9),(0,13),(1,2),(1,5),(1,8),(1,9),(1,13),(2,5),(2,8),(2,9),(2,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_931_q : Finset ℕ := ([0,1,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_931_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(1,3),(1,4),(1,6),(1,7),(1,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_932_q : Finset ℕ := ([0,1,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_932_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(1,3),(1,4),(1,6),(1,7),(1,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_933_q : Finset ℕ := ([0,1,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_933_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(1,3),(1,4),(1,6),(1,7),(1,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_934_q : Finset ℕ := ([0,1,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_934_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,12),(1,3),(1,4),(1,6),(1,7),(1,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_935_q : Finset ℕ := ([0,1,3,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_935_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,13),(1,3),(1,4),(1,6),(1,7),(1,13),(3,4),(3,6),(3,7),(3,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_936_q : Finset ℕ := ([0,1,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_936_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(1,3),(1,4),(1,6),(1,8),(1,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_937_q : Finset ℕ := ([0,1,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_937_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(1,3),(1,4),(1,6),(1,8),(1,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_938_q : Finset ℕ := ([0,1,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_938_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(1,3),(1,4),(1,6),(1,8),(1,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_939_q : Finset ℕ := ([0,1,3,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_939_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,13),(1,3),(1,4),(1,6),(1,8),(1,13),(3,4),(3,6),(3,8),(3,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_940_q : Finset ℕ := ([0,1,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_940_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(1,3),(1,4),(1,6),(1,9),(1,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_941_q : Finset ℕ := ([0,1,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_941_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(1,3),(1,4),(1,6),(1,9),(1,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_942_q : Finset ℕ := ([0,1,3,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_942_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,9),(0,13),(1,3),(1,4),(1,6),(1,9),(1,13),(3,4),(3,6),(3,9),(3,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_943_q : Finset ℕ := ([0,1,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_943_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,10),(0,12),(1,3),(1,4),(1,6),(1,10),(1,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_944_q : Finset ℕ := ([0,1,3,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_944_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,10),(0,13),(1,3),(1,4),(1,6),(1,10),(1,13),(3,4),(3,6),(3,10),(3,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_945_q : Finset ℕ := ([0,1,3,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_945_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,11),(0,13),(1,3),(1,4),(1,6),(1,11),(1,13),(3,4),(3,6),(3,11),(3,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_946_q : Finset ℕ := ([0,1,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_946_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(1,3),(1,4),(1,7),(1,8),(1,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_947_q : Finset ℕ := ([0,1,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_947_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,8),(0,12),(1,3),(1,4),(1,7),(1,8),(1,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_948_q : Finset ℕ := ([0,1,3,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_948_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,7),(0,8),(0,13),(1,3),(1,4),(1,7),(1,8),(1,13),(3,4),(3,7),(3,8),(3,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_949_q : Finset ℕ := ([0,1,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_949_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,9),(0,12),(1,3),(1,4),(1,7),(1,9),(1,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_950_q : Finset ℕ := ([0,1,3,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_950_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,7),(0,9),(0,13),(1,3),(1,4),(1,7),(1,9),(1,13),(3,4),(3,7),(3,9),(3,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_951_q : Finset ℕ := ([0,1,3,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_951_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,7),(0,10),(0,13),(1,3),(1,4),(1,7),(1,10),(1,13),(3,4),(3,7),(3,10),(3,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_952_q : Finset ℕ := ([0,1,3,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_952_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,8),(0,9),(0,13),(1,3),(1,4),(1,8),(1,9),(1,13),(3,4),(3,8),(3,9),(3,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_953_q : Finset ℕ := ([0,1,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_953_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(1,3),(1,5),(1,6),(1,8),(1,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_954_q : Finset ℕ := ([0,1,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_954_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(1,3),(1,5),(1,6),(1,8),(1,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_955_q : Finset ℕ := ([0,1,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_955_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(1,3),(1,5),(1,6),(1,8),(1,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_956_q : Finset ℕ := ([0,1,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_956_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,13),(1,3),(1,5),(1,6),(1,8),(1,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_957_q : Finset ℕ := ([0,1,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_957_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,9),(0,12),(1,3),(1,5),(1,6),(1,9),(1,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_958_q : Finset ℕ := ([0,1,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_958_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,9),(0,13),(1,3),(1,5),(1,6),(1,9),(1,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_959_q : Finset ℕ := ([0,1,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_959_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(1,3),(1,5),(1,7),(1,8),(1,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates031
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_960_q : Finset ℕ := ([0,1,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_960_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,8),(0,12),(1,3),(1,5),(1,7),(1,8),(1,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_961_q : Finset ℕ := ([0,1,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_961_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,8),(0,13),(1,3),(1,5),(1,7),(1,8),(1,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_962_q : Finset ℕ := ([0,1,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_962_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(1,3),(1,5),(1,7),(1,9),(1,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_963_q : Finset ℕ := ([0,1,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_963_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(1,3),(1,5),(1,7),(1,9),(1,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_964_q : Finset ℕ := ([0,1,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_964_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,13),(1,3),(1,5),(1,7),(1,9),(1,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_965_q : Finset ℕ := ([0,1,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_965_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(1,3),(1,5),(1,7),(1,10),(1,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_966_q : Finset ℕ := ([0,1,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_966_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,10),(0,13),(1,3),(1,5),(1,7),(1,10),(1,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_967_q : Finset ℕ := ([0,1,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_967_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,11),(0,13),(1,3),(1,5),(1,7),(1,11),(1,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_968_q : Finset ℕ := ([0,1,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_968_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,9),(0,12),(1,3),(1,5),(1,8),(1,9),(1,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_969_q : Finset ℕ := ([0,1,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_969_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,8),(0,9),(0,13),(1,3),(1,5),(1,8),(1,9),(1,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_970_q : Finset ℕ := ([0,1,3,5,8,10,12] : List ℕ).toFinset
noncomputable def certificate_970_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,10),(0,12),(1,3),(1,5),(1,8),(1,10),(1,12),(3,5),(3,8),(3,10),(3,12),(5,8),(5,10),(5,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_971_q : Finset ℕ := ([0,1,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_971_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,8),(0,10),(0,13),(1,3),(1,5),(1,8),(1,10),(1,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_972_q : Finset ℕ := ([0,1,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_972_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,8),(0,11),(0,13),(1,3),(1,5),(1,8),(1,11),(1,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_973_q : Finset ℕ := ([0,1,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_973_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,9),(0,10),(0,13),(1,3),(1,5),(1,9),(1,10),(1,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_974_q : Finset ℕ := ([0,1,3,5,9,11,13] : List ℕ).toFinset
noncomputable def certificate_974_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,9),(0,11),(0,13),(1,3),(1,5),(1,9),(1,11),(1,13),(3,5),(3,9),(3,11),(3,13),(5,9),(5,11),(5,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_975_q : Finset ℕ := ([0,1,3,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_975_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(1,3),(1,6),(1,7),(1,9),(1,12),(3,6),(3,7),(3,9),(3,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_976_q : Finset ℕ := ([0,1,3,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_976_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,7),(0,9),(0,13),(1,3),(1,6),(1,7),(1,9),(1,13),(3,6),(3,7),(3,9),(3,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_977_q : Finset ℕ := ([0,1,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_977_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,7),(0,10),(0,13),(1,3),(1,6),(1,7),(1,10),(1,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_978_q : Finset ℕ := ([0,1,3,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_978_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,8),(0,9),(0,12),(1,3),(1,6),(1,8),(1,9),(1,12),(3,6),(3,8),(3,9),(3,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_979_q : Finset ℕ := ([0,1,3,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_979_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,8),(0,9),(0,13),(1,3),(1,6),(1,8),(1,9),(1,13),(3,6),(3,8),(3,9),(3,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_980_q : Finset ℕ := ([0,1,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_980_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,8),(0,10),(0,13),(1,3),(1,6),(1,8),(1,10),(1,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_981_q : Finset ℕ := ([0,1,3,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_981_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,8),(0,11),(0,13),(1,3),(1,6),(1,8),(1,11),(1,13),(3,6),(3,8),(3,11),(3,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_982_q : Finset ℕ := ([0,1,3,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_982_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,9),(0,10),(0,13),(1,3),(1,6),(1,9),(1,10),(1,13),(3,6),(3,9),(3,10),(3,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_983_q : Finset ℕ := ([0,1,3,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_983_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,7),(0,9),(0,10),(0,13),(1,3),(1,7),(1,9),(1,10),(1,13),(3,7),(3,9),(3,10),(3,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_984_q : Finset ℕ := ([0,1,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_984_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,4),(0,5),(0,8),(0,9),(0,12),(1,4),(1,5),(1,8),(1,9),(1,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_985_q : Finset ℕ := ([0,1,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_985_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,4),(0,5),(0,8),(0,9),(0,13),(1,4),(1,5),(1,8),(1,9),(1,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_986_q : Finset ℕ := ([0,1,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_986_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,4),(0,5),(0,8),(0,10),(0,13),(1,4),(1,5),(1,8),(1,10),(1,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_987_q : Finset ℕ := ([0,1,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_987_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,4),(0,6),(0,8),(0,10),(0,13),(1,4),(1,6),(1,8),(1,10),(1,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_988_q : Finset ℕ := ([0,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_988_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_989_q : Finset ℕ := ([0,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_989_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_990_q : Finset ℕ := ([0,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_990_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_991_q : Finset ℕ := ([0,2,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_991_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(2,3),(2,5),(2,6),(2,8),(2,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates032
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_992_q : Finset ℕ := ([0,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_992_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_993_q : Finset ℕ := ([0,2,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_993_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(2,3),(2,5),(2,6),(2,9),(2,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_994_q : Finset ℕ := ([0,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_994_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_995_q : Finset ℕ := ([0,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_995_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_996_q : Finset ℕ := ([0,2,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_996_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,8),(0,13),(2,3),(2,5),(2,7),(2,8),(2,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_997_q : Finset ℕ := ([0,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_997_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_998_q : Finset ℕ := ([0,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_998_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_999_q : Finset ℕ := ([0,2,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_999_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(2,3),(2,5),(2,7),(2,9),(2,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def disjointCliques (a k : ℕ) : SimpleGraph (Fin a × Fin k) where
  Adj u v := u.1 = v.1 ∧ u.2 ≠ v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_10_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[],[4]],[[],[],[],[5]],[[],[],[1,1]],[[],[],[1,2]],[[],[],[1,3]],[[],[],[1,4]],[[],[],[2,2]],[[],[],[2,3]],[[],[1],[1]],[[],[1],[2]],[[],[1],[3]],[[],[1],[4]]]

noncomputable def patterns_10_5_1 : List (List (List ℕ)) := [[[],[1,1,1]],[[],[1,1,2]],[[],[1,1,3]],[[],[1,2,1]],[[],[1,2,2]],[[],[1,3,1]],[[],[2],[2]],[[],[2],[3]],[[],[2,1,2]],[[1],[1,1]],[[1],[1,2]],[[1],[1,3]],[[1],[2,2]],[[1,1],[2]],[[1,1],[3]],[[1,1,1,1]]]

noncomputable def patterns_10_5_2 : List (List (List ℕ)) := [[[1,1,1,2]],[[1,1,2,1]],[[1,2],[2]]]

noncomputable def patterns_10_5 : List (List (List ℕ)) := patterns_10_5_0 ++ (patterns_10_5_1 ++ (patterns_10_5_2 ++ ([])))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_10_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[2,2]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,2,1]],[[],[],[2],[2]]]

noncomputable def patterns_10_6_1 : List (List (List ℕ)) := [[[],[1],[1,1]],[[],[1],[1,2]],[[],[1,1],[2]],[[],[1,1,1,1]],[[1],[1],[1]],[[1],[1],[2]],[[1],[1,1,1]],[[1,1],[1,1]]]

noncomputable def patterns_10_6 : List (List (List ℕ)) := patterns_10_6_0 ++ (patterns_10_6_1 ++ ([]))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_10_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1,1,1]],[[],[],[1],[1,1]],[[],[1],[1],[1]]]

noncomputable def patterns_10_7 : List (List (List ℕ)) := patterns_10_7_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_10_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[1,1]],[[],[],[],[],[1],[1]]]

noncomputable def patterns_10_8 : List (List (List ℕ)) := patterns_10_8_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_11_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[],[4]],[[],[],[],[5]],[[],[],[],[6]],[[],[],[1,1]],[[],[],[1,2]],[[],[],[1,3]],[[],[],[1,4]],[[],[],[1,5]],[[],[],[2,2]],[[],[],[2,3]],[[],[],[2,4]],[[],[],[3,3]]]

noncomputable def patterns_11_5_1 : List (List (List ℕ)) := [[[],[1],[1]],[[],[1],[2]],[[],[1],[3]],[[],[1],[4]],[[],[1],[5]],[[],[1,1,1]],[[],[1,1,2]],[[],[1,1,3]],[[],[1,1,4]],[[],[1,2,1]],[[],[1,2,2]],[[],[1,2,3]],[[],[1,3,1]],[[],[1,3,2]],[[],[1,4,1]],[[],[2],[2]]]

noncomputable def patterns_11_5_2 : List (List (List ℕ)) := [[[],[2],[3]],[[],[2],[4]],[[],[2,1,2]],[[],[2,1,3]],[[],[2,2,2]],[[],[3],[3]],[[1],[1,1]],[[1],[1,2]],[[1],[1,3]],[[1],[1,4]],[[1],[2,2]],[[1],[2,3]],[[1,1],[2]],[[1,1],[3]],[[1,1],[4]],[[1,1,1,1]]]

noncomputable def patterns_11_5_3 : List (List (List ℕ)) := [[[1,1,1,2]],[[1,1,1,3]],[[1,1,2,1]],[[1,1,2,2]],[[1,1,3,1]],[[1,2],[2]],[[1,2],[3]],[[1,2,1,2]],[[1,2,2,1]],[[1,3],[2]],[[2],[2,2]],[[2,1,1,2]]]

noncomputable def patterns_11_5 : List (List (List ℕ)) := patterns_11_5_0 ++ (patterns_11_5_1 ++ (patterns_11_5_2 ++ (patterns_11_5_3 ++ ([]))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_11_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[],[5]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[1,4]],[[],[],[],[2,2]],[[],[],[],[2,3]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1],[4]]]

noncomputable def patterns_11_6_1 : List (List (List ℕ)) := [[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,1,3]],[[],[],[1,2,1]],[[],[],[1,2,2]],[[],[],[1,3,1]],[[],[],[2],[2]],[[],[],[2],[3]],[[],[],[2,1,2]],[[],[1],[1,1]],[[],[1],[1,2]],[[],[1],[1,3]],[[],[1],[2,2]],[[],[1,1],[2]],[[],[1,1],[3]],[[],[1,1,1,1]]]

noncomputable def patterns_11_6_2 : List (List (List ℕ)) := [[[],[1,1,1,2]],[[],[1,1,2,1]],[[],[1,2],[2]],[[1],[1],[1]],[[1],[1],[2]],[[1],[1],[3]],[[1],[1,1,1]],[[1],[1,1,2]],[[1],[1,2,1]],[[1],[2],[2]],[[1,1],[1,1]],[[1,1],[1,2]],[[1,1,1],[2]],[[1,1,1,1,1]]]

noncomputable def patterns_11_6 : List (List (List ℕ)) := patterns_11_6_0 ++ (patterns_11_6_1 ++ (patterns_11_6_2 ++ ([])))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_11_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[2,2]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,2,1]],[[],[],[],[2],[2]]]

noncomputable def patterns_11_7_1 : List (List (List ℕ)) := [[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1,1],[2]],[[],[],[1,1,1,1]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1,1,1]],[[],[1,1],[1,1]],[[1],[1],[1,1]]]

noncomputable def patterns_11_7 : List (List (List ℕ)) := patterns_11_7_0 ++ (patterns_11_7_1 ++ ([]))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_11_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1,1,1]],[[],[],[],[1],[1,1]],[[],[],[1],[1],[1]]]

noncomputable def patterns_11_8 : List (List (List ℕ)) := patterns_11_8_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns12x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_12_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[],[5]],[[],[],[],[],[6]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[1,4]],[[],[],[],[1,5]],[[],[],[],[2,2]],[[],[],[],[2,3]],[[],[],[],[2,4]],[[],[],[],[3,3]]]

noncomputable def patterns_12_6_1 : List (List (List ℕ)) := [[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1],[4]],[[],[],[1],[5]],[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,1,3]],[[],[],[1,1,4]],[[],[],[1,2,1]],[[],[],[1,2,2]],[[],[],[1,2,3]],[[],[],[1,3,1]],[[],[],[1,3,2]],[[],[],[1,4,1]],[[],[],[2],[2]]]

noncomputable def patterns_12_6_2 : List (List (List ℕ)) := [[[],[],[2],[3]],[[],[],[2],[4]],[[],[],[2,1,2]],[[],[],[2,1,3]],[[],[],[2,2,2]],[[],[],[3],[3]],[[],[1],[1,1]],[[],[1],[1,2]],[[],[1],[1,3]],[[],[1],[1,4]],[[],[1],[2,2]],[[],[1],[2,3]],[[],[1,1],[2]],[[],[1,1],[3]],[[],[1,1],[4]],[[],[1,1,1,1]]]

noncomputable def patterns_12_6_3 : List (List (List ℕ)) := [[[],[1,1,1,2]],[[],[1,1,1,3]],[[],[1,1,2,1]],[[],[1,1,2,2]],[[],[1,1,3,1]],[[],[1,2],[2]],[[],[1,2],[3]],[[],[1,2,1,2]],[[],[1,2,2,1]],[[],[1,3],[2]],[[],[2],[2,2]],[[],[2,1,1,2]],[[1],[1],[1]],[[1],[1],[2]],[[1],[1],[3]],[[1],[1],[4]]]

noncomputable def patterns_12_6_4 : List (List (List ℕ)) := [[[1],[1,1,1]],[[1],[1,1,2]],[[1],[1,1,3]],[[1],[1,2,1]],[[1],[1,2,2]],[[1],[1,3,1]],[[1],[2],[2]],[[1],[2],[3]],[[1],[2,1,2]],[[1,1],[1,1]],[[1,1],[1,2]],[[1,1],[1,3]],[[1,1],[2,2]],[[1,1,1],[2]],[[1,1,1],[3]],[[1,1,1,1,1]]]

noncomputable def patterns_12_6_5 : List (List (List ℕ)) := [[[1,1,1,1,2]],[[1,1,1,2,1]],[[1,1,2],[2]],[[1,1,2,1,1]],[[1,2],[1,2]],[[1,2,1],[2]],[[2],[2],[2]]]

noncomputable def patterns_12_6 : List (List (List ℕ)) := patterns_12_6_0 ++ (patterns_12_6_1 ++ (patterns_12_6_2 ++ (patterns_12_6_3 ++ (patterns_12_6_4 ++ (patterns_12_6_5 ++ ([]))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns12x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_12_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[2,2]],[[],[],[],[],[2,3]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]]]

noncomputable def patterns_12_7_1 : List (List (List ℕ)) := [[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,2,1]],[[],[],[],[1,2,2]],[[],[],[],[1,3,1]],[[],[],[],[2],[2]],[[],[],[],[2],[3]],[[],[],[],[2,1,2]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[2,2]],[[],[],[1,1],[2]],[[],[],[1,1],[3]],[[],[],[1,1,1,1]]]

noncomputable def patterns_12_7_2 : List (List (List ℕ)) := [[[],[],[1,1,1,2]],[[],[],[1,1,2,1]],[[],[],[1,2],[2]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,2,1]],[[],[1],[2],[2]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1,1],[2]],[[],[1,1,1,1,1]],[[1],[1],[1,1]],[[1],[1],[1,2]]]

noncomputable def patterns_12_7_3 : List (List (List ℕ)) := [[[1],[1,1],[2]],[[1],[1,1,1,1]],[[1,1],[1,1,1]]]

noncomputable def patterns_12_7 : List (List (List ℕ)) := patterns_12_7_0 ++ (patterns_12_7_1 ++ (patterns_12_7_2 ++ (patterns_12_7_3 ++ ([]))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns12x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_12_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[2,2]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,2,1]],[[],[],[],[],[2],[2]]]

noncomputable def patterns_12_8_1 : List (List (List ℕ)) := [[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1,1],[2]],[[],[],[],[1,1,1,1]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1,1,1]],[[],[],[1,1],[1,1]],[[],[1],[1],[1,1]],[[1],[1],[1],[1]]]

noncomputable def patterns_12_8 : List (List (List ℕ)) := patterns_12_8_0 ++ (patterns_12_8_1 ++ ([]))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_13_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[],[5]],[[],[],[],[],[6]],[[],[],[],[],[7]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[1,4]],[[],[],[],[1,5]],[[],[],[],[1,6]],[[],[],[],[2,2]],[[],[],[],[2,3]]]

noncomputable def patterns_13_6_1 : List (List (List ℕ)) := [[[],[],[],[2,4]],[[],[],[],[2,5]],[[],[],[],[3,3]],[[],[],[],[3,4]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1],[4]],[[],[],[1],[5]],[[],[],[1],[6]],[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,1,3]],[[],[],[1,1,4]],[[],[],[1,1,5]],[[],[],[1,2,1]]]

noncomputable def patterns_13_6_2 : List (List (List ℕ)) := [[[],[],[1,2,2]],[[],[],[1,2,3]],[[],[],[1,2,4]],[[],[],[1,3,1]],[[],[],[1,3,2]],[[],[],[1,3,3]],[[],[],[1,4,1]],[[],[],[1,4,2]],[[],[],[1,5,1]],[[],[],[2],[2]],[[],[],[2],[3]],[[],[],[2],[4]],[[],[],[2],[5]],[[],[],[2,1,2]],[[],[],[2,1,3]],[[],[],[2,1,4]]]

noncomputable def patterns_13_6_3 : List (List (List ℕ)) := [[[],[],[2,2,2]],[[],[],[2,2,3]],[[],[],[2,3,2]],[[],[],[3],[3]],[[],[],[3],[4]],[[],[],[3,1,3]],[[],[1],[1,1]],[[],[1],[1,2]],[[],[1],[1,3]],[[],[1],[1,4]],[[],[1],[1,5]],[[],[1],[2,2]],[[],[1],[2,3]],[[],[1],[2,4]],[[],[1],[3,3]],[[],[1,1],[2]]]

noncomputable def patterns_13_6_4 : List (List (List ℕ)) := [[[],[1,1],[3]],[[],[1,1],[4]],[[],[1,1],[5]],[[],[1,1,1,1]],[[],[1,1,1,2]],[[],[1,1,1,3]],[[],[1,1,1,4]],[[],[1,1,2,1]],[[],[1,1,2,2]],[[],[1,1,2,3]],[[],[1,1,3,1]],[[],[1,1,3,2]],[[],[1,1,4,1]],[[],[1,2],[2]],[[],[1,2],[3]],[[],[1,2],[4]]]

noncomputable def patterns_13_6_5 : List (List (List ℕ)) := [[[],[1,2,1,2]],[[],[1,2,1,3]],[[],[1,2,2,1]],[[],[1,2,2,2]],[[],[1,2,3,1]],[[],[1,3],[2]],[[],[1,3],[3]],[[],[1,3,1,2]],[[],[1,4],[2]],[[],[2],[2,2]],[[],[2],[2,3]],[[],[2,1,1,2]],[[],[2,1,1,3]],[[],[2,1,2,2]],[[],[2,2],[3]],[[1],[1],[1]]]

noncomputable def patterns_13_6_6 : List (List (List ℕ)) := [[[1],[1],[2]],[[1],[1],[3]],[[1],[1],[4]],[[1],[1],[5]],[[1],[1,1,1]],[[1],[1,1,2]],[[1],[1,1,3]],[[1],[1,1,4]],[[1],[1,2,1]],[[1],[1,2,2]],[[1],[1,2,3]],[[1],[1,3,1]],[[1],[1,3,2]],[[1],[1,4,1]],[[1],[2],[2]],[[1],[2],[3]]]

noncomputable def patterns_13_6_7 : List (List (List ℕ)) := [[[1],[2],[4]],[[1],[2,1,2]],[[1],[2,1,3]],[[1],[2,2,2]],[[1],[3],[3]],[[1,1],[1,1]],[[1,1],[1,2]],[[1,1],[1,3]],[[1,1],[1,4]],[[1,1],[2,2]],[[1,1],[2,3]],[[1,1,1],[2]],[[1,1,1],[3]],[[1,1,1],[4]],[[1,1,1,1,1]],[[1,1,1,1,2]]]

noncomputable def patterns_13_6_8 : List (List (List ℕ)) := [[[1,1,1,1,3]],[[1,1,1,2,1]],[[1,1,1,2,2]],[[1,1,1,3,1]],[[1,1,2],[2]],[[1,1,2],[3]],[[1,1,2,1,1]],[[1,1,2,1,2]],[[1,1,2,2,1]],[[1,1,3],[2]],[[1,1,3,1,1]],[[1,2],[1,2]],[[1,2],[1,3]],[[1,2],[2,2]],[[1,2,1],[2]],[[1,2,1],[3]]]

noncomputable def patterns_13_6_9 : List (List (List ℕ)) := [[[1,2,1,1,2]],[[1,2,1,2,1]],[[1,2,2],[2]],[[1,3,1],[2]],[[2],[2],[2]],[[2],[2],[3]],[[2],[2,1,2]],[[2,1,1,1,2]]]

noncomputable def patterns_13_6 : List (List (List ℕ)) := patterns_13_6_0 ++ (patterns_13_6_1 ++ (patterns_13_6_2 ++ (patterns_13_6_3 ++ (patterns_13_6_4 ++ (patterns_13_6_5 ++ (patterns_13_6_6 ++ (patterns_13_6_7 ++ (patterns_13_6_8 ++ (patterns_13_6_9 ++ ([]))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_13_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[],[6]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[1,5]],[[],[],[],[],[2,2]],[[],[],[],[],[2,3]],[[],[],[],[],[2,4]],[[],[],[],[],[3,3]]]

noncomputable def patterns_13_7_1 : List (List (List ℕ)) := [[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]],[[],[],[],[1],[5]],[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,1,4]],[[],[],[],[1,2,1]],[[],[],[],[1,2,2]],[[],[],[],[1,2,3]],[[],[],[],[1,3,1]],[[],[],[],[1,3,2]],[[],[],[],[1,4,1]],[[],[],[],[2],[2]]]

noncomputable def patterns_13_7_2 : List (List (List ℕ)) := [[[],[],[],[2],[3]],[[],[],[],[2],[4]],[[],[],[],[2,1,2]],[[],[],[],[2,1,3]],[[],[],[],[2,2,2]],[[],[],[],[3],[3]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[1,4]],[[],[],[1],[2,2]],[[],[],[1],[2,3]],[[],[],[1,1],[2]],[[],[],[1,1],[3]],[[],[],[1,1],[4]],[[],[],[1,1,1,1]]]

noncomputable def patterns_13_7_3 : List (List (List ℕ)) := [[[],[],[1,1,1,2]],[[],[],[1,1,1,3]],[[],[],[1,1,2,1]],[[],[],[1,1,2,2]],[[],[],[1,1,3,1]],[[],[],[1,2],[2]],[[],[],[1,2],[3]],[[],[],[1,2,1,2]],[[],[],[1,2,2,1]],[[],[],[1,3],[2]],[[],[],[2],[2,2]],[[],[],[2,1,1,2]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1],[4]]]

noncomputable def patterns_13_7_4 : List (List (List ℕ)) := [[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,1,3]],[[],[1],[1,2,1]],[[],[1],[1,2,2]],[[],[1],[1,3,1]],[[],[1],[2],[2]],[[],[1],[2],[3]],[[],[1],[2,1,2]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1],[1,3]],[[],[1,1],[2,2]],[[],[1,1,1],[2]],[[],[1,1,1],[3]],[[],[1,1,1,1,1]]]

noncomputable def patterns_13_7_5 : List (List (List ℕ)) := [[[],[1,1,1,1,2]],[[],[1,1,1,2,1]],[[],[1,1,2],[2]],[[],[1,1,2,1,1]],[[],[1,2],[1,2]],[[],[1,2,1],[2]],[[],[2],[2],[2]],[[1],[1],[1,1]],[[1],[1],[1,2]],[[1],[1],[1,3]],[[1],[1],[2,2]],[[1],[1,1],[2]],[[1],[1,1],[3]],[[1],[1,1,1,1]],[[1],[1,1,1,2]],[[1],[1,1,2,1]]]

noncomputable def patterns_13_7_6 : List (List (List ℕ)) := [[[1],[1,2],[2]],[[1,1],[1,1,1]],[[1,1],[1,1,2]],[[1,1],[1,2,1]],[[1,1],[2],[2]],[[1,1,1],[1,2]],[[1,1,1,1],[2]],[[1,1,1,1,1,1]]]

noncomputable def patterns_13_7 : List (List (List ℕ)) := patterns_13_7_0 ++ (patterns_13_7_1 ++ (patterns_13_7_2 ++ (patterns_13_7_3 ++ (patterns_13_7_4 ++ (patterns_13_7_5 ++ (patterns_13_7_6 ++ ([])))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_13_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]]]

noncomputable def patterns_13_8_1 : List (List (List ℕ)) := [[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,3,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2,1,2]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[2,2]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1,1,1]]]

noncomputable def patterns_13_8_2 : List (List (List ℕ)) := [[[],[],[],[1,1,1,2]],[[],[],[],[1,1,2,1]],[[],[],[],[1,2],[2]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,2,1]],[[],[],[1],[2],[2]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1,1],[2]],[[],[],[1,1,1,1,1]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]]]

noncomputable def patterns_13_8_3 : List (List (List ℕ)) := [[[],[1],[1,1],[2]],[[],[1],[1,1,1,1]],[[],[1,1],[1,1,1]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1,1,1]],[[1],[1,1],[1,1]]]

noncomputable def patterns_13_8 : List (List (List ℕ)) := patterns_13_8_0 ++ (patterns_13_8_1 ++ (patterns_13_8_2 ++ (patterns_13_8_3 ++ ([]))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_14_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[],[6]],[[],[],[],[],[],[7]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[1,5]],[[],[],[],[],[1,6]],[[],[],[],[],[2,2]],[[],[],[],[],[2,3]]]

noncomputable def patterns_14_7_1 : List (List (List ℕ)) := [[[],[],[],[],[2,4]],[[],[],[],[],[2,5]],[[],[],[],[],[3,3]],[[],[],[],[],[3,4]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]],[[],[],[],[1],[5]],[[],[],[],[1],[6]],[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,1,4]],[[],[],[],[1,1,5]],[[],[],[],[1,2,1]]]

noncomputable def patterns_14_7_2 : List (List (List ℕ)) := [[[],[],[],[1,2,2]],[[],[],[],[1,2,3]],[[],[],[],[1,2,4]],[[],[],[],[1,3,1]],[[],[],[],[1,3,2]],[[],[],[],[1,3,3]],[[],[],[],[1,4,1]],[[],[],[],[1,4,2]],[[],[],[],[1,5,1]],[[],[],[],[2],[2]],[[],[],[],[2],[3]],[[],[],[],[2],[4]],[[],[],[],[2],[5]],[[],[],[],[2,1,2]],[[],[],[],[2,1,3]],[[],[],[],[2,1,4]]]

noncomputable def patterns_14_7_3 : List (List (List ℕ)) := [[[],[],[],[2,2,2]],[[],[],[],[2,2,3]],[[],[],[],[2,3,2]],[[],[],[],[3],[3]],[[],[],[],[3],[4]],[[],[],[],[3,1,3]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[1,4]],[[],[],[1],[1,5]],[[],[],[1],[2,2]],[[],[],[1],[2,3]],[[],[],[1],[2,4]],[[],[],[1],[3,3]],[[],[],[1,1],[2]]]

noncomputable def patterns_14_7_4 : List (List (List ℕ)) := [[[],[],[1,1],[3]],[[],[],[1,1],[4]],[[],[],[1,1],[5]],[[],[],[1,1,1,1]],[[],[],[1,1,1,2]],[[],[],[1,1,1,3]],[[],[],[1,1,1,4]],[[],[],[1,1,2,1]],[[],[],[1,1,2,2]],[[],[],[1,1,2,3]],[[],[],[1,1,3,1]],[[],[],[1,1,3,2]],[[],[],[1,1,4,1]],[[],[],[1,2],[2]],[[],[],[1,2],[3]],[[],[],[1,2],[4]]]

noncomputable def patterns_14_7_5 : List (List (List ℕ)) := [[[],[],[1,2,1,2]],[[],[],[1,2,1,3]],[[],[],[1,2,2,1]],[[],[],[1,2,2,2]],[[],[],[1,2,3,1]],[[],[],[1,3],[2]],[[],[],[1,3],[3]],[[],[],[1,3,1,2]],[[],[],[1,4],[2]],[[],[],[2],[2,2]],[[],[],[2],[2,3]],[[],[],[2,1,1,2]],[[],[],[2,1,1,3]],[[],[],[2,1,2,2]],[[],[],[2,2],[3]],[[],[1],[1],[1]]]

noncomputable def patterns_14_7_6 : List (List (List ℕ)) := [[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1],[4]],[[],[1],[1],[5]],[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,1,3]],[[],[1],[1,1,4]],[[],[1],[1,2,1]],[[],[1],[1,2,2]],[[],[1],[1,2,3]],[[],[1],[1,3,1]],[[],[1],[1,3,2]],[[],[1],[1,4,1]],[[],[1],[2],[2]],[[],[1],[2],[3]]]

noncomputable def patterns_14_7_7 : List (List (List ℕ)) := [[[],[1],[2],[4]],[[],[1],[2,1,2]],[[],[1],[2,1,3]],[[],[1],[2,2,2]],[[],[1],[3],[3]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1],[1,3]],[[],[1,1],[1,4]],[[],[1,1],[2,2]],[[],[1,1],[2,3]],[[],[1,1,1],[2]],[[],[1,1,1],[3]],[[],[1,1,1],[4]],[[],[1,1,1,1,1]],[[],[1,1,1,1,2]]]

noncomputable def patterns_14_7_8 : List (List (List ℕ)) := [[[],[1,1,1,1,3]],[[],[1,1,1,2,1]],[[],[1,1,1,2,2]],[[],[1,1,1,3,1]],[[],[1,1,2],[2]],[[],[1,1,2],[3]],[[],[1,1,2,1,1]],[[],[1,1,2,1,2]],[[],[1,1,2,2,1]],[[],[1,1,3],[2]],[[],[1,1,3,1,1]],[[],[1,2],[1,2]],[[],[1,2],[1,3]],[[],[1,2],[2,2]],[[],[1,2,1],[2]],[[],[1,2,1],[3]]]

noncomputable def patterns_14_7_9 : List (List (List ℕ)) := [[[],[1,2,1,1,2]],[[],[1,2,1,2,1]],[[],[1,2,2],[2]],[[],[1,3,1],[2]],[[],[2],[2],[2]],[[],[2],[2],[3]],[[],[2],[2,1,2]],[[],[2,1,1,1,2]],[[1],[1],[1,1]],[[1],[1],[1,2]],[[1],[1],[1,3]],[[1],[1],[1,4]],[[1],[1],[2,2]],[[1],[1],[2,3]],[[1],[1,1],[2]],[[1],[1,1],[3]]]

noncomputable def patterns_14_7_10 : List (List (List ℕ)) := [[[1],[1,1],[4]],[[1],[1,1,1,1]],[[1],[1,1,1,2]],[[1],[1,1,1,3]],[[1],[1,1,2,1]],[[1],[1,1,2,2]],[[1],[1,1,3,1]],[[1],[1,2],[2]],[[1],[1,2],[3]],[[1],[1,2,1,2]],[[1],[1,2,2,1]],[[1],[1,3],[2]],[[1],[2],[2,2]],[[1],[2,1,1,2]],[[1,1],[1,1,1]],[[1,1],[1,1,2]]]

noncomputable def patterns_14_7_11 : List (List (List ℕ)) := [[[1,1],[1,1,3]],[[1,1],[1,2,1]],[[1,1],[1,2,2]],[[1,1],[1,3,1]],[[1,1],[2],[2]],[[1,1],[2],[3]],[[1,1],[2,1,2]],[[1,1,1],[1,2]],[[1,1,1],[1,3]],[[1,1,1],[2,2]],[[1,1,1,1],[2]],[[1,1,1,1],[3]],[[1,1,1,1,1,1]],[[1,1,1,1,1,2]],[[1,1,1,1,2,1]],[[1,1,1,2],[2]]]

noncomputable def patterns_14_7_12 : List (List (List ℕ)) := [[[1,1,1,2,1,1]],[[1,1,2],[1,2]],[[1,1,2,1],[2]],[[1,2],[1,2,1]],[[1,2],[2],[2]]]

noncomputable def patterns_14_7 : List (List (List ℕ)) := patterns_14_7_0 ++ (patterns_14_7_1 ++ (patterns_14_7_2 ++ (patterns_14_7_3 ++ (patterns_14_7_4 ++ (patterns_14_7_5 ++ (patterns_14_7_6 ++ (patterns_14_7_7 ++ (patterns_14_7_8 ++ (patterns_14_7_9 ++ (patterns_14_7_10 ++ (patterns_14_7_11 ++ (patterns_14_7_12 ++ ([])))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_14_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[],[2,4]],[[],[],[],[],[],[3,3]]]

noncomputable def patterns_14_8_1 : List (List (List ℕ)) := [[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,4,1]],[[],[],[],[],[2],[2]]]

noncomputable def patterns_14_8_2 : List (List (List ℕ)) := [[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,2,2]],[[],[],[],[],[3],[3]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1,1,1]]]

noncomputable def patterns_14_8_3 : List (List (List ℕ)) := [[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,3,1]],[[],[],[],[1,2],[2]],[[],[],[],[1,2],[3]],[[],[],[],[1,2,1,2]],[[],[],[],[1,2,2,1]],[[],[],[],[1,3],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2,1,1,2]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]]]

noncomputable def patterns_14_8_4 : List (List (List ℕ)) := [[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]],[[],[],[1],[1,3,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]],[[],[],[1],[2,1,2]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[2,2]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]],[[],[],[1,1,1,1,1]]]

noncomputable def patterns_14_8_5 : List (List (List ℕ)) := [[[],[],[1,1,1,1,2]],[[],[],[1,1,1,2,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2,1],[2]],[[],[],[2],[2],[2]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[2,2]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]],[[],[1],[1,1,1,1]],[[],[1],[1,1,1,2]],[[],[1],[1,1,2,1]]]

noncomputable def patterns_14_8_6 : List (List (List ℕ)) := [[[],[1],[1,2],[2]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]],[[],[1,1],[1,2,1]],[[],[1,1],[2],[2]],[[],[1,1,1],[1,2]],[[],[1,1,1,1],[2]],[[],[1,1,1,1,1,1]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1],[3]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,2,1]],[[1],[1],[2],[2]],[[1],[1,1],[1,1]]]

noncomputable def patterns_14_8_7 : List (List (List ℕ)) := [[[1],[1,1],[1,2]],[[1],[1,1,1],[2]],[[1],[1,1,1,1,1]],[[1,1],[1,1],[2]],[[1,1],[1,1,1,1]],[[1,1,1],[1,1,1]]]

noncomputable def patterns_14_8 : List (List (List ℕ)) := patterns_14_8_0 ++ (patterns_14_8_1 ++ (patterns_14_8_2 ++ (patterns_14_8_3 ++ (patterns_14_8_4 ++ (patterns_14_8_5 ++ (patterns_14_8_6 ++ (patterns_14_8_7 ++ ([]))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_15_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[],[6]],[[],[],[],[],[],[7]],[[],[],[],[],[],[8]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[1,5]],[[],[],[],[],[1,6]],[[],[],[],[],[1,7]]]

noncomputable def patterns_15_7_1 : List (List (List ℕ)) := [[[],[],[],[],[2,2]],[[],[],[],[],[2,3]],[[],[],[],[],[2,4]],[[],[],[],[],[2,5]],[[],[],[],[],[2,6]],[[],[],[],[],[3,3]],[[],[],[],[],[3,4]],[[],[],[],[],[3,5]],[[],[],[],[],[4,4]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]],[[],[],[],[1],[5]],[[],[],[],[1],[6]],[[],[],[],[1],[7]]]

noncomputable def patterns_15_7_2 : List (List (List ℕ)) := [[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,1,4]],[[],[],[],[1,1,5]],[[],[],[],[1,1,6]],[[],[],[],[1,2,1]],[[],[],[],[1,2,2]],[[],[],[],[1,2,3]],[[],[],[],[1,2,4]],[[],[],[],[1,2,5]],[[],[],[],[1,3,1]],[[],[],[],[1,3,2]],[[],[],[],[1,3,3]],[[],[],[],[1,3,4]],[[],[],[],[1,4,1]]]

noncomputable def patterns_15_7_3 : List (List (List ℕ)) := [[[],[],[],[1,4,2]],[[],[],[],[1,4,3]],[[],[],[],[1,5,1]],[[],[],[],[1,5,2]],[[],[],[],[1,6,1]],[[],[],[],[2],[2]],[[],[],[],[2],[3]],[[],[],[],[2],[4]],[[],[],[],[2],[5]],[[],[],[],[2],[6]],[[],[],[],[2,1,2]],[[],[],[],[2,1,3]],[[],[],[],[2,1,4]],[[],[],[],[2,1,5]],[[],[],[],[2,2,2]],[[],[],[],[2,2,3]]]

noncomputable def patterns_15_7_4 : List (List (List ℕ)) := [[[],[],[],[2,2,4]],[[],[],[],[2,3,2]],[[],[],[],[2,3,3]],[[],[],[],[2,4,2]],[[],[],[],[3],[3]],[[],[],[],[3],[4]],[[],[],[],[3],[5]],[[],[],[],[3,1,3]],[[],[],[],[3,1,4]],[[],[],[],[3,2,3]],[[],[],[],[4],[4]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[1,4]],[[],[],[1],[1,5]]]

noncomputable def patterns_15_7_5 : List (List (List ℕ)) := [[[],[],[1],[1,6]],[[],[],[1],[2,2]],[[],[],[1],[2,3]],[[],[],[1],[2,4]],[[],[],[1],[2,5]],[[],[],[1],[3,3]],[[],[],[1],[3,4]],[[],[],[1,1],[2]],[[],[],[1,1],[3]],[[],[],[1,1],[4]],[[],[],[1,1],[5]],[[],[],[1,1],[6]],[[],[],[1,1,1,1]],[[],[],[1,1,1,2]],[[],[],[1,1,1,3]],[[],[],[1,1,1,4]]]

noncomputable def patterns_15_7_6 : List (List (List ℕ)) := [[[],[],[1,1,1,5]],[[],[],[1,1,2,1]],[[],[],[1,1,2,2]],[[],[],[1,1,2,3]],[[],[],[1,1,2,4]],[[],[],[1,1,3,1]],[[],[],[1,1,3,2]],[[],[],[1,1,3,3]],[[],[],[1,1,4,1]],[[],[],[1,1,4,2]],[[],[],[1,1,5,1]],[[],[],[1,2],[2]],[[],[],[1,2],[3]],[[],[],[1,2],[4]],[[],[],[1,2],[5]],[[],[],[1,2,1,2]]]

noncomputable def patterns_15_7_7 : List (List (List ℕ)) := [[[],[],[1,2,1,3]],[[],[],[1,2,1,4]],[[],[],[1,2,2,1]],[[],[],[1,2,2,2]],[[],[],[1,2,2,3]],[[],[],[1,2,3,1]],[[],[],[1,2,3,2]],[[],[],[1,2,4,1]],[[],[],[1,3],[2]],[[],[],[1,3],[3]],[[],[],[1,3],[4]],[[],[],[1,3,1,2]],[[],[],[1,3,1,3]],[[],[],[1,3,2,2]],[[],[],[1,3,3,1]],[[],[],[1,4],[2]]]

noncomputable def patterns_15_7_8 : List (List (List ℕ)) := [[[],[],[1,4],[3]],[[],[],[1,4,1,2]],[[],[],[1,5],[2]],[[],[],[2],[2,2]],[[],[],[2],[2,3]],[[],[],[2],[2,4]],[[],[],[2],[3,3]],[[],[],[2,1,1,2]],[[],[],[2,1,1,3]],[[],[],[2,1,1,4]],[[],[],[2,1,2,2]],[[],[],[2,1,2,3]],[[],[],[2,1,3,2]],[[],[],[2,2],[3]],[[],[],[2,2],[4]],[[],[],[2,2,1,3]]]

noncomputable def patterns_15_7_9 : List (List (List ℕ)) := [[[],[],[2,2,2,2]],[[],[],[2,3],[3]],[[],[],[3,1,1,3]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1],[4]],[[],[1],[1],[5]],[[],[1],[1],[6]],[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,1,3]],[[],[1],[1,1,4]],[[],[1],[1,1,5]],[[],[1],[1,2,1]],[[],[1],[1,2,2]]]

noncomputable def patterns_15_7_10 : List (List (List ℕ)) := [[[],[1],[1,2,3]],[[],[1],[1,2,4]],[[],[1],[1,3,1]],[[],[1],[1,3,2]],[[],[1],[1,3,3]],[[],[1],[1,4,1]],[[],[1],[1,4,2]],[[],[1],[1,5,1]],[[],[1],[2],[2]],[[],[1],[2],[3]],[[],[1],[2],[4]],[[],[1],[2],[5]],[[],[1],[2,1,2]],[[],[1],[2,1,3]],[[],[1],[2,1,4]],[[],[1],[2,2,2]]]

noncomputable def patterns_15_7_11 : List (List (List ℕ)) := [[[],[1],[2,2,3]],[[],[1],[2,3,2]],[[],[1],[3],[3]],[[],[1],[3],[4]],[[],[1],[3,1,3]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1],[1,3]],[[],[1,1],[1,4]],[[],[1,1],[1,5]],[[],[1,1],[2,2]],[[],[1,1],[2,3]],[[],[1,1],[2,4]],[[],[1,1],[3,3]],[[],[1,1,1],[2]],[[],[1,1,1],[3]]]

noncomputable def patterns_15_7_12 : List (List (List ℕ)) := [[[],[1,1,1],[4]],[[],[1,1,1],[5]],[[],[1,1,1,1,1]],[[],[1,1,1,1,2]],[[],[1,1,1,1,3]],[[],[1,1,1,1,4]],[[],[1,1,1,2,1]],[[],[1,1,1,2,2]],[[],[1,1,1,2,3]],[[],[1,1,1,3,1]],[[],[1,1,1,3,2]],[[],[1,1,1,4,1]],[[],[1,1,2],[2]],[[],[1,1,2],[3]],[[],[1,1,2],[4]],[[],[1,1,2,1,1]]]

noncomputable def patterns_15_7_13 : List (List (List ℕ)) := [[[],[1,1,2,1,2]],[[],[1,1,2,1,3]],[[],[1,1,2,2,1]],[[],[1,1,2,2,2]],[[],[1,1,2,3,1]],[[],[1,1,3],[2]],[[],[1,1,3],[3]],[[],[1,1,3,1,1]],[[],[1,1,3,1,2]],[[],[1,1,3,2,1]],[[],[1,1,4],[2]],[[],[1,1,4,1,1]],[[],[1,2],[1,2]],[[],[1,2],[1,3]],[[],[1,2],[1,4]],[[],[1,2],[2,2]]]

noncomputable def patterns_15_7_14 : List (List (List ℕ)) := [[[],[1,2],[2,3]],[[],[1,2,1],[2]],[[],[1,2,1],[3]],[[],[1,2,1],[4]],[[],[1,2,1,1,2]],[[],[1,2,1,1,3]],[[],[1,2,1,2,1]],[[],[1,2,1,2,2]],[[],[1,2,1,3,1]],[[],[1,2,2],[2]],[[],[1,2,2],[3]],[[],[1,2,2,1,2]],[[],[1,2,2,2,1]],[[],[1,2,3],[2]],[[],[1,3],[1,3]],[[],[1,3],[2,2]]]

noncomputable def patterns_15_7_15 : List (List (List ℕ)) := [[[],[1,3,1],[2]],[[],[1,3,1],[3]],[[],[1,3,1,1,2]],[[],[1,3,2],[2]],[[],[1,4,1],[2]],[[],[2],[2],[2]],[[],[2],[2],[3]],[[],[2],[2],[4]],[[],[2],[2,1,2]],[[],[2],[2,1,3]],[[],[2],[2,2,2]],[[],[2],[3],[3]],[[],[2,1,1,1,2]],[[],[2,1,1,1,3]],[[],[2,1,1,2,2]],[[],[2,1,2],[3]]]

noncomputable def patterns_15_7_16 : List (List (List ℕ)) := [[[],[2,1,2,1,2]],[[],[2,2],[2,2]],[[1],[1],[1,1]],[[1],[1],[1,2]],[[1],[1],[1,3]],[[1],[1],[1,4]],[[1],[1],[1,5]],[[1],[1],[2,2]],[[1],[1],[2,3]],[[1],[1],[2,4]],[[1],[1],[3,3]],[[1],[1,1],[2]],[[1],[1,1],[3]],[[1],[1,1],[4]],[[1],[1,1],[5]],[[1],[1,1,1,1]]]

noncomputable def patterns_15_7_17 : List (List (List ℕ)) := [[[1],[1,1,1,2]],[[1],[1,1,1,3]],[[1],[1,1,1,4]],[[1],[1,1,2,1]],[[1],[1,1,2,2]],[[1],[1,1,2,3]],[[1],[1,1,3,1]],[[1],[1,1,3,2]],[[1],[1,1,4,1]],[[1],[1,2],[2]],[[1],[1,2],[3]],[[1],[1,2],[4]],[[1],[1,2,1,2]],[[1],[1,2,1,3]],[[1],[1,2,2,1]],[[1],[1,2,2,2]]]

noncomputable def patterns_15_7_18 : List (List (List ℕ)) := [[[1],[1,2,3,1]],[[1],[1,3],[2]],[[1],[1,3],[3]],[[1],[1,3,1,2]],[[1],[1,4],[2]],[[1],[2],[2,2]],[[1],[2],[2,3]],[[1],[2,1,1,2]],[[1],[2,1,1,3]],[[1],[2,1,2,2]],[[1],[2,2],[3]],[[1,1],[1,1,1]],[[1,1],[1,1,2]],[[1,1],[1,1,3]],[[1,1],[1,1,4]],[[1,1],[1,2,1]]]

noncomputable def patterns_15_7_19 : List (List (List ℕ)) := [[[1,1],[1,2,2]],[[1,1],[1,2,3]],[[1,1],[1,3,1]],[[1,1],[1,3,2]],[[1,1],[1,4,1]],[[1,1],[2],[2]],[[1,1],[2],[3]],[[1,1],[2],[4]],[[1,1],[2,1,2]],[[1,1],[2,1,3]],[[1,1],[2,2,2]],[[1,1],[3],[3]],[[1,1,1],[1,2]],[[1,1,1],[1,3]],[[1,1,1],[1,4]],[[1,1,1],[2,2]]]

noncomputable def patterns_15_7_20 : List (List (List ℕ)) := [[[1,1,1],[2,3]],[[1,1,1,1],[2]],[[1,1,1,1],[3]],[[1,1,1,1],[4]],[[1,1,1,1,1,1]],[[1,1,1,1,1,2]],[[1,1,1,1,1,3]],[[1,1,1,1,2,1]],[[1,1,1,1,2,2]],[[1,1,1,1,3,1]],[[1,1,1,2],[2]],[[1,1,1,2],[3]],[[1,1,1,2,1,1]],[[1,1,1,2,1,2]],[[1,1,1,2,2,1]],[[1,1,1,3],[2]]]

noncomputable def patterns_15_7_21 : List (List (List ℕ)) := [[[1,1,1,3,1,1]],[[1,1,2],[1,2]],[[1,1,2],[1,3]],[[1,1,2],[2,2]],[[1,1,2,1],[2]],[[1,1,2,1],[3]],[[1,1,2,1,1,2]],[[1,1,2,1,2,1]],[[1,1,2,2],[2]],[[1,1,2,2,1,1]],[[1,1,3],[1,2]],[[1,1,3,1],[2]],[[1,2],[1,2,1]],[[1,2],[1,2,2]],[[1,2],[1,3,1]],[[1,2],[2],[2]]]

noncomputable def patterns_15_7_22 : List (List (List ℕ)) := [[[1,2],[2],[3]],[[1,2],[2,1,2]],[[1,2,1],[1,3]],[[1,2,1],[2,2]],[[1,2,1,1,1,2]],[[1,2,1,1,2,1]],[[1,2,1,2],[2]],[[1,2,2,1],[2]],[[1,3],[2],[2]],[[2],[2],[2,2]],[[2],[2,1,1,2]],[[2,1,1,1,1,2]]]

noncomputable def patterns_15_7 : List (List (List ℕ)) := patterns_15_7_0 ++ (patterns_15_7_1 ++ (patterns_15_7_2 ++ (patterns_15_7_3 ++ (patterns_15_7_4 ++ (patterns_15_7_5 ++ (patterns_15_7_6 ++ (patterns_15_7_7 ++ (patterns_15_7_8 ++ (patterns_15_7_9 ++ (patterns_15_7_10 ++ (patterns_15_7_11 ++ (patterns_15_7_12 ++ (patterns_15_7_13 ++ (patterns_15_7_14 ++ (patterns_15_7_15 ++ (patterns_15_7_16 ++ (patterns_15_7_17 ++ (patterns_15_7_18 ++ (patterns_15_7_19 ++ (patterns_15_7_20 ++ (patterns_15_7_21 ++ (patterns_15_7_22 ++ ([])))))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_15_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[],[7]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[1,6]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]]]

noncomputable def patterns_15_8_1 : List (List (List ℕ)) := [[[],[],[],[],[],[2,4]],[[],[],[],[],[],[2,5]],[[],[],[],[],[],[3,3]],[[],[],[],[],[],[3,4]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1],[6]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,1,5]],[[],[],[],[],[1,2,1]]]

noncomputable def patterns_15_8_2 : List (List (List ℕ)) := [[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]],[[],[],[],[],[1,2,4]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,3,3]],[[],[],[],[],[1,4,1]],[[],[],[],[],[1,4,2]],[[],[],[],[],[1,5,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2],[5]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,1,4]]]

noncomputable def patterns_15_8_3 : List (List (List ℕ)) := [[[],[],[],[],[2,2,2]],[[],[],[],[],[2,2,3]],[[],[],[],[],[2,3,2]],[[],[],[],[],[3],[3]],[[],[],[],[],[3],[4]],[[],[],[],[],[3,1,3]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[1,5]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1],[2,4]],[[],[],[],[1],[3,3]],[[],[],[],[1,1],[2]]]

noncomputable def patterns_15_8_4 : List (List (List ℕ)) := [[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1],[5]],[[],[],[],[1,1,1,1]],[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,1,4]],[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,2,3]],[[],[],[],[1,1,3,1]],[[],[],[],[1,1,3,2]],[[],[],[],[1,1,4,1]],[[],[],[],[1,2],[2]],[[],[],[],[1,2],[3]],[[],[],[],[1,2],[4]]]

noncomputable def patterns_15_8_5 : List (List (List ℕ)) := [[[],[],[],[1,2,1,2]],[[],[],[],[1,2,1,3]],[[],[],[],[1,2,2,1]],[[],[],[],[1,2,2,2]],[[],[],[],[1,2,3,1]],[[],[],[],[1,3],[2]],[[],[],[],[1,3],[3]],[[],[],[],[1,3,1,2]],[[],[],[],[1,4],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2],[2,3]],[[],[],[],[2,1,1,2]],[[],[],[],[2,1,1,3]],[[],[],[],[2,1,2,2]],[[],[],[],[2,2],[3]],[[],[],[1],[1],[1]]]

noncomputable def patterns_15_8_6 : List (List (List ℕ)) := [[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]],[[],[],[1],[1],[5]],[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,1,4]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]],[[],[],[1],[1,2,3]],[[],[],[1],[1,3,1]],[[],[],[1],[1,3,2]],[[],[],[1],[1,4,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]]]

noncomputable def patterns_15_8_7 : List (List (List ℕ)) := [[[],[],[1],[2],[4]],[[],[],[1],[2,1,2]],[[],[],[1],[2,1,3]],[[],[],[1],[2,2,2]],[[],[],[1],[3],[3]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[1,4]],[[],[],[1,1],[2,2]],[[],[],[1,1],[2,3]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]],[[],[],[1,1,1],[4]],[[],[],[1,1,1,1,1]],[[],[],[1,1,1,1,2]]]

noncomputable def patterns_15_8_8 : List (List (List ℕ)) := [[[],[],[1,1,1,1,3]],[[],[],[1,1,1,2,1]],[[],[],[1,1,1,2,2]],[[],[],[1,1,1,3,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2],[3]],[[],[],[1,1,2,1,1]],[[],[],[1,1,2,1,2]],[[],[],[1,1,2,2,1]],[[],[],[1,1,3],[2]],[[],[],[1,1,3,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2],[1,3]],[[],[],[1,2],[2,2]],[[],[],[1,2,1],[2]],[[],[],[1,2,1],[3]]]

noncomputable def patterns_15_8_9 : List (List (List ℕ)) := [[[],[],[1,2,1,1,2]],[[],[],[1,2,1,2,1]],[[],[],[1,2,2],[2]],[[],[],[1,3,1],[2]],[[],[],[2],[2],[2]],[[],[],[2],[2],[3]],[[],[],[2],[2,1,2]],[[],[],[2,1,1,1,2]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[1,4]],[[],[1],[1],[2,2]],[[],[1],[1],[2,3]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]]]

noncomputable def patterns_15_8_10 : List (List (List ℕ)) := [[[],[1],[1,1],[4]],[[],[1],[1,1,1,1]],[[],[1],[1,1,1,2]],[[],[1],[1,1,1,3]],[[],[1],[1,1,2,1]],[[],[1],[1,1,2,2]],[[],[1],[1,1,3,1]],[[],[1],[1,2],[2]],[[],[1],[1,2],[3]],[[],[1],[1,2,1,2]],[[],[1],[1,2,2,1]],[[],[1],[1,3],[2]],[[],[1],[2],[2,2]],[[],[1],[2,1,1,2]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]]]

noncomputable def patterns_15_8_11 : List (List (List ℕ)) := [[[],[1,1],[1,1,3]],[[],[1,1],[1,2,1]],[[],[1,1],[1,2,2]],[[],[1,1],[1,3,1]],[[],[1,1],[2],[2]],[[],[1,1],[2],[3]],[[],[1,1],[2,1,2]],[[],[1,1,1],[1,2]],[[],[1,1,1],[1,3]],[[],[1,1,1],[2,2]],[[],[1,1,1,1],[2]],[[],[1,1,1,1],[3]],[[],[1,1,1,1,1,1]],[[],[1,1,1,1,1,2]],[[],[1,1,1,1,2,1]],[[],[1,1,1,2],[2]]]

noncomputable def patterns_15_8_12 : List (List (List ℕ)) := [[[],[1,1,1,2,1,1]],[[],[1,1,2],[1,2]],[[],[1,1,2,1],[2]],[[],[1,2],[1,2,1]],[[],[1,2],[2],[2]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1],[3]],[[1],[1],[1],[4]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,1,3]],[[1],[1],[1,2,1]],[[1],[1],[1,2,2]],[[1],[1],[1,3,1]],[[1],[1],[2],[2]]]

noncomputable def patterns_15_8_13 : List (List (List ℕ)) := [[[1],[1],[2],[3]],[[1],[1],[2,1,2]],[[1],[1,1],[1,1]],[[1],[1,1],[1,2]],[[1],[1,1],[1,3]],[[1],[1,1],[2,2]],[[1],[1,1,1],[2]],[[1],[1,1,1],[3]],[[1],[1,1,1,1,1]],[[1],[1,1,1,1,2]],[[1],[1,1,1,2,1]],[[1],[1,1,2],[2]],[[1],[1,1,2,1,1]],[[1],[1,2],[1,2]],[[1],[1,2,1],[2]],[[1],[2],[2],[2]]]

noncomputable def patterns_15_8_14 : List (List (List ℕ)) := [[[1,1],[1,1],[2]],[[1,1],[1,1],[3]],[[1,1],[1,1,1,1]],[[1,1],[1,1,1,2]],[[1,1],[1,1,2,1]],[[1,1],[1,2],[2]],[[1,1,1],[1,1,1]],[[1,1,1],[1,1,2]],[[1,1,1],[1,2,1]],[[1,1,1],[2],[2]],[[1,1,1,1],[1,2]],[[1,1,1,1,1],[2]],[[1,1,1,1,1,1,1]]]

noncomputable def patterns_15_8 : List (List (List ℕ)) := patterns_15_8_0 ++ (patterns_15_8_1 ++ (patterns_15_8_2 ++ (patterns_15_8_3 ++ (patterns_15_8_4 ++ (patterns_15_8_5 ++ (patterns_15_8_6 ++ (patterns_15_8_7 ++ (patterns_15_8_8 ++ (patterns_15_8_9 ++ (patterns_15_8_10 ++ (patterns_15_8_11 ++ (patterns_15_8_12 ++ (patterns_15_8_13 ++ (patterns_15_8_14 ++ ([])))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns16x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_16_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[],[7]],[[],[],[],[],[],[],[8]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[1,6]],[[],[],[],[],[],[1,7]]]

noncomputable def patterns_16_8_1 : List (List (List ℕ)) := [[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[],[2,4]],[[],[],[],[],[],[2,5]],[[],[],[],[],[],[2,6]],[[],[],[],[],[],[3,3]],[[],[],[],[],[],[3,4]],[[],[],[],[],[],[3,5]],[[],[],[],[],[],[4,4]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1],[6]],[[],[],[],[],[1],[7]]]

noncomputable def patterns_16_8_2 : List (List (List ℕ)) := [[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,1,5]],[[],[],[],[],[1,1,6]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]],[[],[],[],[],[1,2,4]],[[],[],[],[],[1,2,5]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,3,3]],[[],[],[],[],[1,3,4]],[[],[],[],[],[1,4,1]]]

noncomputable def patterns_16_8_3 : List (List (List ℕ)) := [[[],[],[],[],[1,4,2]],[[],[],[],[],[1,4,3]],[[],[],[],[],[1,5,1]],[[],[],[],[],[1,5,2]],[[],[],[],[],[1,6,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2],[5]],[[],[],[],[],[2],[6]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,1,4]],[[],[],[],[],[2,1,5]],[[],[],[],[],[2,2,2]],[[],[],[],[],[2,2,3]]]

noncomputable def patterns_16_8_4 : List (List (List ℕ)) := [[[],[],[],[],[2,2,4]],[[],[],[],[],[2,3,2]],[[],[],[],[],[2,3,3]],[[],[],[],[],[2,4,2]],[[],[],[],[],[3],[3]],[[],[],[],[],[3],[4]],[[],[],[],[],[3],[5]],[[],[],[],[],[3,1,3]],[[],[],[],[],[3,1,4]],[[],[],[],[],[3,2,3]],[[],[],[],[],[4],[4]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[1,5]]]

noncomputable def patterns_16_8_5 : List (List (List ℕ)) := [[[],[],[],[1],[1,6]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1],[2,4]],[[],[],[],[1],[2,5]],[[],[],[],[1],[3,3]],[[],[],[],[1],[3,4]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1],[5]],[[],[],[],[1,1],[6]],[[],[],[],[1,1,1,1]],[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,1,4]]]

noncomputable def patterns_16_8_6 : List (List (List ℕ)) := [[[],[],[],[1,1,1,5]],[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,2,3]],[[],[],[],[1,1,2,4]],[[],[],[],[1,1,3,1]],[[],[],[],[1,1,3,2]],[[],[],[],[1,1,3,3]],[[],[],[],[1,1,4,1]],[[],[],[],[1,1,4,2]],[[],[],[],[1,1,5,1]],[[],[],[],[1,2],[2]],[[],[],[],[1,2],[3]],[[],[],[],[1,2],[4]],[[],[],[],[1,2],[5]],[[],[],[],[1,2,1,2]]]

noncomputable def patterns_16_8_7 : List (List (List ℕ)) := [[[],[],[],[1,2,1,3]],[[],[],[],[1,2,1,4]],[[],[],[],[1,2,2,1]],[[],[],[],[1,2,2,2]],[[],[],[],[1,2,2,3]],[[],[],[],[1,2,3,1]],[[],[],[],[1,2,3,2]],[[],[],[],[1,2,4,1]],[[],[],[],[1,3],[2]],[[],[],[],[1,3],[3]],[[],[],[],[1,3],[4]],[[],[],[],[1,3,1,2]],[[],[],[],[1,3,1,3]],[[],[],[],[1,3,2,2]],[[],[],[],[1,3,3,1]],[[],[],[],[1,4],[2]]]

noncomputable def patterns_16_8_8 : List (List (List ℕ)) := [[[],[],[],[1,4],[3]],[[],[],[],[1,4,1,2]],[[],[],[],[1,5],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2],[2,3]],[[],[],[],[2],[2,4]],[[],[],[],[2],[3,3]],[[],[],[],[2,1,1,2]],[[],[],[],[2,1,1,3]],[[],[],[],[2,1,1,4]],[[],[],[],[2,1,2,2]],[[],[],[],[2,1,2,3]],[[],[],[],[2,1,3,2]],[[],[],[],[2,2],[3]],[[],[],[],[2,2],[4]],[[],[],[],[2,2,1,3]]]

noncomputable def patterns_16_8_9 : List (List (List ℕ)) := [[[],[],[],[2,2,2,2]],[[],[],[],[2,3],[3]],[[],[],[],[3,1,1,3]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]],[[],[],[1],[1],[5]],[[],[],[1],[1],[6]],[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,1,4]],[[],[],[1],[1,1,5]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]]]

noncomputable def patterns_16_8_10 : List (List (List ℕ)) := [[[],[],[1],[1,2,3]],[[],[],[1],[1,2,4]],[[],[],[1],[1,3,1]],[[],[],[1],[1,3,2]],[[],[],[1],[1,3,3]],[[],[],[1],[1,4,1]],[[],[],[1],[1,4,2]],[[],[],[1],[1,5,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]],[[],[],[1],[2],[4]],[[],[],[1],[2],[5]],[[],[],[1],[2,1,2]],[[],[],[1],[2,1,3]],[[],[],[1],[2,1,4]],[[],[],[1],[2,2,2]]]

noncomputable def patterns_16_8_11 : List (List (List ℕ)) := [[[],[],[1],[2,2,3]],[[],[],[1],[2,3,2]],[[],[],[1],[3],[3]],[[],[],[1],[3],[4]],[[],[],[1],[3,1,3]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[1,4]],[[],[],[1,1],[1,5]],[[],[],[1,1],[2,2]],[[],[],[1,1],[2,3]],[[],[],[1,1],[2,4]],[[],[],[1,1],[3,3]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]]]

noncomputable def patterns_16_8_12 : List (List (List ℕ)) := [[[],[],[1,1,1],[4]],[[],[],[1,1,1],[5]],[[],[],[1,1,1,1,1]],[[],[],[1,1,1,1,2]],[[],[],[1,1,1,1,3]],[[],[],[1,1,1,1,4]],[[],[],[1,1,1,2,1]],[[],[],[1,1,1,2,2]],[[],[],[1,1,1,2,3]],[[],[],[1,1,1,3,1]],[[],[],[1,1,1,3,2]],[[],[],[1,1,1,4,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2],[3]],[[],[],[1,1,2],[4]],[[],[],[1,1,2,1,1]]]

noncomputable def patterns_16_8_13 : List (List (List ℕ)) := [[[],[],[1,1,2,1,2]],[[],[],[1,1,2,1,3]],[[],[],[1,1,2,2,1]],[[],[],[1,1,2,2,2]],[[],[],[1,1,2,3,1]],[[],[],[1,1,3],[2]],[[],[],[1,1,3],[3]],[[],[],[1,1,3,1,1]],[[],[],[1,1,3,1,2]],[[],[],[1,1,3,2,1]],[[],[],[1,1,4],[2]],[[],[],[1,1,4,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2],[1,3]],[[],[],[1,2],[1,4]],[[],[],[1,2],[2,2]]]

noncomputable def patterns_16_8_14 : List (List (List ℕ)) := [[[],[],[1,2],[2,3]],[[],[],[1,2,1],[2]],[[],[],[1,2,1],[3]],[[],[],[1,2,1],[4]],[[],[],[1,2,1,1,2]],[[],[],[1,2,1,1,3]],[[],[],[1,2,1,2,1]],[[],[],[1,2,1,2,2]],[[],[],[1,2,1,3,1]],[[],[],[1,2,2],[2]],[[],[],[1,2,2],[3]],[[],[],[1,2,2,1,2]],[[],[],[1,2,2,2,1]],[[],[],[1,2,3],[2]],[[],[],[1,3],[1,3]],[[],[],[1,3],[2,2]]]

noncomputable def patterns_16_8_15 : List (List (List ℕ)) := [[[],[],[1,3,1],[2]],[[],[],[1,3,1],[3]],[[],[],[1,3,1,1,2]],[[],[],[1,3,2],[2]],[[],[],[1,4,1],[2]],[[],[],[2],[2],[2]],[[],[],[2],[2],[3]],[[],[],[2],[2],[4]],[[],[],[2],[2,1,2]],[[],[],[2],[2,1,3]],[[],[],[2],[2,2,2]],[[],[],[2],[3],[3]],[[],[],[2,1,1,1,2]],[[],[],[2,1,1,1,3]],[[],[],[2,1,1,2,2]],[[],[],[2,1,2],[3]]]

noncomputable def patterns_16_8_16 : List (List (List ℕ)) := [[[],[],[2,1,2,1,2]],[[],[],[2,2],[2,2]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[1,4]],[[],[1],[1],[1,5]],[[],[1],[1],[2,2]],[[],[1],[1],[2,3]],[[],[1],[1],[2,4]],[[],[1],[1],[3,3]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]],[[],[1],[1,1],[4]],[[],[1],[1,1],[5]],[[],[1],[1,1,1,1]]]

noncomputable def patterns_16_8_17 : List (List (List ℕ)) := [[[],[1],[1,1,1,2]],[[],[1],[1,1,1,3]],[[],[1],[1,1,1,4]],[[],[1],[1,1,2,1]],[[],[1],[1,1,2,2]],[[],[1],[1,1,2,3]],[[],[1],[1,1,3,1]],[[],[1],[1,1,3,2]],[[],[1],[1,1,4,1]],[[],[1],[1,2],[2]],[[],[1],[1,2],[3]],[[],[1],[1,2],[4]],[[],[1],[1,2,1,2]],[[],[1],[1,2,1,3]],[[],[1],[1,2,2,1]],[[],[1],[1,2,2,2]]]

noncomputable def patterns_16_8_18 : List (List (List ℕ)) := [[[],[1],[1,2,3,1]],[[],[1],[1,3],[2]],[[],[1],[1,3],[3]],[[],[1],[1,3,1,2]],[[],[1],[1,4],[2]],[[],[1],[2],[2,2]],[[],[1],[2],[2,3]],[[],[1],[2,1,1,2]],[[],[1],[2,1,1,3]],[[],[1],[2,1,2,2]],[[],[1],[2,2],[3]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]],[[],[1,1],[1,1,3]],[[],[1,1],[1,1,4]],[[],[1,1],[1,2,1]]]

noncomputable def patterns_16_8_19 : List (List (List ℕ)) := [[[],[1,1],[1,2,2]],[[],[1,1],[1,2,3]],[[],[1,1],[1,3,1]],[[],[1,1],[1,3,2]],[[],[1,1],[1,4,1]],[[],[1,1],[2],[2]],[[],[1,1],[2],[3]],[[],[1,1],[2],[4]],[[],[1,1],[2,1,2]],[[],[1,1],[2,1,3]],[[],[1,1],[2,2,2]],[[],[1,1],[3],[3]],[[],[1,1,1],[1,2]],[[],[1,1,1],[1,3]],[[],[1,1,1],[1,4]],[[],[1,1,1],[2,2]]]

noncomputable def patterns_16_8_20 : List (List (List ℕ)) := [[[],[1,1,1],[2,3]],[[],[1,1,1,1],[2]],[[],[1,1,1,1],[3]],[[],[1,1,1,1],[4]],[[],[1,1,1,1,1,1]],[[],[1,1,1,1,1,2]],[[],[1,1,1,1,1,3]],[[],[1,1,1,1,2,1]],[[],[1,1,1,1,2,2]],[[],[1,1,1,1,3,1]],[[],[1,1,1,2],[2]],[[],[1,1,1,2],[3]],[[],[1,1,1,2,1,1]],[[],[1,1,1,2,1,2]],[[],[1,1,1,2,2,1]],[[],[1,1,1,3],[2]]]

noncomputable def patterns_16_8_21 : List (List (List ℕ)) := [[[],[1,1,1,3,1,1]],[[],[1,1,2],[1,2]],[[],[1,1,2],[1,3]],[[],[1,1,2],[2,2]],[[],[1,1,2,1],[2]],[[],[1,1,2,1],[3]],[[],[1,1,2,1,1,2]],[[],[1,1,2,1,2,1]],[[],[1,1,2,2],[2]],[[],[1,1,2,2,1,1]],[[],[1,1,3],[1,2]],[[],[1,1,3,1],[2]],[[],[1,2],[1,2,1]],[[],[1,2],[1,2,2]],[[],[1,2],[1,3,1]],[[],[1,2],[2],[2]]]

noncomputable def patterns_16_8_22 : List (List (List ℕ)) := [[[],[1,2],[2],[3]],[[],[1,2],[2,1,2]],[[],[1,2,1],[1,3]],[[],[1,2,1],[2,2]],[[],[1,2,1,1,1,2]],[[],[1,2,1,1,2,1]],[[],[1,2,1,2],[2]],[[],[1,2,2,1],[2]],[[],[1,3],[2],[2]],[[],[2],[2],[2,2]],[[],[2],[2,1,1,2]],[[],[2,1,1,1,1,2]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1],[3]],[[1],[1],[1],[4]]]

noncomputable def patterns_16_8_23 : List (List (List ℕ)) := [[[1],[1],[1],[5]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,1,3]],[[1],[1],[1,1,4]],[[1],[1],[1,2,1]],[[1],[1],[1,2,2]],[[1],[1],[1,2,3]],[[1],[1],[1,3,1]],[[1],[1],[1,3,2]],[[1],[1],[1,4,1]],[[1],[1],[2],[2]],[[1],[1],[2],[3]],[[1],[1],[2],[4]],[[1],[1],[2,1,2]],[[1],[1],[2,1,3]]]

noncomputable def patterns_16_8_24 : List (List (List ℕ)) := [[[1],[1],[2,2,2]],[[1],[1],[3],[3]],[[1],[1,1],[1,1]],[[1],[1,1],[1,2]],[[1],[1,1],[1,3]],[[1],[1,1],[1,4]],[[1],[1,1],[2,2]],[[1],[1,1],[2,3]],[[1],[1,1,1],[2]],[[1],[1,1,1],[3]],[[1],[1,1,1],[4]],[[1],[1,1,1,1,1]],[[1],[1,1,1,1,2]],[[1],[1,1,1,1,3]],[[1],[1,1,1,2,1]],[[1],[1,1,1,2,2]]]

noncomputable def patterns_16_8_25 : List (List (List ℕ)) := [[[1],[1,1,1,3,1]],[[1],[1,1,2],[2]],[[1],[1,1,2],[3]],[[1],[1,1,2,1,1]],[[1],[1,1,2,1,2]],[[1],[1,1,2,2,1]],[[1],[1,1,3],[2]],[[1],[1,1,3,1,1]],[[1],[1,2],[1,2]],[[1],[1,2],[1,3]],[[1],[1,2],[2,2]],[[1],[1,2,1],[2]],[[1],[1,2,1],[3]],[[1],[1,2,1,1,2]],[[1],[1,2,1,2,1]],[[1],[1,2,2],[2]]]

noncomputable def patterns_16_8_26 : List (List (List ℕ)) := [[[1],[1,3,1],[2]],[[1],[2],[2],[2]],[[1],[2],[2],[3]],[[1],[2],[2,1,2]],[[1],[2,1,1,1,2]],[[1,1],[1,1],[2]],[[1,1],[1,1],[3]],[[1,1],[1,1],[4]],[[1,1],[1,1,1,1]],[[1,1],[1,1,1,2]],[[1,1],[1,1,1,3]],[[1,1],[1,1,2,1]],[[1,1],[1,1,2,2]],[[1,1],[1,1,3,1]],[[1,1],[1,2],[2]],[[1,1],[1,2],[3]]]

noncomputable def patterns_16_8_27 : List (List (List ℕ)) := [[[1,1],[1,2,1,2]],[[1,1],[1,2,2,1]],[[1,1],[1,3],[2]],[[1,1],[2],[2,2]],[[1,1],[2,1,1,2]],[[1,1,1],[1,1,1]],[[1,1,1],[1,1,2]],[[1,1,1],[1,1,3]],[[1,1,1],[1,2,1]],[[1,1,1],[1,2,2]],[[1,1,1],[1,3,1]],[[1,1,1],[2],[2]],[[1,1,1],[2],[3]],[[1,1,1],[2,1,2]],[[1,1,1,1],[1,2]],[[1,1,1,1],[1,3]]]

noncomputable def patterns_16_8_28 : List (List (List ℕ)) := [[[1,1,1,1],[2,2]],[[1,1,1,1,1],[2]],[[1,1,1,1,1],[3]],[[1,1,1,1,1,1,1]],[[1,1,1,1,1,1,2]],[[1,1,1,1,1,2,1]],[[1,1,1,1,2],[2]],[[1,1,1,1,2,1,1]],[[1,1,1,2],[1,2]],[[1,1,1,2,1],[2]],[[1,1,1,2,1,1,1]],[[1,1,2],[1,1,2]],[[1,1,2],[1,2,1]],[[1,1,2],[2],[2]],[[1,1,2,1],[1,2]],[[1,1,2,1,1],[2]]]

noncomputable def patterns_16_8_29 : List (List (List ℕ)) := [[[1,2],[1,2],[2]],[[1,2,1],[1,2,1]],[[1,2,1],[2],[2]],[[2],[2],[2],[2]]]

noncomputable def patterns_16_8 : List (List (List ℕ)) := patterns_16_8_0 ++ (patterns_16_8_1 ++ (patterns_16_8_2 ++ (patterns_16_8_3 ++ (patterns_16_8_4 ++ (patterns_16_8_5 ++ (patterns_16_8_6 ++ (patterns_16_8_7 ++ (patterns_16_8_8 ++ (patterns_16_8_9 ++ (patterns_16_8_10 ++ (patterns_16_8_11 ++ (patterns_16_8_12 ++ (patterns_16_8_13 ++ (patterns_16_8_14 ++ (patterns_16_8_15 ++ (patterns_16_8_16 ++ (patterns_16_8_17 ++ (patterns_16_8_18 ++ (patterns_16_8_19 ++ (patterns_16_8_20 ++ (patterns_16_8_21 ++ (patterns_16_8_22 ++ (patterns_16_8_23 ++ (patterns_16_8_24 ++ (patterns_16_8_25 ++ (patterns_16_8_26 ++ (patterns_16_8_27 ++ (patterns_16_8_28 ++ (patterns_16_8_29 ++ ([]))))))))))))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns17x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_17_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[],[7]],[[],[],[],[],[],[],[8]],[[],[],[],[],[],[],[9]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[1,6]]]

noncomputable def patterns_17_8_1 : List (List (List ℕ)) := [[[],[],[],[],[],[1,7]],[[],[],[],[],[],[1,8]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[],[2,4]],[[],[],[],[],[],[2,5]],[[],[],[],[],[],[2,6]],[[],[],[],[],[],[2,7]],[[],[],[],[],[],[3,3]],[[],[],[],[],[],[3,4]],[[],[],[],[],[],[3,5]],[[],[],[],[],[],[3,6]],[[],[],[],[],[],[4,4]],[[],[],[],[],[],[4,5]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]]]

noncomputable def patterns_17_8_2 : List (List (List ℕ)) := [[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1],[6]],[[],[],[],[],[1],[7]],[[],[],[],[],[1],[8]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,1,5]],[[],[],[],[],[1,1,6]],[[],[],[],[],[1,1,7]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]]]

noncomputable def patterns_17_8_3 : List (List (List ℕ)) := [[[],[],[],[],[1,2,4]],[[],[],[],[],[1,2,5]],[[],[],[],[],[1,2,6]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,3,3]],[[],[],[],[],[1,3,4]],[[],[],[],[],[1,3,5]],[[],[],[],[],[1,4,1]],[[],[],[],[],[1,4,2]],[[],[],[],[],[1,4,3]],[[],[],[],[],[1,4,4]],[[],[],[],[],[1,5,1]],[[],[],[],[],[1,5,2]],[[],[],[],[],[1,5,3]],[[],[],[],[],[1,6,1]]]

noncomputable def patterns_17_8_4 : List (List (List ℕ)) := [[[],[],[],[],[1,6,2]],[[],[],[],[],[1,7,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2],[5]],[[],[],[],[],[2],[6]],[[],[],[],[],[2],[7]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,1,4]],[[],[],[],[],[2,1,5]],[[],[],[],[],[2,1,6]],[[],[],[],[],[2,2,2]],[[],[],[],[],[2,2,3]],[[],[],[],[],[2,2,4]]]

noncomputable def patterns_17_8_5 : List (List (List ℕ)) := [[[],[],[],[],[2,2,5]],[[],[],[],[],[2,3,2]],[[],[],[],[],[2,3,3]],[[],[],[],[],[2,3,4]],[[],[],[],[],[2,4,2]],[[],[],[],[],[2,4,3]],[[],[],[],[],[2,5,2]],[[],[],[],[],[3],[3]],[[],[],[],[],[3],[4]],[[],[],[],[],[3],[5]],[[],[],[],[],[3],[6]],[[],[],[],[],[3,1,3]],[[],[],[],[],[3,1,4]],[[],[],[],[],[3,1,5]],[[],[],[],[],[3,2,3]],[[],[],[],[],[3,2,4]]]

noncomputable def patterns_17_8_6 : List (List (List ℕ)) := [[[],[],[],[],[3,3,3]],[[],[],[],[],[4],[4]],[[],[],[],[],[4],[5]],[[],[],[],[],[4,1,4]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[1,5]],[[],[],[],[1],[1,6]],[[],[],[],[1],[1,7]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1],[2,4]],[[],[],[],[1],[2,5]],[[],[],[],[1],[2,6]]]

noncomputable def patterns_17_8_7 : List (List (List ℕ)) := [[[],[],[],[1],[3,3]],[[],[],[],[1],[3,4]],[[],[],[],[1],[3,5]],[[],[],[],[1],[4,4]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1],[5]],[[],[],[],[1,1],[6]],[[],[],[],[1,1],[7]],[[],[],[],[1,1,1,1]],[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,1,4]],[[],[],[],[1,1,1,5]],[[],[],[],[1,1,1,6]]]

noncomputable def patterns_17_8_8 : List (List (List ℕ)) := [[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,2,3]],[[],[],[],[1,1,2,4]],[[],[],[],[1,1,2,5]],[[],[],[],[1,1,3,1]],[[],[],[],[1,1,3,2]],[[],[],[],[1,1,3,3]],[[],[],[],[1,1,3,4]],[[],[],[],[1,1,4,1]],[[],[],[],[1,1,4,2]],[[],[],[],[1,1,4,3]],[[],[],[],[1,1,5,1]],[[],[],[],[1,1,5,2]],[[],[],[],[1,1,6,1]],[[],[],[],[1,2],[2]]]

noncomputable def patterns_17_8_9 : List (List (List ℕ)) := [[[],[],[],[1,2],[3]],[[],[],[],[1,2],[4]],[[],[],[],[1,2],[5]],[[],[],[],[1,2],[6]],[[],[],[],[1,2,1,2]],[[],[],[],[1,2,1,3]],[[],[],[],[1,2,1,4]],[[],[],[],[1,2,1,5]],[[],[],[],[1,2,2,1]],[[],[],[],[1,2,2,2]],[[],[],[],[1,2,2,3]],[[],[],[],[1,2,2,4]],[[],[],[],[1,2,3,1]],[[],[],[],[1,2,3,2]],[[],[],[],[1,2,3,3]],[[],[],[],[1,2,4,1]]]

noncomputable def patterns_17_8_10 : List (List (List ℕ)) := [[[],[],[],[1,2,4,2]],[[],[],[],[1,2,5,1]],[[],[],[],[1,3],[2]],[[],[],[],[1,3],[3]],[[],[],[],[1,3],[4]],[[],[],[],[1,3],[5]],[[],[],[],[1,3,1,2]],[[],[],[],[1,3,1,3]],[[],[],[],[1,3,1,4]],[[],[],[],[1,3,2,2]],[[],[],[],[1,3,2,3]],[[],[],[],[1,3,3,1]],[[],[],[],[1,3,3,2]],[[],[],[],[1,3,4,1]],[[],[],[],[1,4],[2]],[[],[],[],[1,4],[3]]]

noncomputable def patterns_17_8_11 : List (List (List ℕ)) := [[[],[],[],[1,4],[4]],[[],[],[],[1,4,1,2]],[[],[],[],[1,4,1,3]],[[],[],[],[1,4,2,2]],[[],[],[],[1,5],[2]],[[],[],[],[1,5],[3]],[[],[],[],[1,5,1,2]],[[],[],[],[1,6],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2],[2,3]],[[],[],[],[2],[2,4]],[[],[],[],[2],[2,5]],[[],[],[],[2],[3,3]],[[],[],[],[2],[3,4]],[[],[],[],[2,1,1,2]],[[],[],[],[2,1,1,3]]]

noncomputable def patterns_17_8_12 : List (List (List ℕ)) := [[[],[],[],[2,1,1,4]],[[],[],[],[2,1,1,5]],[[],[],[],[2,1,2,2]],[[],[],[],[2,1,2,3]],[[],[],[],[2,1,2,4]],[[],[],[],[2,1,3,2]],[[],[],[],[2,1,3,3]],[[],[],[],[2,1,4,2]],[[],[],[],[2,2],[3]],[[],[],[],[2,2],[4]],[[],[],[],[2,2],[5]],[[],[],[],[2,2,1,3]],[[],[],[],[2,2,1,4]],[[],[],[],[2,2,2,2]],[[],[],[],[2,2,2,3]],[[],[],[],[2,2,3,2]]]

noncomputable def patterns_17_8_13 : List (List (List ℕ)) := [[[],[],[],[2,3],[3]],[[],[],[],[2,3],[4]],[[],[],[],[2,3,1,3]],[[],[],[],[2,4],[3]],[[],[],[],[3],[3,3]],[[],[],[],[3,1,1,3]],[[],[],[],[3,1,1,4]],[[],[],[],[3,1,2,3]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]],[[],[],[1],[1],[5]],[[],[],[1],[1],[6]],[[],[],[1],[1],[7]],[[],[],[1],[1,1,1]]]

noncomputable def patterns_17_8_14 : List (List (List ℕ)) := [[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,1,4]],[[],[],[1],[1,1,5]],[[],[],[1],[1,1,6]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]],[[],[],[1],[1,2,3]],[[],[],[1],[1,2,4]],[[],[],[1],[1,2,5]],[[],[],[1],[1,3,1]],[[],[],[1],[1,3,2]],[[],[],[1],[1,3,3]],[[],[],[1],[1,3,4]],[[],[],[1],[1,4,1]],[[],[],[1],[1,4,2]]]

noncomputable def patterns_17_8_15 : List (List (List ℕ)) := [[[],[],[1],[1,4,3]],[[],[],[1],[1,5,1]],[[],[],[1],[1,5,2]],[[],[],[1],[1,6,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]],[[],[],[1],[2],[4]],[[],[],[1],[2],[5]],[[],[],[1],[2],[6]],[[],[],[1],[2,1,2]],[[],[],[1],[2,1,3]],[[],[],[1],[2,1,4]],[[],[],[1],[2,1,5]],[[],[],[1],[2,2,2]],[[],[],[1],[2,2,3]],[[],[],[1],[2,2,4]]]

noncomputable def patterns_17_8_16 : List (List (List ℕ)) := [[[],[],[1],[2,3,2]],[[],[],[1],[2,3,3]],[[],[],[1],[2,4,2]],[[],[],[1],[3],[3]],[[],[],[1],[3],[4]],[[],[],[1],[3],[5]],[[],[],[1],[3,1,3]],[[],[],[1],[3,1,4]],[[],[],[1],[3,2,3]],[[],[],[1],[4],[4]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[1,4]],[[],[],[1,1],[1,5]],[[],[],[1,1],[1,6]]]

noncomputable def patterns_17_8_17 : List (List (List ℕ)) := [[[],[],[1,1],[2,2]],[[],[],[1,1],[2,3]],[[],[],[1,1],[2,4]],[[],[],[1,1],[2,5]],[[],[],[1,1],[3,3]],[[],[],[1,1],[3,4]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]],[[],[],[1,1,1],[4]],[[],[],[1,1,1],[5]],[[],[],[1,1,1],[6]],[[],[],[1,1,1,1,1]],[[],[],[1,1,1,1,2]],[[],[],[1,1,1,1,3]],[[],[],[1,1,1,1,4]],[[],[],[1,1,1,1,5]]]

noncomputable def patterns_17_8_18 : List (List (List ℕ)) := [[[],[],[1,1,1,2,1]],[[],[],[1,1,1,2,2]],[[],[],[1,1,1,2,3]],[[],[],[1,1,1,2,4]],[[],[],[1,1,1,3,1]],[[],[],[1,1,1,3,2]],[[],[],[1,1,1,3,3]],[[],[],[1,1,1,4,1]],[[],[],[1,1,1,4,2]],[[],[],[1,1,1,5,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2],[3]],[[],[],[1,1,2],[4]],[[],[],[1,1,2],[5]],[[],[],[1,1,2,1,1]],[[],[],[1,1,2,1,2]]]

noncomputable def patterns_17_8_19 : List (List (List ℕ)) := [[[],[],[1,1,2,1,3]],[[],[],[1,1,2,1,4]],[[],[],[1,1,2,2,1]],[[],[],[1,1,2,2,2]],[[],[],[1,1,2,2,3]],[[],[],[1,1,2,3,1]],[[],[],[1,1,2,3,2]],[[],[],[1,1,2,4,1]],[[],[],[1,1,3],[2]],[[],[],[1,1,3],[3]],[[],[],[1,1,3],[4]],[[],[],[1,1,3,1,1]],[[],[],[1,1,3,1,2]],[[],[],[1,1,3,1,3]],[[],[],[1,1,3,2,1]],[[],[],[1,1,3,2,2]]]

noncomputable def patterns_17_8_20 : List (List (List ℕ)) := [[[],[],[1,1,3,3,1]],[[],[],[1,1,4],[2]],[[],[],[1,1,4],[3]],[[],[],[1,1,4,1,1]],[[],[],[1,1,4,1,2]],[[],[],[1,1,4,2,1]],[[],[],[1,1,5],[2]],[[],[],[1,1,5,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2],[1,3]],[[],[],[1,2],[1,4]],[[],[],[1,2],[1,5]],[[],[],[1,2],[2,2]],[[],[],[1,2],[2,3]],[[],[],[1,2],[2,4]],[[],[],[1,2],[3,3]]]

noncomputable def patterns_17_8_21 : List (List (List ℕ)) := [[[],[],[1,2,1],[2]],[[],[],[1,2,1],[3]],[[],[],[1,2,1],[4]],[[],[],[1,2,1],[5]],[[],[],[1,2,1,1,2]],[[],[],[1,2,1,1,3]],[[],[],[1,2,1,1,4]],[[],[],[1,2,1,2,1]],[[],[],[1,2,1,2,2]],[[],[],[1,2,1,2,3]],[[],[],[1,2,1,3,1]],[[],[],[1,2,1,3,2]],[[],[],[1,2,1,4,1]],[[],[],[1,2,2],[2]],[[],[],[1,2,2],[3]],[[],[],[1,2,2],[4]]]

noncomputable def patterns_17_8_22 : List (List (List ℕ)) := [[[],[],[1,2,2,1,2]],[[],[],[1,2,2,1,3]],[[],[],[1,2,2,2,1]],[[],[],[1,2,2,2,2]],[[],[],[1,2,2,3,1]],[[],[],[1,2,3],[2]],[[],[],[1,2,3],[3]],[[],[],[1,2,3,1,2]],[[],[],[1,2,3,2,1]],[[],[],[1,2,4],[2]],[[],[],[1,3],[1,3]],[[],[],[1,3],[1,4]],[[],[],[1,3],[2,2]],[[],[],[1,3],[2,3]],[[],[],[1,3,1],[2]],[[],[],[1,3,1],[3]]]

noncomputable def patterns_17_8_23 : List (List (List ℕ)) := [[[],[],[1,3,1],[4]],[[],[],[1,3,1,1,2]],[[],[],[1,3,1,1,3]],[[],[],[1,3,1,2,2]],[[],[],[1,3,1,3,1]],[[],[],[1,3,2],[2]],[[],[],[1,3,2],[3]],[[],[],[1,3,2,1,2]],[[],[],[1,3,3],[2]],[[],[],[1,4],[2,2]],[[],[],[1,4,1],[2]],[[],[],[1,4,1],[3]],[[],[],[1,4,1,1,2]],[[],[],[1,4,2],[2]],[[],[],[1,5,1],[2]],[[],[],[2],[2],[2]]]

noncomputable def patterns_17_8_24 : List (List (List ℕ)) := [[[],[],[2],[2],[3]],[[],[],[2],[2],[4]],[[],[],[2],[2],[5]],[[],[],[2],[2,1,2]],[[],[],[2],[2,1,3]],[[],[],[2],[2,1,4]],[[],[],[2],[2,2,2]],[[],[],[2],[2,2,3]],[[],[],[2],[2,3,2]],[[],[],[2],[3],[3]],[[],[],[2],[3],[4]],[[],[],[2],[3,1,3]],[[],[],[2,1,1,1,2]],[[],[],[2,1,1,1,3]],[[],[],[2,1,1,1,4]],[[],[],[2,1,1,2,2]]]

noncomputable def patterns_17_8_25 : List (List (List ℕ)) := [[[],[],[2,1,1,2,3]],[[],[],[2,1,1,3,2]],[[],[],[2,1,2],[3]],[[],[],[2,1,2],[4]],[[],[],[2,1,2,1,2]],[[],[],[2,1,2,1,3]],[[],[],[2,1,2,2,2]],[[],[],[2,1,3],[3]],[[],[],[2,1,3,1,2]],[[],[],[2,2],[2,2]],[[],[],[2,2],[2,3]],[[],[],[2,2,1,1,3]],[[],[],[2,2,1,2,2]],[[],[],[2,2,2],[3]],[[],[],[3],[3],[3]],[[],[],[3,1,1,1,3]]]

noncomputable def patterns_17_8_26 : List (List (List ℕ)) := [[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[1,4]],[[],[1],[1],[1,5]],[[],[1],[1],[1,6]],[[],[1],[1],[2,2]],[[],[1],[1],[2,3]],[[],[1],[1],[2,4]],[[],[1],[1],[2,5]],[[],[1],[1],[3,3]],[[],[1],[1],[3,4]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]],[[],[1],[1,1],[4]],[[],[1],[1,1],[5]]]

noncomputable def patterns_17_8_27 : List (List (List ℕ)) := [[[],[1],[1,1],[6]],[[],[1],[1,1,1,1]],[[],[1],[1,1,1,2]],[[],[1],[1,1,1,3]],[[],[1],[1,1,1,4]],[[],[1],[1,1,1,5]],[[],[1],[1,1,2,1]],[[],[1],[1,1,2,2]],[[],[1],[1,1,2,3]],[[],[1],[1,1,2,4]],[[],[1],[1,1,3,1]],[[],[1],[1,1,3,2]],[[],[1],[1,1,3,3]],[[],[1],[1,1,4,1]],[[],[1],[1,1,4,2]],[[],[1],[1,1,5,1]]]

noncomputable def patterns_17_8_28 : List (List (List ℕ)) := [[[],[1],[1,2],[2]],[[],[1],[1,2],[3]],[[],[1],[1,2],[4]],[[],[1],[1,2],[5]],[[],[1],[1,2,1,2]],[[],[1],[1,2,1,3]],[[],[1],[1,2,1,4]],[[],[1],[1,2,2,1]],[[],[1],[1,2,2,2]],[[],[1],[1,2,2,3]],[[],[1],[1,2,3,1]],[[],[1],[1,2,3,2]],[[],[1],[1,2,4,1]],[[],[1],[1,3],[2]],[[],[1],[1,3],[3]],[[],[1],[1,3],[4]]]

noncomputable def patterns_17_8_29 : List (List (List ℕ)) := [[[],[1],[1,3,1,2]],[[],[1],[1,3,1,3]],[[],[1],[1,3,2,2]],[[],[1],[1,3,3,1]],[[],[1],[1,4],[2]],[[],[1],[1,4],[3]],[[],[1],[1,4,1,2]],[[],[1],[1,5],[2]],[[],[1],[2],[2,2]],[[],[1],[2],[2,3]],[[],[1],[2],[2,4]],[[],[1],[2],[3,3]],[[],[1],[2,1,1,2]],[[],[1],[2,1,1,3]],[[],[1],[2,1,1,4]],[[],[1],[2,1,2,2]]]

noncomputable def patterns_17_8_30 : List (List (List ℕ)) := [[[],[1],[2,1,2,3]],[[],[1],[2,1,3,2]],[[],[1],[2,2],[3]],[[],[1],[2,2],[4]],[[],[1],[2,2,1,3]],[[],[1],[2,2,2,2]],[[],[1],[2,3],[3]],[[],[1],[3,1,1,3]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]],[[],[1,1],[1,1,3]],[[],[1,1],[1,1,4]],[[],[1,1],[1,1,5]],[[],[1,1],[1,2,1]],[[],[1,1],[1,2,2]],[[],[1,1],[1,2,3]]]

noncomputable def patterns_17_8_31 : List (List (List ℕ)) := [[[],[1,1],[1,2,4]],[[],[1,1],[1,3,1]],[[],[1,1],[1,3,2]],[[],[1,1],[1,3,3]],[[],[1,1],[1,4,1]],[[],[1,1],[1,4,2]],[[],[1,1],[1,5,1]],[[],[1,1],[2],[2]],[[],[1,1],[2],[3]],[[],[1,1],[2],[4]],[[],[1,1],[2],[5]],[[],[1,1],[2,1,2]],[[],[1,1],[2,1,3]],[[],[1,1],[2,1,4]],[[],[1,1],[2,2,2]],[[],[1,1],[2,2,3]]]

noncomputable def patterns_17_8_32 : List (List (List ℕ)) := [[[],[1,1],[2,3,2]],[[],[1,1],[3],[3]],[[],[1,1],[3],[4]],[[],[1,1],[3,1,3]],[[],[1,1,1],[1,2]],[[],[1,1,1],[1,3]],[[],[1,1,1],[1,4]],[[],[1,1,1],[1,5]],[[],[1,1,1],[2,2]],[[],[1,1,1],[2,3]],[[],[1,1,1],[2,4]],[[],[1,1,1],[3,3]],[[],[1,1,1,1],[2]],[[],[1,1,1,1],[3]],[[],[1,1,1,1],[4]],[[],[1,1,1,1],[5]]]

noncomputable def patterns_17_8_33 : List (List (List ℕ)) := [[[],[1,1,1,1,1,1]],[[],[1,1,1,1,1,2]],[[],[1,1,1,1,1,3]],[[],[1,1,1,1,1,4]],[[],[1,1,1,1,2,1]],[[],[1,1,1,1,2,2]],[[],[1,1,1,1,2,3]],[[],[1,1,1,1,3,1]],[[],[1,1,1,1,3,2]],[[],[1,1,1,1,4,1]],[[],[1,1,1,2],[2]],[[],[1,1,1,2],[3]],[[],[1,1,1,2],[4]],[[],[1,1,1,2,1,1]],[[],[1,1,1,2,1,2]],[[],[1,1,1,2,1,3]]]

noncomputable def patterns_17_8_34 : List (List (List ℕ)) := [[[],[1,1,1,2,2,1]],[[],[1,1,1,2,2,2]],[[],[1,1,1,2,3,1]],[[],[1,1,1,3],[2]],[[],[1,1,1,3],[3]],[[],[1,1,1,3,1,1]],[[],[1,1,1,3,1,2]],[[],[1,1,1,3,2,1]],[[],[1,1,1,4],[2]],[[],[1,1,1,4,1,1]],[[],[1,1,2],[1,2]],[[],[1,1,2],[1,3]],[[],[1,1,2],[1,4]],[[],[1,1,2],[2,2]],[[],[1,1,2],[2,3]],[[],[1,1,2,1],[2]]]

noncomputable def patterns_17_8_35 : List (List (List ℕ)) := [[[],[1,1,2,1],[3]],[[],[1,1,2,1],[4]],[[],[1,1,2,1,1,2]],[[],[1,1,2,1,1,3]],[[],[1,1,2,1,2,1]],[[],[1,1,2,1,2,2]],[[],[1,1,2,1,3,1]],[[],[1,1,2,2],[2]],[[],[1,1,2,2],[3]],[[],[1,1,2,2,1,1]],[[],[1,1,2,2,1,2]],[[],[1,1,2,2,2,1]],[[],[1,1,2,3],[2]],[[],[1,1,2,3,1,1]],[[],[1,1,3],[1,2]],[[],[1,1,3],[1,3]]]

noncomputable def patterns_17_8_36 : List (List (List ℕ)) := [[[],[1,1,3],[2,2]],[[],[1,1,3,1],[2]],[[],[1,1,3,1],[3]],[[],[1,1,3,1,1,2]],[[],[1,1,3,1,2,1]],[[],[1,1,3,2],[2]],[[],[1,1,4],[1,2]],[[],[1,1,4,1],[2]],[[],[1,2],[1,2,1]],[[],[1,2],[1,2,2]],[[],[1,2],[1,2,3]],[[],[1,2],[1,3,1]],[[],[1,2],[1,3,2]],[[],[1,2],[1,4,1]],[[],[1,2],[2],[2]],[[],[1,2],[2],[3]]]

noncomputable def patterns_17_8_37 : List (List (List ℕ)) := [[[],[1,2],[2],[4]],[[],[1,2],[2,1,2]],[[],[1,2],[2,1,3]],[[],[1,2],[2,2,2]],[[],[1,2],[3],[3]],[[],[1,2,1],[1,3]],[[],[1,2,1],[1,4]],[[],[1,2,1],[2,2]],[[],[1,2,1],[2,3]],[[],[1,2,1,1,1,2]],[[],[1,2,1,1,1,3]],[[],[1,2,1,1,2,1]],[[],[1,2,1,1,2,2]],[[],[1,2,1,1,3,1]],[[],[1,2,1,2],[2]],[[],[1,2,1,2],[3]]]

noncomputable def patterns_17_8_38 : List (List (List ℕ)) := [[[],[1,2,1,2,1,2]],[[],[1,2,1,2,2,1]],[[],[1,2,1,3],[2]],[[],[1,2,2],[1,3]],[[],[1,2,2],[2,2]],[[],[1,2,2,1],[2]],[[],[1,2,2,1],[3]],[[],[1,2,2,1,1,2]],[[],[1,2,2,2],[2]],[[],[1,2,3,1],[2]],[[],[1,3],[1,3,1]],[[],[1,3],[2],[2]],[[],[1,3],[2],[3]],[[],[1,3],[2,1,2]],[[],[1,3,1],[2,2]],[[],[1,3,1,1,1,2]]]

noncomputable def patterns_17_8_39 : List (List (List ℕ)) := [[[],[1,3,1,2],[2]],[[],[1,4],[2],[2]],[[],[2],[2],[2,2]],[[],[2],[2],[2,3]],[[],[2],[2,1,1,2]],[[],[2],[2,1,1,3]],[[],[2],[2,1,2,2]],[[],[2],[2,2],[3]],[[],[2,1,1,1,1,2]],[[],[2,1,1,1,1,3]],[[],[2,1,1,1,2,2]],[[],[2,1,1,2],[3]],[[],[2,1,1,2,1,2]],[[],[2,1,2],[2,2]],[[1],[1],[1],[1]],[[1],[1],[1],[2]]]

noncomputable def patterns_17_8_40 : List (List (List ℕ)) := [[[1],[1],[1],[3]],[[1],[1],[1],[4]],[[1],[1],[1],[5]],[[1],[1],[1],[6]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,1,3]],[[1],[1],[1,1,4]],[[1],[1],[1,1,5]],[[1],[1],[1,2,1]],[[1],[1],[1,2,2]],[[1],[1],[1,2,3]],[[1],[1],[1,2,4]],[[1],[1],[1,3,1]],[[1],[1],[1,3,2]],[[1],[1],[1,3,3]]]

noncomputable def patterns_17_8_41 : List (List (List ℕ)) := [[[1],[1],[1,4,1]],[[1],[1],[1,4,2]],[[1],[1],[1,5,1]],[[1],[1],[2],[2]],[[1],[1],[2],[3]],[[1],[1],[2],[4]],[[1],[1],[2],[5]],[[1],[1],[2,1,2]],[[1],[1],[2,1,3]],[[1],[1],[2,1,4]],[[1],[1],[2,2,2]],[[1],[1],[2,2,3]],[[1],[1],[2,3,2]],[[1],[1],[3],[3]],[[1],[1],[3],[4]],[[1],[1],[3,1,3]]]

noncomputable def patterns_17_8_42 : List (List (List ℕ)) := [[[1],[1,1],[1,1]],[[1],[1,1],[1,2]],[[1],[1,1],[1,3]],[[1],[1,1],[1,4]],[[1],[1,1],[1,5]],[[1],[1,1],[2,2]],[[1],[1,1],[2,3]],[[1],[1,1],[2,4]],[[1],[1,1],[3,3]],[[1],[1,1,1],[2]],[[1],[1,1,1],[3]],[[1],[1,1,1],[4]],[[1],[1,1,1],[5]],[[1],[1,1,1,1,1]],[[1],[1,1,1,1,2]],[[1],[1,1,1,1,3]]]

noncomputable def patterns_17_8_43 : List (List (List ℕ)) := [[[1],[1,1,1,1,4]],[[1],[1,1,1,2,1]],[[1],[1,1,1,2,2]],[[1],[1,1,1,2,3]],[[1],[1,1,1,3,1]],[[1],[1,1,1,3,2]],[[1],[1,1,1,4,1]],[[1],[1,1,2],[2]],[[1],[1,1,2],[3]],[[1],[1,1,2],[4]],[[1],[1,1,2,1,1]],[[1],[1,1,2,1,2]],[[1],[1,1,2,1,3]],[[1],[1,1,2,2,1]],[[1],[1,1,2,2,2]],[[1],[1,1,2,3,1]]]

noncomputable def patterns_17_8_44 : List (List (List ℕ)) := [[[1],[1,1,3],[2]],[[1],[1,1,3],[3]],[[1],[1,1,3,1,1]],[[1],[1,1,3,1,2]],[[1],[1,1,3,2,1]],[[1],[1,1,4],[2]],[[1],[1,1,4,1,1]],[[1],[1,2],[1,2]],[[1],[1,2],[1,3]],[[1],[1,2],[1,4]],[[1],[1,2],[2,2]],[[1],[1,2],[2,3]],[[1],[1,2,1],[2]],[[1],[1,2,1],[3]],[[1],[1,2,1],[4]],[[1],[1,2,1,1,2]]]

noncomputable def patterns_17_8_45 : List (List (List ℕ)) := [[[1],[1,2,1,1,3]],[[1],[1,2,1,2,1]],[[1],[1,2,1,2,2]],[[1],[1,2,1,3,1]],[[1],[1,2,2],[2]],[[1],[1,2,2],[3]],[[1],[1,2,2,1,2]],[[1],[1,2,2,2,1]],[[1],[1,2,3],[2]],[[1],[1,3],[1,3]],[[1],[1,3],[2,2]],[[1],[1,3,1],[2]],[[1],[1,3,1],[3]],[[1],[1,3,1,1,2]],[[1],[1,3,2],[2]],[[1],[1,4,1],[2]]]

noncomputable def patterns_17_8_46 : List (List (List ℕ)) := [[[1],[2],[2],[2]],[[1],[2],[2],[3]],[[1],[2],[2],[4]],[[1],[2],[2,1,2]],[[1],[2],[2,1,3]],[[1],[2],[2,2,2]],[[1],[2],[3],[3]],[[1],[2,1,1,1,2]],[[1],[2,1,1,1,3]],[[1],[2,1,1,2,2]],[[1],[2,1,2],[3]],[[1],[2,1,2,1,2]],[[1],[2,2],[2,2]],[[1,1],[1,1],[2]],[[1,1],[1,1],[3]],[[1,1],[1,1],[4]]]

noncomputable def patterns_17_8_47 : List (List (List ℕ)) := [[[1,1],[1,1],[5]],[[1,1],[1,1,1,1]],[[1,1],[1,1,1,2]],[[1,1],[1,1,1,3]],[[1,1],[1,1,1,4]],[[1,1],[1,1,2,1]],[[1,1],[1,1,2,2]],[[1,1],[1,1,2,3]],[[1,1],[1,1,3,1]],[[1,1],[1,1,3,2]],[[1,1],[1,1,4,1]],[[1,1],[1,2],[2]],[[1,1],[1,2],[3]],[[1,1],[1,2],[4]],[[1,1],[1,2,1,2]],[[1,1],[1,2,1,3]]]

noncomputable def patterns_17_8_48 : List (List (List ℕ)) := [[[1,1],[1,2,2,1]],[[1,1],[1,2,2,2]],[[1,1],[1,2,3,1]],[[1,1],[1,3],[2]],[[1,1],[1,3],[3]],[[1,1],[1,3,1,2]],[[1,1],[1,4],[2]],[[1,1],[2],[2,2]],[[1,1],[2],[2,3]],[[1,1],[2,1,1,2]],[[1,1],[2,1,1,3]],[[1,1],[2,1,2,2]],[[1,1],[2,2],[3]],[[1,1,1],[1,1,1]],[[1,1,1],[1,1,2]],[[1,1,1],[1,1,3]]]

noncomputable def patterns_17_8_49 : List (List (List ℕ)) := [[[1,1,1],[1,1,4]],[[1,1,1],[1,2,1]],[[1,1,1],[1,2,2]],[[1,1,1],[1,2,3]],[[1,1,1],[1,3,1]],[[1,1,1],[1,3,2]],[[1,1,1],[1,4,1]],[[1,1,1],[2],[2]],[[1,1,1],[2],[3]],[[1,1,1],[2],[4]],[[1,1,1],[2,1,2]],[[1,1,1],[2,1,3]],[[1,1,1],[2,2,2]],[[1,1,1],[3],[3]],[[1,1,1,1],[1,2]],[[1,1,1,1],[1,3]]]

noncomputable def patterns_17_8_50 : List (List (List ℕ)) := [[[1,1,1,1],[1,4]],[[1,1,1,1],[2,2]],[[1,1,1,1],[2,3]],[[1,1,1,1,1],[2]],[[1,1,1,1,1],[3]],[[1,1,1,1,1],[4]],[[1,1,1,1,1,1,1]],[[1,1,1,1,1,1,2]],[[1,1,1,1,1,1,3]],[[1,1,1,1,1,2,1]],[[1,1,1,1,1,2,2]],[[1,1,1,1,1,3,1]],[[1,1,1,1,2],[2]],[[1,1,1,1,2],[3]],[[1,1,1,1,2,1,1]],[[1,1,1,1,2,1,2]]]

noncomputable def patterns_17_8_51 : List (List (List ℕ)) := [[[1,1,1,1,2,2,1]],[[1,1,1,1,3],[2]],[[1,1,1,1,3,1,1]],[[1,1,1,2],[1,2]],[[1,1,1,2],[1,3]],[[1,1,1,2],[2,2]],[[1,1,1,2,1],[2]],[[1,1,1,2,1],[3]],[[1,1,1,2,1,1,1]],[[1,1,1,2,1,1,2]],[[1,1,1,2,1,2,1]],[[1,1,1,2,2],[2]],[[1,1,1,2,2,1,1]],[[1,1,1,3],[1,2]],[[1,1,1,3,1],[2]],[[1,1,1,3,1,1,1]]]

noncomputable def patterns_17_8_52 : List (List (List ℕ)) := [[[1,1,2],[1,1,2]],[[1,1,2],[1,1,3]],[[1,1,2],[1,2,1]],[[1,1,2],[1,2,2]],[[1,1,2],[1,3,1]],[[1,1,2],[2],[2]],[[1,1,2],[2],[3]],[[1,1,2],[2,1,2]],[[1,1,2,1],[1,2]],[[1,1,2,1],[1,3]],[[1,1,2,1],[2,2]],[[1,1,2,1,1],[2]],[[1,1,2,1,1],[3]],[[1,1,2,1,1,1,2]],[[1,1,2,1,1,2,1]],[[1,1,2,1,2],[2]]]

noncomputable def patterns_17_8_53 : List (List (List ℕ)) := [[[1,1,2,1,2,1,1]],[[1,1,2,2],[1,2]],[[1,1,2,2,1],[2]],[[1,1,3],[1,2,1]],[[1,1,3],[2],[2]],[[1,1,3,1],[1,2]],[[1,1,3,1,1],[2]],[[1,2],[1,2],[2]],[[1,2],[1,2],[3]],[[1,2],[1,2,1,2]],[[1,2],[1,2,2,1]],[[1,2],[1,3],[2]],[[1,2],[2],[2,2]],[[1,2],[2,1,1,2]],[[1,2,1],[1,2,1]],[[1,2,1],[1,2,2]]]

noncomputable def patterns_17_8_54 : List (List (List ℕ)) := [[[1,2,1],[1,3,1]],[[1,2,1],[2],[2]],[[1,2,1],[2],[3]],[[1,2,1],[2,1,2]],[[1,2,1,1,1,1,2]],[[1,2,1,1,1,2,1]],[[1,2,1,1,2],[2]],[[1,2,1,2,1],[2]],[[1,2,2],[2],[2]],[[1,3,1],[2],[2]],[[2],[2],[2],[2]],[[2],[2],[2],[3]],[[2],[2],[2,1,2]],[[2],[2,1,1,1,2]],[[2,1,1,1,1,1,2]]]

noncomputable def patterns_17_8 : List (List (List ℕ)) := patterns_17_8_0 ++ (patterns_17_8_1 ++ (patterns_17_8_2 ++ (patterns_17_8_3 ++ (patterns_17_8_4 ++ (patterns_17_8_5 ++ (patterns_17_8_6 ++ (patterns_17_8_7 ++ (patterns_17_8_8 ++ (patterns_17_8_9 ++ (patterns_17_8_10 ++ (patterns_17_8_11 ++ (patterns_17_8_12 ++ (patterns_17_8_13 ++ (patterns_17_8_14 ++ (patterns_17_8_15 ++ (patterns_17_8_16 ++ (patterns_17_8_17 ++ (patterns_17_8_18 ++ (patterns_17_8_19 ++ (patterns_17_8_20 ++ (patterns_17_8_21 ++ (patterns_17_8_22 ++ (patterns_17_8_23 ++ (patterns_17_8_24 ++ (patterns_17_8_25 ++ (patterns_17_8_26 ++ (patterns_17_8_27 ++ (patterns_17_8_28 ++ (patterns_17_8_29 ++ (patterns_17_8_30 ++ (patterns_17_8_31 ++ (patterns_17_8_32 ++ (patterns_17_8_33 ++ (patterns_17_8_34 ++ (patterns_17_8_35 ++ (patterns_17_8_36 ++ (patterns_17_8_37 ++ (patterns_17_8_38 ++ (patterns_17_8_39 ++ (patterns_17_8_40 ++ (patterns_17_8_41 ++ (patterns_17_8_42 ++ (patterns_17_8_43 ++ (patterns_17_8_44 ++ (patterns_17_8_45 ++ (patterns_17_8_46 ++ (patterns_17_8_47 ++ (patterns_17_8_48 ++ (patterns_17_8_49 ++ (patterns_17_8_50 ++ (patterns_17_8_51 ++ (patterns_17_8_52 ++ (patterns_17_8_53 ++ (patterns_17_8_54 ++ ([])))))))))))))))))))))))))))))))))))))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns5x3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_5_3_0 : List (List (List ℕ)) := [[[],[],[]],[[],[1]],[[],[2]],[[1,1]]]

noncomputable def patterns_5_3 : List (List (List ℕ)) := patterns_5_3_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns5x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_5_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]]]

noncomputable def patterns_5_4 : List (List (List ℕ)) := patterns_5_4_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns5x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_5_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]]]

noncomputable def patterns_5_5 : List (List (List ℕ)) := patterns_5_5_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_6_3_0 : List (List (List ℕ)) := [[[],[],[]],[[],[1]],[[],[2]],[[],[3]],[[1,1]],[[1,2]]]

noncomputable def patterns_6_3 : List (List (List ℕ)) := patterns_6_3_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_6_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[1,1]],[[1],[1]]]

noncomputable def patterns_6_4 : List (List (List ℕ)) := patterns_6_4_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_6_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]]]

noncomputable def patterns_6_5 : List (List (List ℕ)) := patterns_6_5_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_6_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]]]

noncomputable def patterns_6_6 : List (List (List ℕ)) := patterns_6_6_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_7_3_0 : List (List (List ℕ)) := [[[],[],[]],[[],[1]],[[],[2]],[[],[3]],[[],[4]],[[1,1]],[[1,2]],[[1,3]],[[2,2]]]

noncomputable def patterns_7_3 : List (List (List ℕ)) := patterns_7_3_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_7_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[],[3]],[[],[1,1]],[[],[1,2]],[[1],[1]],[[1],[2]],[[1,1,1]]]

noncomputable def patterns_7_4 : List (List (List ℕ)) := patterns_7_4_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_7_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[1,1]],[[],[1],[1]]]

noncomputable def patterns_7_5 : List (List (List ℕ)) := patterns_7_5_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_7_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]]]

noncomputable def patterns_7_6 : List (List (List ℕ)) := patterns_7_6_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_7_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]]]

noncomputable def patterns_7_7 : List (List (List ℕ)) := patterns_7_7_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_8_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[],[3]],[[],[],[4]],[[],[1,1]],[[],[1,2]],[[],[1,3]],[[],[2,2]],[[1],[1]],[[1],[2]],[[1],[3]],[[1,1,1]],[[1,1,2]],[[1,2,1]],[[2],[2]]]

noncomputable def patterns_8_4 : List (List (List ℕ)) := patterns_8_4_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_8_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[1,1]],[[],[],[1,2]],[[],[1],[1]],[[],[1],[2]],[[],[1,1,1]],[[1],[1,1]]]

noncomputable def patterns_8_5 : List (List (List ℕ)) := patterns_8_5_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_8_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[1,1]],[[],[],[1],[1]]]

noncomputable def patterns_8_6 : List (List (List ℕ)) := patterns_8_6_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_8_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]]]

noncomputable def patterns_8_7 : List (List (List ℕ)) := patterns_8_7_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_8_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]]]

noncomputable def patterns_8_8 : List (List (List ℕ)) := patterns_8_8_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_9_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[],[3]],[[],[],[4]],[[],[],[5]],[[],[1,1]],[[],[1,2]],[[],[1,3]],[[],[1,4]],[[],[2,2]],[[],[2,3]],[[1],[1]],[[1],[2]],[[1],[3]],[[1],[4]]]

noncomputable def patterns_9_4_1 : List (List (List ℕ)) := [[[1,1,1]],[[1,1,2]],[[1,1,3]],[[1,2,1]],[[1,2,2]],[[1,3,1]],[[2],[2]],[[2],[3]],[[2,1,2]]]

noncomputable def patterns_9_4 : List (List (List ℕ)) := patterns_9_4_0 ++ (patterns_9_4_1 ++ ([]))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_9_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[],[4]],[[],[],[1,1]],[[],[],[1,2]],[[],[],[1,3]],[[],[],[2,2]],[[],[1],[1]],[[],[1],[2]],[[],[1],[3]],[[],[1,1,1]],[[],[1,1,2]],[[],[1,2,1]],[[],[2],[2]]]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_9_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1,1,1]],[[],[1],[1,1]],[[1],[1],[1]]]

noncomputable def patterns_9_6 : List (List (List ℕ)) := patterns_9_6_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_9_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[1,1]],[[],[],[],[1],[1]]]

noncomputable def patterns_9_7 : List (List (List ℕ)) := patterns_9_7_0 ++ ([])

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_9_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]]]

noncomputable def patterns_9_8 : List (List (List ℕ)) := patterns_9_8_0 ++ ([])

end CycleClique

end OAI
end


