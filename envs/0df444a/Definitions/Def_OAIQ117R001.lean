-- Prove2me | Definitions.Def_OAIQ117R001
-- name    : OAIQ117R001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:01:40.371389+00:00
-- url     : https://prove2.me/theorems/7ece72eb-2db1-4517-8430-a443524f7a2d
-- title:
--   Definitions bundle OAIQ117R001 of the split of OpenAI, Randomized quasipolynomial-time mean-payoff games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.randomized_quasipolynomial_mean_payoff`, carved from OpenAI's openai/math development (OpenAI, *Randomized quasipolynomial-time mean-payoff games*, OpenAI Math Release, September 25, 2026, result family 104, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 20 definitions, 2 inductive types or structures, 9 instances and 13 theorems. The definitions and types are `OAI.MeanPayoff.PolyBound`, `OAI.MeanPayoff.RandomTree.badCount`, `OAI.MeanPayoff.RandomTree.moment`, `OAI.MeanPayoff.RegisterBits.Compile.escape`, `OAI.MeanPayoff.RegisterBits.Compile.overhead`, `OAI.MeanPayoff.SourceControl.trialCredit`, `OAI.MeanPayoff.TreeDevice.Certified.MaskRep`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.FrameLabel`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.JobLabel`, `OAI.MeanPayoff.TreeDevice.Prefix.suffix`, `OAI.MeanPayoff.TreeDevice.Sort.bubbleInt`, `OAI.MeanPayoff.TreeDevice.Split.State`, `OAI.MeanPayoff.TreeDevice.Split.step`, `OAI.MeanPayoff.TwoPhase.equiv`, `OAI.MeanPayoff.TwoPhase.even`, `OAI.MeanPayoff.TwoPhase.interleave`, `OAI.MeanPayoff.TwoPhase.odd`, `OAI.MeanPayoff.average`, `OAI.MeanPayoff.badTimes`, `OAI.MeanPayoff.inputScale`, `OAI.MeanPayoff.vectorBound`, `OAI.MeanPayoff.widthPotential`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MeanPayoff_Allocation`, `MeanPayoff_Alternatives`, `MeanPayoff_Budgets`, `MeanPayoff_EncodedArithmetic`, `MeanPayoff_FiniteBox`, `MeanPayoff_FiniteSuccess`, `MeanPayoff_FiniteTrees`, `MeanPayoff_InputSize`, `MeanPayoff_Instructions`, `MeanPayoff_ParserCosts`, `MeanPayoff_Potential`, `MeanPayoff_Sorting`, `MeanPayoff_StackSimulation`, `MeanPayoff_WordDecoding`, `RandomMean_DispatchBounds`, `RandomMean_StateGrowth`.
--
--   **Imports.** It imports the published bundle `Def_RandomizedMeanPayoff`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ117R002`.
-- source:
--   OpenAI, Randomized quasipolynomial-time mean-payoff games, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 104; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Randomized-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_RandomizedMeanPayoff

section
-- module Solutions.OAIQ117_RM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

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
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

def vectorBound {n : ℕ} (p : Fin n → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (p i).natAbs)

noncomputable def average (w : ℕ → ℝ) (T : ℕ) : ℝ := (∑ j ∈ Finset.range T, w j) / T

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Budgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

namespace RandomTree

open scoped Classical

noncomputable def badCount {α : Type} (P : α → Prop) : List α → ℕ
  | [] => 0
  | a :: as => (if P a then 0 else 1) + badCount P as

noncomputable def moment {α : Type} (P : α → Prop) (as : List α) : ℚ :=
  16 ^ badCount P as

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Alternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
open scoped Classical

noncomputable def badTimes {α : Type} (bad : α → Prop) (qs : List α) (q : α) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun j => bad (qs.getD j q))).card

@[simp] theorem badTimes_zero {α : Type} (bad : α → Prop) (qs : List α) (q : α) :
    badTimes bad qs q 0 = 0 := by simp [badTimes]

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff


def widthPotential (s B : ℕ) : ℕ :=
  8 * s * Nat.log 2 B + (8 * s * B) / (2 ^ Nat.log 2 B)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def inputScale (G : Game) : ℕ := 2 ^ 24 * ((input G).length + 2)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace TwoPhase

def even {t : ℕ} (bits : Fin (2 * t) → Bool) (j : Fin t) : Bool :=
  bits ⟨2 * j.val, by omega⟩

def odd {t : ℕ} (bits : Fin (2 * t) → Bool) (j : Fin t) : Bool :=
  bits ⟨2 * j.val + 1, by omega⟩

def interleave {t : ℕ} (bits : (Fin t → Bool) × (Fin t → Bool))
    (j : Fin (2 * t)) : Bool :=
  if j.val % 2 = 0 then bits.1 ⟨j.val / 2, by omega⟩
  else bits.2 ⟨j.val / 2, by omega⟩

@[simp] theorem even_interleave {t : ℕ} (bits : (Fin t → Bool) × (Fin t → Bool)) :
    even (interleave bits) = bits.1 := by
  funext j
  simp [even, interleave]

@[simp] theorem odd_interleave {t : ℕ} (bits : (Fin t → Bool) × (Fin t → Bool)) :
    odd (interleave bits) = bits.2 := by
  funext j
  simp [odd, interleave, Nat.add_div]

def equiv (t : ℕ) : ((Fin t → Bool) × (Fin t → Bool)) ≃ (Fin (2 * t) → Bool) where
  toFun := interleave
  invFun := fun bits => (even bits, odd bits)
  left_inv bits := by simp only [even_interleave, odd_interleave]
  right_inv bits := by
    funext j
    simp only [interleave, even, odd]
    split <;> rename_i hj
    · congr 1
      apply Fin.ext
      dsimp only
      have hm := Nat.mod_add_div j.val 2
      omega
    · congr 1
      apply Fin.ext
      dsimp only
      have hm := Nat.mod_add_div j.val 2
      have hb := Nat.mod_lt j.val (by omega : 0 < 2)
      omega

open scoped Classical

end TwoPhase
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Instructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits

namespace Compile

theorem ofFn_split {K : ℕ} (s : Fin K → List Bool) (k : Fin K) :
    List.ofFn s = (List.ofFn s).take k.val ++ s k :: (List.ofFn s).drop (k.val + 1) := by
  have h : k.val < (List.ofFn s).length := by simp
  have ht := List.take_append_drop (k.val + 1) (List.ofFn s)
  rw [List.take_succ_eq_append_getElem h, List.getElem_ofFn] at ht
  simpa [List.append_assoc] using ht.symm

theorem ofFn_update {K : ℕ} (s : Fin K → List Bool) (k : Fin K) (xs : List Bool) :
    List.ofFn (Function.update s k xs) = (List.ofFn s).set k.val xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_ofFn, List.getElem_set]
  simp [Function.update_apply, Fin.ext_iff, eq_comm]

end Compile


namespace Compile

def escape : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: escape bs

@[simp] theorem escape_append (a b : List Bool) : escape (a ++ b) = escape a ++ escape b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [escape, ih]

end Compile
end MeanPayoff.RegisterBits
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
open RandomTree

namespace Compile

def overhead (K S n : ℕ) : ℕ := n * (4 * (S + n) + 2 * K + 6)

end Compile
end MeanPayoff.RegisterBits

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.SourceControl

def trialCredit (t : ℕ) : ℕ := 3*t+1

end MeanPayoff.SourceControl
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sorting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Sort

def bubbleInt (w : ℤ) : List ℤ → List ℤ
  | [] => [w]
  | x::xs => min w x::bubbleInt (max w x) xs

end MeanPayoff.TreeDevice.Sort
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_WordDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Split
abbrev State := List Bool × List Bool

def step (z : State × Unit) : State := (z.1.2.headD false::z.1.1,z.1.2.tail)
end MeanPayoff.TreeDevice.Split

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ParserCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice
namespace Prefix

def suffix : List Bool → List Bool
  | [] => []
  | false::xs => xs
  | true::xs => suffix xs

theorem suffix_isSuffix (xs : List Bool) : ∃ pre, pre++suffix xs=xs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨[false],rfl⟩
    | true =>
      obtain ⟨pre,hp⟩ := ih
      exact ⟨true::pre,by simpa only [List.cons_append,suffix] using congrArg (List.cons true) hp⟩
end Prefix

end MeanPayoff.TreeDevice
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified

def MaskRep {n : ℕ} (H : Finset (Fin n)) (xs : List Bool) : Prop :=
  xs=List.ofFn (fun i => decide (i∈H))

end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

def PolyBound {ι : Type} (base f : ι→ℕ) : Prop :=
  ∃ K d : ℕ, ∀ i, f i≤K*(base i+1)^d
end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_StateGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
 theorem mask_head {n : ℕ} {bs : List (List Bool)} (h : ∀ b∈bs, b.length≤n) : (bs.headD []).length≤n := by
  cases bs with
  | nil => exact Nat.zero_le _
  | cons b bs => exact h b (by simp)
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_DispatchBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
inductive JobLabel where
  | solve | ask | trials | update | centers | orient | orientTrials | orientPlus | tighten | reweight
inductive FrameLabel where
  | trialsHead | vectorCons | median | centerFirst | centerSecond | centersHead | orientLoop | orientTail | orientHead | orientCons | combine | tightenFirst | tightenSecond | floor | ceiling | solveTight | solveOriented | reweightHead | solveReweighted | capHigh | capLow | includeInner
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end


