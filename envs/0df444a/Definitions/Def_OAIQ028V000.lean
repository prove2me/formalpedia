-- Prove2me | Definitions.Def_OAIQ028V000
-- name    : OAIQ028V000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:06:53.20148+00:00
-- url     : https://prove2.me/theorems/9c85d971-d87e-4e26-9922-b673940ac7a1
-- title:
--   Definitions bundle OAIQ028V000 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 758 declarations of OpenAI's Lean: 360 definitions, 16 inductive types or structures, 6 instances and 376 theorems. The definitions and types are `OAI.UniqueGames.BinaryEncoding.clauseBits`, `OAI.UniqueGames.BinaryEncoding.literalBits`, `OAI.UniqueGames.BinaryEncoding.namesBitSize`, `OAI.UniqueGames.BinaryFormula.activeNames`, `OAI.UniqueGames.BinaryFormula.clauseNames`, `OAI.UniqueGames.BinaryFormula.compactClause`, `OAI.UniqueGames.BinaryFormula.compactClauses`, `OAI.UniqueGames.BinaryFormula.compactIndex`, `OAI.UniqueGames.BinaryFormula.compactLiteral`, `OAI.UniqueGames.BinaryFormula.decodeName`, `OAI.UniqueGames.BinaryFormula.dense`, `OAI.UniqueGames.BinaryFormula.extendAssignment`, `OAI.UniqueGames.BinaryFormula.restrictAssignment`, `OAI.UniqueGames.BinaryFormula.sourceNames`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.Label`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.labelEquiv`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.labelIndex`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.leftHalf`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.patternRelationIndex`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.relationAddress`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.rightHalf`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph`, `OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableVerifier`, `OAI.UniqueGames.Foundations.Complexity.MachineComposition.advance`, `OAI.UniqueGames.Foundations.Complexity.MachineComposition.compositionPolynomial`, `OAI.UniqueGames.Foundations.Complexity.MachineComposition.embeddedExecution`, `OAI.UniqueGames.Foundations.Complexity.MachineComposition.liftExecutionInTime`, `OAI.UniqueGames.Foundations.Complexity.MachineEmbedding.Alphabet`, `OAI.UniqueGames.Foundations.Complexity.MachineEmbedding.configuration`, `OAI.UniqueGames.Foundations.Complexity.MachineEmbedding.label`, `OAI.UniqueGames.Foundations.Complexity.MachineEmbedding.program`, `OAI.UniqueGames.Foundations.Complexity.MachineEmbedding.statement`, `OAI.UniqueGames.Foundations.Complexity.MachineEmbedding.tapes`, `OAI.UniqueGames.Foundations.Complexity.Runtime.maxLabelPushes`, `OAI.UniqueGames.Foundations.Complexity.Runtime.programPushBound`, `OAI.UniqueGames.Foundations.Complexity.Runtime.statementPushBound`, `OAI.UniqueGames.Foundations.CorrelatedSampling.RectangleSeed`, `OAI.UniqueGames.Foundations.CorrelatedSampling.SharedProfileSeed`, `OAI.UniqueGames.Foundations.CorrelatedSampling.ThresholdInterval`, `OAI.UniqueGames.Foundations.CorrelatedSampling.cutAt` and 336 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Encoding_BinaryEncoding`, `VertexCover_Encoding_BinaryFormula`, `VertexCover_Encoding_FinalCNFPattern`, `VertexCover_Encoding_MachineComposition`, `VertexCover_Encoding_MachineEmbedding`, `VertexCover_Encoding_Runtime`, `VertexCover_Fourier_Decoder`, `VertexCover_Fourier_Folding`, `VertexCover_Fourier_SourceContexts`, `VertexCover_Fourier_Walsh`, `VertexCover_Games_Basic`, `VertexCover_Machines_ExpanderStep`, `VertexCover_PCP_AlphabetGraph`, `VertexCover_PCP_AlphabetReduction`, `VertexCover_PCP_AlphabetTableEnumeration`, `VertexCover_PCP_AlphabetTableQueries`, `VertexCover_PCP_AlphabetTableRelations`, `VertexCover_PCP_AlphabetTableTable`, `VertexCover_PCP_AssignmentTester`, `VertexCover_PCP_CayleySampling`, `VertexCover_PCP_CayleySpectral`, `VertexCover_PCP_CayleyTailCount`, `VertexCover_PCP_CloudPadding`, `VertexCover_PCP_CloudRounding`, `VertexCover_PCP_CodeComposition`, `VertexCover_PCP_ConstraintGraph`, `VertexCover_PCP_DegreeReplacement`, `VertexCover_PCP_ExpanderFamily`, `VertexCover_PCP_ExpanderTables`, `VertexCover_PCP_Expanders`, `VertexCover_PCP_FinalBooleanVerifier`, `VertexCover_PCP_GenericGraphTables`, `VertexCover_PCP_GraphGap`, `VertexCover_PCP_GraphTables`, `VertexCover_PCP_GraphTransport`, `VertexCover_PCP_LazyConstraint`, `VertexCover_PCP_Overlay`, `VertexCover_PCP_PortTables`, `VertexCover_PCP_PoweringLazy`, `VertexCover_PCP_PoweringWalks`, `VertexCover_PCP_Preprocessing`, `VertexCover_PCP_PreprocessingCloudIndex`, `VertexCover_PCP_PreprocessingOverlayTables`, `VertexCover_PCP_PreprocessingPaddingTables`, `VertexCover_PCP_PreprocessingRegularTables`, `VertexCover_PCP_QueryIncidence`, `VertexCover_PCP_Regularization`, `VertexCover_PCP_SpectralReturn`, `VertexCover_PCP_Target`, `VertexCover_PCP_UniformRestriction`, `VertexCover_PCP_VerifierToCNF`, `VertexCover_PCP_VertexPadding`, `VertexCover_PCP_ZigzagGraphs`, `VertexCover_Reduction_DenseEncodingBound`, `VertexCover_Reduction_PairEventMean`, `VertexCover_Sampling_Basic`, `VertexCover_Sampling_FiniteTrials`, `VertexCover_Sampling_LabelBound`, `VertexCover_Sampling_Rectangle`, `VertexCover_Sampling_SharedProfiles`, `VertexCover_Sampling_ThresholdPartition`, `VertexCover_Sampling_TraceLaw`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ028V003`, `OAIQ028V004` and `OAIQ028V005`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover

section
-- module Solutions.OAIQ028_VC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Encoding_BinaryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGames.BinaryFormula

def clauseNames (clause : Clause) : List Nat :=
  [clause[0].name, clause[1].name, clause[2].name]

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

end UniqueGames.BinaryFormula

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Encoding_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGames.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

end UniqueGames.BinaryEncoding

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_Walsh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_xor (b «c» : Bool) :
    bitSign (b ^^ «c») = bitSign b * bitSign «c» := by
  cases b <;> cases «c» <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp []
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

end UniqueGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_Folding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                   

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

end UniqueGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_Decoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                   

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem sign_power_parity (b : Bool) (n : Nat) :
    bitSign b ^ n = bitSign (decide (Odd n) && b) := by
  cases b
  · simp [bitSign]
  · simp only [Bool.and_true, bitSign, ite_true, decide_eq_true_eq]
    rw [neg_one_pow_eq_ite]
    by_cases h : Even n
    · simp [h, Nat.not_odd_iff_even.mpr h]
    · simp [h, Nat.not_even_iff_odd.mp h]

end UniqueGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AssignmentTester
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

noncomputable section

namespace UniqueGames.Foundations.PCP.AssignmentTester

open UniqueGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

theorem bitSign_parity (s f : Cube A) : bitSign (parity s f) = walsh s f := by
  have hw : walsh s f = (-1 : ℝ) ^
      (Finset.univ.filter fun a => s a && f a = true).card := by
    simp [walsh, bitSign, Finset.prod_ite]
  rw [hw]
  simpa [parity, bitSign] using
    (sign_power_parity true (Finset.univ.filter fun a => s a && f a = true).card).symm

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign] <;> linarith

theorem parity_xor (s f g : Cube A) :
    parity s (cubeXor f g) = (parity s f ^^ parity s g) := by
  apply bitSign_injective
  rw [bitSign_parity, bitSign_xor, bitSign_parity, bitSign_parity, walsh_xor]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

def singleMask (i : A) : Cube A := fun j => decide (j = i)

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

variable {K : Type*} [Fintype K] [Nonempty K]

def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

end UniqueGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CodeComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

noncomputable section

namespace UniqueGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open UniqueGames.Foundations.Hastad

def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

end UniqueGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

noncomputable section

namespace UniqueGames.Foundations.PCP.AlphabetReduction

open UniqueGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

abbrev InputCoordinate (A : Type*) := Bool × Cube A

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

end UniqueGames.Foundations.PCP.AlphabetReduction
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                           

namespace UniqueGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.«variables» → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

end UniqueGames.Foundations.Target

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ConstraintGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end UniqueGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.GraphTables

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

end UniqueGames.Foundations.PCP.GraphTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

end UniqueGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                   

namespace UniqueGames.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

structure Table (vertices ports : Nat) where
  reverseIndex : Vector (Fin (vertices * ports)) (vertices * ports)
  relations : Vector GraphTables.RelationTable (vertices * ports)
  involutive : Function.Involutive
    (fun i : Fin (vertices * ports) => reverseIndex[i])
  transpose : ∀ (i : Fin (vertices * ports)) (a b : Label),
    GraphTables.relationAt relations[reverseIndex[i]] b a =
      GraphTables.relationAt relations[i] a b

variable {n d : Nat}

def rotation (table : Table n d) (e : Fin n × Fin d) : Fin n × Fin d :=
  (rowIndex n d).symm table.reverseIndex[rowIndex n d e]

def accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) : Bool :=
  GraphTables.relationAt table.relations[rowIndex n d e] a b

@[simp] theorem rowIndex_rotation (table : Table n d) (e : Fin n × Fin d) :
    rowIndex n d (rotation table e) = table.reverseIndex[rowIndex n d e] := by
  exact (rowIndex n d).apply_symm_apply _

theorem rotation_involutive (table : Table n d) : Function.Involutive (rotation table) := by
  intro e
  simp only [rotation, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex n d).symm (table.involutive (rowIndex n d e))).trans
    ((rowIndex n d).symm_apply_apply e)

theorem accepts_rotation (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    accepts table (rotation table e) b a = accepts table e a b := by
  simpa only [accepts, rowIndex_rotation] using table.transpose (rowIndex n d e) a b

def portGraph (table : Table n d) : PortGraph (Fin n) (Fin d) where
  rot :=
    { toFun := rotation table
      invFun := rotation table
      left_inv := rotation_involutive table
      right_inv := rotation_involutive table }
  rot_involutive := rotation_involutive table

@[simp] theorem portGraph_rot (table : Table n d) (e : Fin n × Fin d) :
    (portGraph table).rot e = rotation table e := rfl

def baseGraph (table : Table n d) : ConstraintGraph (Fin n) (Fin n × Fin d) Label where
  reverse := (portGraph table).rot
  reverse_involutive := rotation_involutive table
  tail := Prod.fst
  accepts := accepts table
  reverse_accepts := accepts_rotation table

@[simp] theorem baseGraph_reverse (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).reverse e = rotation table e := rfl

@[simp] theorem baseGraph_tail (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).tail e = e.1 := rfl

@[simp] theorem baseGraph_head (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).head e = (rotation table e).1 := rfl

@[simp] theorem baseGraph_accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    (baseGraph table).accepts e a b = accepts table e a b := rfl

def ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rowIndex n d (G.rot ((rowIndex n d).symm i)))
  relations := Vector.ofFn (fun i => GraphTables.relationOf (predicate ((rowIndex n d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply]
    exact (congrArg (rowIndex n d) (G.rot_involutive ((rowIndex n d).symm i))).trans
      ((rowIndex n d).apply_symm_apply i)
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]
    exact htranspose ((rowIndex n d).symm i) a b

@[simp] theorem rotation_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) : rotation (ofPortGraph G predicate htranspose) e = G.rot e := by
  simp only [rotation, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

@[simp] theorem accepts_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) (a b : Label) :
    accepts (ofPortGraph G predicate htranspose) e a b = predicate e a b := by
  simp only [accepts, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]

end UniqueGames.Foundations.PCP.PortTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_QueryIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def incidenceAccept [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q) : Bool :=
  decide (LeftValid T event left) &&
    decide (left (canonicalSlot T event slot) = decodeRight positive right)

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

def predicate [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    Dart E q → Label q → Label q → Bool
  | ((event, slot), false), a, b => incidenceAccept T positive event slot a b
  | ((event, slot), true), a, b => incidenceAccept T positive event slot b a

def graph [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    ConstraintGraph (Vertex E X) (Dart E q) (Label q) where
  reverse := reverseEquiv
  reverse_involutive := reverse_involutive
  tail := tail T
  accepts := predicate T positive
  reverse_accepts := by
    rintro ⟨⟨event, slot⟩, orientation⟩ a b
    cases orientation <;> rfl

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

@[simp] theorem card_vertex [Fintype E] [Fintype X] :
    Fintype.card (Vertex E X) = Fintype.card E + Fintype.card X := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart [Fintype E] :
    Fintype.card (Dart E q) = 2 * q * Fintype.card E := by
  simp [Dart, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end UniqueGames.Foundations.PCP.QueryIncidence

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_UniformRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

end UniqueGames.Foundations.PCP.UniformRestriction

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

noncomputable section

namespace UniqueGames.Foundations.PCP.AlphabetGraph

open UniqueGames.Foundations.Hastad
open scoped BigOperators

abbrev Address (V E A : Type*) := (V × Cube A) ⊕ (E × Cube (A × A))

abbrev LocalEvent (A : Type*) := Fin 4 × AlphabetReduction.InputCoordinate A ×
  Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A)

abbrev Event (E A : Type*) := E × LocalEvent A

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev legal (G : ConstraintGraph V E A) (e : E) (p : A × A) : Prop :=
  G.accepts e p.1 p.2 = true

instance legalDecidable (G : ConstraintGraph V E A) (e : E) :
    DecidablePred (legal G e) :=
  fun p => inferInstanceAs (Decidable (G.accepts e p.1 p.2 = true))

def restrictTape (G : ConstraintGraph V E A) (e : E) (f : Cube (A × A)) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) := UniformRestriction.restrict (legal G e) f

def extendTape (G : ConstraintGraph V E A) (e : E)
    (f : Cube (AlphabetReduction.LegalPair (G.accepts e))) : Cube (A × A) :=
  UniformRestriction.extend (legal G e) f

def globalizeQuery (G : ConstraintGraph V E A) (e : E) :
    AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e)) → Address V E A
  | .inl (side, tape) => .inl ((if side then G.head e else G.tail e), tape)
  | .inr tape => .inr (e, extendTape G e tape)

def verifier (G : ConstraintGraph V E A) : QueryIncidence.Verifier (Event E A) (Address V E A) 6 where
  query := fun (e, kind, k, f, g, r₀, r₁, r₂) slot =>
    globalizeQuery G e (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
      (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
      (restrictTape G e r₁) (restrictTape G e r₂) slot)
  accepts := fun (_, kind, _, _, _, _, _, _) b => AssignmentTester.eventAccepts kind b

def vertexBlock (assignment : Address V E A → Bool) (v : V) : Cube A → Bool :=
  fun tape => assignment (.inl (v, tape))

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

def honestAssignment (G : ConstraintGraph V E A) (labeling : V → A) : Address V E A → Bool
  | .inl (v, tape) => tape (labeling v)
  | .inr (e, tape) => tape (labeling (G.tail e), labeling (G.head e))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem honest_vertexBlock (G : ConstraintGraph V E A) (labeling : V → A) (v : V) :
    vertexBlock (honestAssignment G labeling) v = CodeComposition.codeword (labeling v) := rfl

def graph [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A) :
    ConstraintGraph (QueryIncidence.Vertex (Event E A) (Address V E A))
      (QueryIncidence.Dart (Event E A) 6) (QueryIncidence.Label 6) := QueryIncidence.graph (verifier G) (by omega)

end UniqueGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                  

namespace UniqueGames.Foundations.PCP.AlphabetTable.Enumeration

open UniqueGames.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

end UniqueGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableQueries
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                              

namespace UniqueGames.Foundations.PCP.AlphabetTable.Queries

open UniqueGames.Foundations.Hastad

abbrev RawQuery (q : Nat) :=
  (Bool × Cube (Fin q)) ⊕ Cube (Fin q × Fin q)

abbrev LocalEvent (q : Nat) := AlphabetGraph.LocalEvent (Fin q)

def mask {q : Nat} (P : Fin q → Fin q → Bool) (f : Cube (Fin q × Fin q)) :
    Cube (Fin q × Fin q) := fun p => if P p.1 p.2 then f p else false

def xorTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a ^^ g a

def andTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a && g a

def inputPairTape {q : Nat} (k : Bool × Cube (Fin q)) : Cube (Fin q × Fin q) :=
  fun p => if k.1 then k.2 p.2 else k.2 p.1

def query {q : Nat} (P : Fin q → Fin q → Bool) (event : LocalEvent q)
    (slot : Fin 6) : RawQuery q :=
  match event with
  | (kind, k, f, g, r₀, r₁, r₂) =>
    if kind = 0 then
      if slot = 0 then .inr (mask P f) else
      if slot = 1 then .inr (mask P g) else .inr (mask P (xorTape f g))
    else if kind = 1 then
      if slot = 0 then .inr (mask P r₀) else
      if slot = 1 then .inr (mask P (xorTape r₀ (andTape f g))) else
      if slot = 2 then .inr (mask P r₁) else
      if slot = 3 then .inr (mask P (xorTape r₁ f)) else
      if slot = 4 then .inr (mask P r₂) else .inr (mask P (xorTape r₂ g))
    else if kind = 2 then
      if slot = 0 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (fun _ => true)))
    else
      if slot = 0 then .inl k else
      if slot = 1 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (inputPairTape k)))

def globalize {q : Nat} {V E : Type*} (tail head : V) (edge : E) :
    RawQuery q → AlphabetGraph.Address V E (Fin q)
  | .inl (side, tape) => .inl ((if side then head else tail), tape)
  | .inr tape => .inr (edge, tape)

@[simp] theorem mask_idempotent {q : Nat} (P : Fin q → Fin q → Bool)
    (f : Cube (Fin q × Fin q)) : mask P (mask P f) = mask P f := by
  funext p
  cases hp : P p.1 p.2 <;> simp [mask, hp]

def extendQuery {q : Nat} (P : Fin q → Fin q → Bool) :
    AlphabetReduction.InputCoordinate (Fin q) ⊕ Cube (AlphabetReduction.LegalPair P) →
      RawQuery q
  | .inl k => .inl k
  | .inr tape => .inr (UniformRestriction.extend (fun p : Fin q × Fin q => P p.1 p.2 = true) tape)

theorem query_eq_extend_eventQueries {q : Nat} (P : Fin q → Fin q → Bool)
    (kind : Fin 4) (k : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) (slot : Fin 6) :
    query P (kind, k, f, g, r₀, r₁, r₂) slot =
      extendQuery P (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding P) kind k
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) f)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) g)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₀)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₁)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₂) slot) := by
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, AssignmentTester.eventQueries, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> simp_all only [extendQuery]
  all_goals rfl

theorem globalize_extendQuery {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E)
    (x : AlphabetReduction.InputCoordinate (Fin q) ⊕
      Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    globalize (G.tail e) (G.head e) e (extendQuery (G.accepts e) x) =
      AlphabetGraph.globalizeQuery G e x := by
  cases x with
  | inl k => cases k; rfl
  | inr tape => rfl

theorem globalize_query {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E) (event : LocalEvent q) (slot : Fin 6) :
    globalize (G.tail e) (G.head e) e (query (G.accepts e) event slot) =
      (AlphabetGraph.verifier G).query (e, event) slot := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rw [query_eq_extend_eventQueries]
  exact globalize_extendQuery G e _

end UniqueGames.Foundations.PCP.AlphabetTable.Queries

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                

namespace UniqueGames.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

def relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable :=
  GraphTables.relationOf fun a b =>
    predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
      slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)

@[simp] theorem relationAt_relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot orientation) a b =
      predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
        slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  exact GraphTables.relationAt_relationOf _ _ _

def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

def relationFromTable (old : Vector Bool (q * q)) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable := relation (oldPredicate old) selfLoop event slot orientation

@[simp] theorem oldPredicate_relationAt (old : GraphTables.RelationTable)
    (a b : GraphTables.Label) : oldPredicate old a b = GraphTables.relationAt old a b := rfl

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem eqProfile_query_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (i j : Fin 6) :
    eqProfile (decide (G.tail e = G.head e)) (query (G.accepts e) event) i j = true ↔
      (AlphabetGraph.verifier G).query (e, event) i =
        (AlphabetGraph.verifier G).query (e, event) j := by
  rw [← globalize_query G e event i, ← globalize_query G e event j]
  exact (globalize_eq_iff (G.tail e) (G.head e) e _ rfl _ _).symm

theorem canonicalSlot_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    canonicalSlot (decide (G.tail e = G.head e)) (query (G.accepts e) event) slot =
      QueryIncidence.canonicalSlot (AlphabetGraph.verifier G) (e, event) slot := by
  unfold canonicalSlot QueryIncidence.canonicalSlot
  apply Fin.find_congr'
  exact eqProfile_query_iff G e event _ slot

omit [DecidableEq E] in
theorem repeatedConsistent_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    RepeatedConsistent (decide (G.tail e = G.head e)) (query (G.accepts e) event) label ↔
      QueryIncidence.RepeatedConsistent (AlphabetGraph.verifier G) (e, event) label := by
  constructor
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mpr hij)
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mp hij)

omit [DecidableEq V] [DecidableEq E] in
theorem verifier_accepts (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    (AlphabetGraph.verifier G).accepts (e, event) label =
      AssignmentTester.eventAccepts event.1 label := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rfl

theorem incidenceAccept_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) :
    incidenceAccept (decide (G.tail e = G.head e)) (query (G.accepts e) event)
      (AssignmentTester.eventAccepts event.1) slot left right =
      QueryIncidence.incidenceAccept (AlphabetGraph.verifier G) (by decide) (e, event) slot
        left right := by
  simp only [incidenceAccept, QueryIncidence.incidenceAccept, QueryIncidence.LeftValid,
    verifier_accepts, repeatedConsistent_iff, canonicalSlot_eq,
    QueryIncidence.decodeRight, QueryIncidence.zeroSlot]
  rfl

theorem relationAt_relation_graph (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt
        (relation (G.accepts e) (decide (G.tail e = G.head e)) event slot orientation) a b =
      (AlphabetGraph.graph G).accepts (((e, event), slot), orientation)
        (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  rw [relationAt_relation]
  cases orientation <;>
    exact incidenceAccept_eq G e event slot _ _

end UniqueGames.Foundations.PCP.AlphabetTable.Relations

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_DegreeReplacement
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

open scoped BigOperators

namespace UniqueGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

end UniqueGames.Foundations.PCP.DegreeReplacement

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] («c» : ℝ) : mean (fun _ : A => «c») = «c» :=
  Fintype.expect_const «c»

end Averages

end

end UniqueGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ZigzagGraphs
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

end UniqueGames.Foundations.PCP.ZigzagGraphs

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Overlay
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                

open scoped BigOperators

namespace UniqueGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

end UniqueGames.Foundations.PCP.Overlay

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLazy
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def lazyRotate (G : PortGraph V D) : Edge V (Bool × D) → Edge V (Bool × D)
  | (v, (false, d)) => (v, (false, d))
  | (v, (true, d)) => ((G.rot (v, d)).1, (true, (G.rot (v, d)).2))

theorem lazyRotate_involutive (G : PortGraph V D) :
    Function.Involutive (lazyRotate G) := by
  rintro ⟨v, b, d⟩
  cases b with
  | false => rfl
  | true =>
    exact congrArg (fun e : V × D => (e.1, (true, e.2))) (rot_rot G (v, d))

def lazyGraph (G : PortGraph V D) : PortGraph V (Bool × D) where
  rot := {
    toFun := lazyRotate G
    invFun := lazyRotate G
    left_inv := lazyRotate_involutive G
    right_inv := lazyRotate_involutive G }
  rot_involutive := lazyRotate_involutive G

@[simp] theorem lazyGraph_rot_false (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (false, d)) = (v, (false, d)) := rfl

@[simp] theorem lazyGraph_rot_true (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (true, d)) = ((G.rot (v, d)).1, (true, (G.rot (v, d)).2)) := rfl

end UniqueGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_LazyConstraint
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a «c»
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a «c»

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

end UniqueGames.Foundations.PCP.LazyConstraint

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CayleySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

noncomputable section

namespace UniqueGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open UniqueGames.Foundations.Hastad

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

end UniqueGames.Foundations.PCP.CayleySampling

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CayleySpectral
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Hastad.bitSign_not _root_.OAI.UniqueGames.Foundations.Hastad.cubeFlip_cubeFlip _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

noncomputable section

namespace UniqueGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open UniqueGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

end UniqueGames.Foundations.PCP.CayleySpectral
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CayleyTailCount
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Hastad.bitSign_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators
open UniqueGames.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in
                                                                     
theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

theorem ratio_le_of_weight («c» m : ℕ)
    (h : «c» * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    («c» : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : («c» : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance instDecidableBadWord (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

theorem seventh_power_size : (2 : ℕ) ^ 448 = (((2 : ℕ) ^ 16) ^ 7) ^ 4 := by
  rw [← pow_mul, ← pow_mul]

end UniqueGames.Foundations.PCP.CayleyTailCount

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Expanders
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                  

noncomputable section

namespace UniqueGames.Foundations.PCP.Expanders

open scoped BigOperators
open UniqueGames.Foundations.Hastad
open CayleySpectral

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, ite_eq_left hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, ite_eq_right hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, ite_eq_right hs, ite_eq_left hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

def baseDimension : Nat := 448
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · unfold baseDimension initialDegree basePower
    exact CayleyTailCount.seventh_power_size
  · norm_num [basePower]

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end UniqueGames.Foundations.PCP.Expanders
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphTransport
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

end UniqueGames.Foundations.PCP.GraphTransport

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

noncomputable def baseOnCloud : PortGraph CloudPort BasePort :=
  GraphTransport.reindex (Classical.choose exists_baseGraph) baseVertexEquiv (Equiv.refl _)

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

def graph (H : PortGraph CloudPort BasePort) : (n : Nat) → PortGraph (Vertex n) Port
  | 0 => { rot := Equiv.refl _, rot_involutive := fun _ => rfl }
  | n + 1 => ZigzagGraphs.zigzag (ZigzagGraphs.square (graph H n)) H

noncomputable def family (n : Nat) : PortGraph (Vertex n) Port := graph baseOnCloud n

theorem card_vertex (n : Nat) : Fintype.card (Vertex n) = growth ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × CloudPort) = growth ^ (n + 1)
    rw [Fintype.card_prod, ih, card_cloudPort, pow_succ]

def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

end UniqueGames.Foundations.PCP.ExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CloudPadding
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

theorem paddedSize_of_pos {k : Nat} (hk : 0 < k) :
    paddedSize k = ExpanderFamily.size k := by
  simp only [paddedSize, ite_eq_right (Nat.ne_of_gt hk)]

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.le_size k

def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem card_padded_cloud (G : ConstraintGraph V E A) (dummy : V → Type*)
    [∀ v, Fintype (dummy v)] (v : V) :
    Fintype.card (Cloud (paddedGraph G dummy) v) =
      Fintype.card (Cloud G v) + Fintype.card (dummy v) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (paddedCloudEquiv G dummy v)

abbrev dummy (G : ConstraintGraph V E A) (v : V) :=
  Fin (paddedSize (Fintype.card (Cloud G v)) - Fintype.card (Cloud G v))

theorem card_cloud (G : ConstraintGraph V E A) (v : V) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      paddedSize (Fintype.card (Cloud G v)) := by
  rw [card_padded_cloud]
  simp only [dummy, Fintype.card_fin]
  exact Nat.add_sub_of_le (le_paddedSize _)

theorem card_cloud_eq_family (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      Fintype.card (ExpanderFamily.Vertex
        (ExpanderFamily.level (Fintype.card (Cloud G v)))) := by
  rw [card_cloud, paddedSize_of_pos hk, ExpanderFamily.card_vertex]
  rfl

end UniqueGames.Foundations.PCP.CloudPadding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CloudRounding
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.CloudRounding

open scoped BigOperators

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

end GraphRounding

end UniqueGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Regularization
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

noncomputable section

namespace UniqueGames.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Vertex (G : ConstraintGraph V E A) := PaddedDart G (CloudPadding.dummy G)
abbrev Port := ExpanderFamily.Port ⊕ Unit

def cloudEquiv (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card (Cloud G v))) ≃
      Cloud (paddedGraph G (CloudPadding.dummy G)) v :=
  Fintype.equivOfCardEq (CloudPadding.card_cloud_eq_family G v hk).symm

def cloudGraph (G : ConstraintGraph V E A) (v : V) :
    PortGraph (Cloud (paddedGraph G (CloudPadding.dummy G)) v) ExpanderFamily.Port :=
  if hk : Fintype.card (Cloud G v) = 0 then
    { rot := Equiv.refl _
      rot_involutive := fun _ => rfl }
  else
    GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v (Nat.pos_of_ne_zero hk)) (Equiv.refl _)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  paddedReplacementGraph G (CloudPadding.dummy G) (cloudGraph G)

omit [Fintype A] [DecidableEq E] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) (e : Vertex G × Port) :
    (graph G).tail e = e.1 := rfl

end UniqueGames.Foundations.PCP.Regularization

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

def reverseFunction (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (V ⊕ Fin extra) × D → (V ⊕ Fin extra) × D
  | (Sum.inl v, d) => (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2)
  | (Sum.inr w, d) => (Sum.inr w, d)

theorem reverseFunction_involutive (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    Function.Involutive (reverseFunction G extra) := by
  rintro ⟨v | w, d⟩
  · change (Sum.inl (G.reverse (G.reverse (v, d))).1,
      (G.reverse (G.reverse (v, d))).2) = (Sum.inl v, d)
    rw [G.reverse_involutive]
  · rfl

def pad (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    ConstraintGraph (V ⊕ Fin extra) ((V ⊕ Fin extra) × D) A where
  reverse := {
    toFun := reverseFunction G extra
    invFun := reverseFunction G extra
    left_inv := reverseFunction_involutive G extra
    right_inv := reverseFunction_involutive G extra }
  reverse_involutive := reverseFunction_involutive G extra
  tail := Prod.fst
  accepts := fun e a b => match e.1 with
    | Sum.inl v => G.accepts (v, e.2) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v | w, d⟩ a b
    · change G.accepts (G.reverse (v, d)) b a = G.accepts (v, d) a b
      exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem pad_tail (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (pad G extra).tail = Prod.fst := rfl

@[simp] theorem pad_reverse_inl (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (v : V) (d : D) :
    (pad G extra).reverse (Sum.inl v, d) =
      (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2) := rfl

@[simp] theorem pad_reverse_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (w : Fin extra) (d : D) :
    (pad G extra).reverse (Sum.inr w, d) = (Sum.inr w, d) := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (extra : ℕ) (labeling : V ⊕ Fin extra → A)
    (v : V) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inl v, d) =
      G.edgeSatisfied (fun v => labeling (Sum.inl v)) (v, d) := by
  change G.accepts (v, d) (labeling (Sum.inl v))
      (labeling (Sum.inl (G.reverse (v, d)).1)) =
    G.accepts (v, d) (labeling (Sum.inl (G.tail (v, d))))
      (labeling (Sum.inl (G.tail (G.reverse (v, d)))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) (w : Fin extra) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inr w, d) = true := rfl

def extendLabeling (extra : ℕ) (defaultA : A) (labeling : V → A) : V ⊕ Fin extra → A :=
  Sum.elim labeling (fun _ => defaultA)

@[simp] theorem extendLabeling_inl (extra : ℕ) (defaultA : A) (labeling : V → A)
    (v : V) : extendLabeling extra defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem extendLabeling_inr (extra : ℕ) (defaultA : A) (labeling : V → A)
    (w : Fin extra) : extendLabeling extra defaultA labeling (Sum.inr w) = defaultA := rfl

variable (V : Type*) [Fintype V]

def extraVertices : ℕ := ExpanderFamily.size (Fintype.card V) - Fintype.card V

abbrev Vertex := V ⊕ Fin (extraVertices V)

theorem card_vertex : Fintype.card (Vertex V) = ExpanderFamily.size (Fintype.card V) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_sub_of_le (ExpanderFamily.le_size _)

noncomputable def familyVertexEquiv :
    Vertex V ≃ ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card V)) :=
  Fintype.equivOfCardEq (by
    rw [card_vertex, ExpanderFamily.card_vertex]
    rfl)

variable {V}

def paddedG (G : ConstraintGraph V (V × D) A) : ConstraintGraph (Vertex V) (Vertex V × D) A :=
  pad G (extraVertices V)

@[simp] theorem paddedG_tail (G : ConstraintGraph V (V × D) A) :
    (paddedG G).tail = Prod.fst := rfl

end UniqueGames.Foundations.PCP.VertexPadding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Preprocessing
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

noncomputable section

namespace UniqueGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

abbrev Vertex (G : ConstraintGraph V E A) := VertexPadding.Vertex (Regularization.Vertex G)
abbrev OverlayPort := Regularization.Port ⊕ ExpanderFamily.Port
abbrev Port := Bool × OverlayPort

def paddedGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Regularization.Port) A :=
  VertexPadding.paddedG (Regularization.graph G)

def overlayExpander (G : ConstraintGraph V E A) :
    PortGraph (Vertex G) ExpanderFamily.Port :=
  GraphTransport.reindex
    (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Regularization.Vertex G))))
    (VertexPadding.familyVertexEquiv (Regularization.Vertex G)).symm (Equiv.refl _)

def overlayGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × OverlayPort) A :=
  Overlay.constraintGraph (paddedGraph G) (overlayExpander G)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  LazyConstraint.constraintGraph (overlayGraph G)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  Overlay.originalPortGraph (graph G)

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) : (graph G).tail = Prod.fst := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

end UniqueGames.Foundations.PCP.Preprocessing
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ExpanderTables
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

def graph {v d : Nat} (table : Table v d) : PortGraph (Fin v) (Fin d) where
  rot := ZigzagGraphs.involutionEquiv (lookup table) (lookup_involutive table)
  rot_involutive := lookup_involutive table

@[simp] theorem graph_rot {v d : Nat} (table : Table v d) (x : Fin v × Fin d) :
    (graph table).rot x = lookup table x := rfl

def ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) : Table v d where
  rows := Vector.ofFn (fun i => rowIndex v d (G.rot ((rowIndex v d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
    exact (congrArg (rowIndex v d) (G.rot_involutive ((rowIndex v d).symm i))).trans
      ((rowIndex v d).apply_symm_apply i)

@[simp] theorem lookup_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d))
    (x : Fin v × Fin d) : lookup (ofGraph G) x = G.rot x := by
  simp only [lookup, reverseIndex, ofGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

theorem graph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

@[simp] theorem graph_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) :
    graph (ofGraph G) = G := graph_ext (lookup_ofGraph G)

end UniqueGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphGap
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

end UniqueGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingOverlayTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

def materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) : PortTables.Table n d :=
  PortTables.ofPortGraph
    (GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports)
    (fun x a b => G.accepts (x.1, ports.symm x.2) a b)
    (by
      intro x a b
      simp only [GraphTransport.reindex, Overlay.originalPortGraph,
        Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Equiv.refl_apply, Equiv.symm_apply_apply, Prod.map]
      convert G.reverse_accepts (x.1, ports.symm x.2) a b using 1 ; rfl)

@[simp] theorem accepts_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (x : Fin n × Fin d) (a b : PortTables.Label) :
    PortTables.accepts (materialize G ports) x a b =
      G.accepts (x.1, ports.symm x.2) a b := by
  exact PortTables.accepts_ofPortGraph _ _ _ x a b

end UniqueGames.Foundations.PCP.PreprocessingOverlayTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingPaddingTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem vertexEquiv_inl (h : n ≤ m) (v : Fin n) :
    vertexEquiv h (Sum.inl v) = v.castLE h := rfl

@[simp] theorem vertexEquiv_inr_val (h : n ≤ m) (v : Fin (m - n)) :
    (vertexEquiv h (Sum.inr v)).val = n + v.val := rfl

@[simp] theorem vertexEquiv_symm_old (h : n ≤ m) (v : Fin n) :
    (vertexEquiv h).symm (v.castLE h) = Sum.inl v :=
  (vertexEquiv h).symm_apply_apply (Sum.inl v)

def dartEquiv (h : n ≤ m) :
    (Fin n ⊕ Fin (m - n)) × Fin d ≃ Fin m × Fin d :=
  Equiv.prodCongr (vertexEquiv h) (Equiv.refl _)

@[simp] theorem dartEquiv_apply (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    dartEquiv h (v, p) = (vertexEquiv h v, p) := rfl

def sumGraph (table : Table n d) (m : Nat) :
    ConstraintGraph (Fin n ⊕ Fin (m - n))
      ((Fin n ⊕ Fin (m - n)) × Fin d) Label :=
  VertexPadding.pad (baseGraph table) (m - n)

def paddedGraph (table : Table n d) (h : n ≤ m) :
    ConstraintGraph (Fin m) (Fin m × Fin d) Label where
  reverse := ((dartEquiv h).symm.trans (sumGraph table m).reverse).trans (dartEquiv h)
  reverse_involutive e := by
    change dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h ((sumGraph table m).reverse
        ((dartEquiv h).symm e))))) = e
    rw [Equiv.symm_apply_apply, (sumGraph table m).reverse_involutive,
      Equiv.apply_symm_apply]
  tail := Prod.fst
  accepts e a b := (sumGraph table m).accepts ((dartEquiv h).symm e) a b
  reverse_accepts e a b := by
    change (sumGraph table m).accepts ((dartEquiv h).symm
      (dartEquiv h ((sumGraph table m).reverse ((dartEquiv h).symm e)))) b a = _
    rw [Equiv.symm_apply_apply]
    exact (sumGraph table m).reverse_accepts _ _ _

theorem paddedGraph_reverse_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).reverse (dartEquiv h e) =
      dartEquiv h ((sumGraph table m).reverse e) := by
  change dartEquiv h ((sumGraph table m).reverse
    ((dartEquiv h).symm (dartEquiv h e))) = _
  rw [Equiv.symm_apply_apply]

theorem paddedGraph_accepts_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) (a b : Label) :
    (paddedGraph table h).accepts (dartEquiv h e) a b =
      (sumGraph table m).accepts e a b := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e)) a b = _
  rw [Equiv.symm_apply_apply]

def pad (table : Table n d) (h : n ≤ m) : Table m d :=
  ofPortGraph
    { rot := (paddedGraph table h).reverse
      rot_involutive := (paddedGraph table h).reverse_involutive }
    (paddedGraph table h).accepts (paddedGraph table h).reverse_accepts

@[simp] theorem rotation_pad (table : Table n d) (h : n ≤ m) (e : Fin m × Fin d) :
    rotation (pad table h) e = (paddedGraph table h).reverse e := by
  exact rotation_ofPortGraph _ _ _ e

@[simp] theorem accepts_pad (table : Table n d) (h : n ≤ m)
    (e : Fin m × Fin d) (a b : Label) :
    accepts (pad table h) e a b = (paddedGraph table h).accepts e a b := by
  exact accepts_ofPortGraph _ _ _ e a b

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem baseGraph_pad (table : Table n d) (h : n ≤ m) :
    baseGraph (pad table h) = paddedGraph table h := by
  apply constraintGraph_ext
  · exact rotation_pad table h
  · rfl
  · funext e a b
    exact accepts_pad table h e a b

theorem rotation_pad_equiv (table : Table n d) (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h v, p) =
      (vertexEquiv h ((sumGraph table m).reverse (v, p)).1,
        ((sumGraph table m).reverse (v, p)).2) := by
  rw [rotation_pad]
  exact paddedGraph_reverse_equiv table h (v, p)

@[simp] theorem rotation_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    rotation (pad table h) (v.castLE h, p) =
      ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inl, baseGraph_reverse,
    vertexEquiv_inl] using rotation_pad_equiv table h (Sum.inl v) p

@[simp] theorem rotation_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h (Sum.inr v), p) =
      (vertexEquiv h (Sum.inr v), p) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inr] using
    rotation_pad_equiv table h (Sum.inr v) p

@[simp] theorem accepts_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) (a b : Label) :
    accepts (pad table h) (v.castLE h, p) a b = accepts table (v, p) a b := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inl v, p) a b

@[simp] theorem accepts_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) (a b : Label) :
    accepts (pad table h) (vertexEquiv h (Sum.inr v), p) a b = true := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inr v, p) a b

theorem paddedGraph_edgeSatisfied_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e))
    (labeling (dartEquiv h e).1)
    (labeling (dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h e)))).1) =
    (sumGraph table m).accepts e (labeling (vertexEquiv h e.1))
      (labeling (vertexEquiv h ((sumGraph table m).reverse e).1))
  simp only [Equiv.symm_apply_apply] ; rfl

theorem edgeSatisfied_pad_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  rw [baseGraph_pad]
  exact paddedGraph_edgeSatisfied_equiv table h labeling e

@[simp] theorem edgeSatisfied_pad_old (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin n) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (v.castLE h, p) =
      (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) (v, p) := by
  simpa only [dartEquiv_apply, vertexEquiv_inl, sumGraph,
    VertexPadding.edgeSatisfied_inl (baseGraph table) rfl] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inl v, p)

@[simp] theorem edgeSatisfied_pad_new (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin (m - n)) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (vertexEquiv h (Sum.inr v), p) = true := by
  simpa only [dartEquiv_apply, sumGraph, VertexPadding.edgeSatisfied_inr] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inr v, p)

end UniqueGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingCloudIndex
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                

namespace UniqueGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

def cloudDarts (t : Table) (v : Fin t.vertices) : List (Fin t.darts) :=
  (List.finRange t.darts).filter (fun e => decide (t.rows[e].tail = v))

@[simp] theorem mem_cloudDarts (t : Table) (v : Fin t.vertices) (e : Fin t.darts) :
    e ∈ cloudDarts t v ↔ t.rows[e].tail = v := by
  simp [cloudDarts]

theorem cloudDarts_nodup (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange t.darts)

def cloudSize (t : Table) (v : Fin t.vertices) : Nat := (cloudDarts t v).length

def cloudSelect (t : Table) (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    Cloud (semantics t) v :=
  ⟨(cloudDarts t v).get i,
    (mem_cloudDarts t v _).1 (List.get_mem (cloudDarts t v) i)⟩

def cloudRank (t : Table) (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    Fin (cloudSize t v) :=
  ⟨(cloudDarts t v).idxOf e.val,
    List.idxOf_lt_length_of_mem ((mem_cloudDarts t v e.val).2 e.property)⟩

@[simp] theorem cloudSelect_val (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) :
    (cloudSelect t v i).val = (cloudDarts t v).get i := rfl

@[simp] theorem cloudRank_val (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) :
    (cloudRank t v e).val = (cloudDarts t v).idxOf e.val := rfl

@[simp] theorem cloudSelect_cloudRank (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : cloudSelect t v (cloudRank t v e) = e := by
  apply Subtype.ext
  exact List.idxOf_get (cloudRank t v e).isLt

@[simp] theorem cloudRank_cloudSelect (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) : cloudRank t v (cloudSelect t v i) = i := by
  apply Fin.ext
  exact List.get_idxOf (cloudDarts_nodup t v) i

def cloudEquiv (t : Table) (v : Fin t.vertices) :
    Cloud (semantics t) v ≃ Fin (cloudSize t v) where
  toFun := cloudRank t v
  invFun := cloudSelect t v
  left_inv := cloudSelect_cloudRank t v
  right_inv := cloudRank_cloudSelect t v

abbrev PaddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :=
  Cloud (paddedGraph (semantics t) (fun u => Fin (padding u))) v

def paddedOld (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : PaddedCloud t padding v :=
  ⟨Sum.inl e.val, e.property⟩

def paddedNew (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (i : Fin (padding v)) : PaddedCloud t padding v :=
  ⟨Sum.inr ⟨v, i⟩, rfl⟩

def paddedCloudEquiv (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) : PaddedCloud t padding v ≃ Fin (cloudSize t v + padding v) :=
  (CloudPadding.paddedCloudEquiv (semantics t) (fun u => Fin (padding u)) v).trans
    ((Equiv.sumCongr (cloudEquiv t v) (Equiv.refl (Fin (padding v)))).trans
      finSumFinEquiv)

def paddedCloudRank (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    PaddedCloud t padding v → Fin (cloudSize t v + padding v) :=
  paddedCloudEquiv t padding v

@[simp] theorem paddedCloudRank_old (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    paddedCloudRank t padding v (paddedOld t padding v e) =
      Fin.castAdd (padding v) (cloudRank t v e) := rfl

@[simp] theorem paddedCloudRank_new (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudRank t padding v (paddedNew t padding v i) =
      Fin.natAdd (cloudSize t v) i := rfl

@[simp] theorem paddedCloudRank_old_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    (paddedCloudRank t padding v (paddedOld t padding v e)).val =
      (cloudRank t v e).val := rfl

@[simp] theorem paddedCloudRank_new_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    (paddedCloudRank t padding v (paddedNew t padding v i)).val =
      cloudSize t v + i.val := rfl

end UniqueGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_old _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

abbrev Vertex (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :=
  PaddedDart (GraphTables.semantics t) (fun v => Fin (padding v))

def vertexCount (t : GraphTables.Table) (padding : Fin t.vertices → Nat) : Nat :=
  t.darts + ∑ v, padding v

def vertexOrder (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :
    Vertex t padding ≃ Fin (vertexCount t padding) :=
  (Equiv.sumCongr (Equiv.refl _) (paddingOrder padding)).trans finSumFinEquiv

@[simp] theorem vertexOrder_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    (vertexOrder t padding (Sum.inl e)).val = e.val := rfl

@[simp] theorem vertexOrder_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (z : Σ v, Fin (padding v)) :
    (vertexOrder t padding (Sum.inr z)).val =
      t.darts + (paddingOrder padding z).val := rfl

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

@[simp] theorem portOrder_internal (q : Nat) (p : Fin q) :
    (portOrder q (Sum.inl p)).val = p.val := rfl

@[simp] theorem portOrder_inherited (q : Nat) :
    (portOrder q (Sum.inr ())).val = q := rfl

def cloudGraphs (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) (v : Fin t.vertices) :
    PortGraph (Cloud (paddedGraph (GraphTables.semantics t)
      (fun w => Fin (padding w))) v) (Fin q) :=
  GraphTransport.reindex (ExpanderTables.graph (tables v))
    (PreprocessingCloudIndex.paddedCloudEquiv t padding v).symm (Equiv.refl _)

def sourcePortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Vertex t padding) (Fin q ⊕ Unit) :=
  paddedReplacementPortGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def sourceGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    ConstraintGraph (Vertex t padding) (Vertex t padding × (Fin q ⊕ Unit))
      GraphTables.Label :=
  paddedReplacementGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def numberedPortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Fin (vertexCount t padding)) (Fin (q + 1)) :=
  GraphTransport.reindex (sourcePortGraph t padding tables)
    (vertexOrder t padding) (portOrder q)

def numberedAccepts (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1))
    (a b : GraphTables.Label) : Bool :=
  (sourceGraph t padding tables).accepts
    ((vertexOrder t padding).symm e.1, (portOrder q).symm e.2) a b

theorem numberedAccepts_transpose (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1)) (a b : GraphTables.Label) :
    numberedAccepts t padding tables ((numberedPortGraph t padding tables).rot e) b a =
      numberedAccepts t padding tables e a b := by
  obtain ⟨z, rfl⟩ := (Equiv.prodCongr (vertexOrder t padding) (portOrder q)).surjective e
  rcases z with ⟨v, p⟩
  simp only [numberedPortGraph, Equiv.prodCongr_apply, Prod.map_apply,
    GraphTransport.reindex_rot, numberedAccepts, Equiv.symm_apply_apply]
  exact (sourceGraph t padding tables).reverse_accepts (v, p) a b

def ofCloudTables (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortTables.Table (vertexCount t padding) (q + 1) :=
  PortTables.ofPortGraph (numberedPortGraph t padding tables)
    (numberedAccepts t padding tables) (numberedAccepts_transpose t padding tables)

@[simp] theorem rotation_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) =
      (vertexOrder t padding ((sourcePortGraph t padding tables).rot (v, p)).1,
        portOrder q ((sourcePortGraph t padding tables).rot (v, p)).2) := by
  rw [ofCloudTables, PortTables.rotation_ofPortGraph]
  exact GraphTransport.reindex_rot _ _ _ _ _

@[simp] theorem accepts_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) a b =
      (sourceGraph t padding tables).accepts (v, p) a b := by
  simp only [ofCloudTables, PortTables.accepts_ofPortGraph,
    numberedAccepts, Equiv.symm_apply_apply]

@[simp] theorem accepts_internal (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q (Sum.inl p)) a b = decide (a = b) := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin t.darts) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inl e), portOrder q (Sum.inr ())) a b =
      GraphTables.acceptsAt t.rows e a b := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (z : Σ v, Fin (padding v)) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inr z), portOrder q (Sum.inr ())) a b = true := by
  rw [accepts_ofCloudTables]
  rfl

end UniqueGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GenericGraphTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.GenericGraphTables

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

@[simp] theorem relationAt_relationOf (predicate : (Label q) → (Label q) → Bool) (a b : (Label q)) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows q n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

structure Table (q : Nat) where
  vertices : Nat
  darts : Nat
  rows : Rows q vertices darts
  valid : Valid rows

def semantics (table : (Table q)) : ConstraintGraph (Fin table.vertices) (Fin table.darts) (Label q) where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : (Table q)) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : (Table q)) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : (Table q)) (e : Fin table.darts) (a b : (Label q)) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : Rows q n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : (Table q) :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

end UniqueGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

def rowFromDart (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    GraphTables.DartRow (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  let edge := dart.1.1.1
  let event := dart.1.1.2
  let slot := dart.1.2
  let old := input.rows[edge]
  let head := input.rows[old.reverseIndex].tail
  { tail := Enumeration.vertexEquiv input.vertices input.darts q
      (if dart.2 then
        .inr (Queries.globalize old.tail head edge
          (Queries.query (GenericGraphTables.relationAt old.relation) event slot))
      else .inl (edge, event))
    reverseIndex := Enumeration.dartEquiv input.darts q (dart.1, !dart.2)
    relation := Relations.relationFromTable old.relation (decide (old.tail = head))
      event slot dart.2 }

def rows (input : GenericGraphTables.Table q) :
    GraphTables.Rows (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  Vector.ofFn (fun index =>
    rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index))

@[simp] theorem rows_at (input : GenericGraphTables.Table q)
    (index : Fin (Enumeration.dartCount input.darts q)) :
    (rows input)[index] =
      rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index) := by
  simp [rows]

theorem dartRow_ext {n m : Nat} {left right : GraphTables.DartRow n m}
    (ht : left.tail = right.tail) (hr : left.reverseIndex = right.reverseIndex)
    (hp : left.relation = right.relation) : left = right := by
  cases left
  cases right
  cases ht
  cases hr
  cases hp
  rfl

theorem relation_ext {left right : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt left a b = GraphTables.relationAt right a b) :
    left = right := by
  apply Vector.ext
  intro i hi
  let labels := GraphTables.relationIndex.symm (⟨i, hi⟩ : Fin 4096)
  have index : GraphTables.relationIndex labels = (⟨i, hi⟩ : Fin 4096) :=
    GraphTables.relationIndex.apply_symm_apply _
  have point := h labels.1 labels.2
  simpa only [GraphTables.relationAt, index, Fin.getElem_fin] using point

theorem rowFromDart_eq_graphRow (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    rowFromDart input dart =
      { tail := Enumeration.vertexEquiv input.vertices input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).tail dart)
        reverseIndex := Enumeration.dartEquiv input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).reverse dart)
        relation := GraphTables.relationOf (fun a b =>
          (AlphabetGraph.graph (GenericGraphTables.semantics input)).accepts dart
            (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)) } := by
  rcases dart with ⟨⟨⟨edge, event⟩, slot⟩, orientation⟩
  apply dartRow_ext
  · cases orientation with
    | false => rfl
    | true =>
      have query := Queries.globalize_query (GenericGraphTables.semantics input)
        edge event slot
      have predicate : (GenericGraphTables.semantics input).accepts edge =
          GenericGraphTables.relationAt input.rows[edge].relation := rfl
      rw [predicate] at query
      simpa only [rowFromDart, AlphabetGraph.graph, QueryIncidence.graph,
        QueryIncidence.tail, GenericGraphTables.semantics_tail,
        ConstraintGraph.head, GenericGraphTables.semantics_reverse,
        ite_true] using
        congrArg (fun address => Enumeration.vertexEquiv input.vertices input.darts q
          (.inr address)) query
  · rfl
  · apply relation_ext
    intro a b
    rw [GraphTables.relationAt_relationOf]
    have relation := Relations.relationAt_relation_graph (GenericGraphTables.semantics input)
      edge event slot orientation a b
    have predicate : (GenericGraphTables.semantics input).accepts edge =
        Relations.oldPredicate input.rows[edge].relation := rfl
    rw [predicate] at relation
    simp only [rowFromDart, Relations.relationFromTable,
      GenericGraphTables.semantics_tail, ConstraintGraph.head,
      GenericGraphTables.semantics_reverse] at relation ⊢
    exact relation

theorem rows_eq_graphRows (input : GenericGraphTables.Table q) :
    rows input = GraphTables.graphRows
      (GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv) := by
  apply Vector.ext
  intro i hi
  simp only [rows, GraphTables.graphRows, Vector.getElem_ofFn]
  exact rowFromDart_eq_graphRow input
    ((Enumeration.dartEquiv input.darts q).symm ⟨i, hi⟩)

theorem rows_valid (input : GenericGraphTables.Table q) : GraphTables.Valid (rows input) := by
  rw [rows_eq_graphRows]
  exact GraphTables.graphRows_valid _

def build (input : GenericGraphTables.Table q) : GraphTables.Table where
  vertices := Enumeration.vertexCount input.vertices input.darts q
  darts := Enumeration.dartCount input.darts q
  rows := rows input
  valid := rows_valid input

@[simp] theorem build_vertices (input : GenericGraphTables.Table q) :
    (build input).vertices = Enumeration.vertexCount input.vertices input.darts q := rfl

@[simp] theorem build_darts (input : GenericGraphTables.Table q) :
    (build input).darts = Enumeration.dartCount input.darts q := rfl

end UniqueGames.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_VerifierToCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

namespace UniqueGames.Foundations.PCP.VerifierToCNF

open Target

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: «c» :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: «c» :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, «c»] => simp [fillBits]
  | a :: b :: «c» :: d :: rest =>
    have ih := fillBits_length ((a || b) :: «c» :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: «c» :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

abbrev Pattern (q : Nat) := Fin q → Bool

def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.«variables» + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.«variables») : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.«variables» (finProdFinEquiv (finProdFinEquiv (e, p), j))

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.«variables» :=
  ⟨V.query e i, !(patternAt q p i)⟩

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.«variables» → Bool :=
  fun v => B (oldIndex V v)

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (v : Fin V.«variables») :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

end UniqueGames.Foundations.PCP.VerifierToCNF

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.PCP.FinalBooleanVerifier

open Target

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

abbrev verifier (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    VerifierToCNF.FiniteVerifier 12 where
  «variables» := n * 6
  events := m
  query := fun e i => Fin.addCases (motive := fun _ : Fin (6 + 6) => Fin (n * 6))
    (fun j : Fin 6 => bitIndex vertices (G.tail (edges.symm e)) j)
    (fun j : Fin 6 => bitIndex vertices (G.head (edges.symm e)) j) i
  accepts := fun e bits => G.accepts (edges.symm e)
    (fun j => bits (Fin.castAdd 6 j)) (fun j => bits (Fin.natAdd 6 j))

end UniqueGames.Foundations.PCP.FinalBooleanVerifier

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Encoding_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                               
section

namespace UniqueGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv

def labelIndex (label : Label) : Fin 64 := labelEquiv label

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

def relationAddress (bits : VerifierToCNF.Pattern 12) : Fin 4096 :=
  GraphTables.relationIndex (labelIndex (leftHalf bits), labelIndex (rightHalf bits))

def patternRelationIndex (p : VerifierToCNF.PatternIndex 12) : Fin 4096 :=
  relationAddress (VerifierToCNF.patternAt 12 p)

@[simp] theorem patternRelationIndex_eq (p : VerifierToCNF.PatternIndex 12) :
    patternRelationIndex p = relationAddress (VerifierToCNF.patternAt 12 p) := rfl

def tableGraph (table : GraphTables.Table) :
    ConstraintGraph (Fin table.vertices) (Fin table.darts) Label :=
  (GraphTables.semantics table).reindex (Equiv.refl _) (Equiv.refl _) labelEquiv.symm

@[simp] theorem tableGraph_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).tail e = table.rows[e].tail := rfl

@[simp] theorem tableGraph_reverse (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem tableGraph_accepts (table : GraphTables.Table) (e : Fin table.darts)
    (a b : Label) :
    (tableGraph table).accepts e a b =
      GraphTables.relationAt table.rows[e].relation (labelIndex a) (labelIndex b) := rfl

abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

end UniqueGames.Foundations.Complexity.FinalCNFPattern
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Encoding_MachineEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) («c» : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget «c».l
  var := («c».var, extraState)
  stk := tapes «c».stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

def program (haltTarget : Option (Λ ⊕ Λextra)) (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)) :
    Λ ⊕ Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .inl l => statement haltTarget (source l)
  | .inr l => extra l

theorem step_running (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (l : Λ) (state : σ) (sourceTapes : ∀ k, List (Γ k)) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes ⟨some l, state, sourceTapes⟩) =
      some (configuration haltTarget extraState extraTapes
        (stepAux (source l) state sourceTapes)) := by
  change some (stepAux (statement haltTarget (source l)) (state, extraState)
    (tapes sourceTapes extraTapes)) = _
  rw [stepAux_simulation]

theorem step_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (a b : Cfg Γ Λ σ) (h : step source a = some b) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes a) =
      some (configuration haltTarget extraState extraTapes b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [step] at h
    | some l =>
      have hb : stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      exact step_running haltTarget extraState extraTapes source extra l state sourceTapes

end UniqueGames.Foundations.Complexity.MachineEmbedding
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Encoding_MachineComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

end UniqueGames.Foundations.Complexity.MachineComposition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Encoding_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                       
section

namespace UniqueGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

theorem iterateSizeBound {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end UniqueGames.Foundations.Complexity.Runtime

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceContexts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Hastad.SourceContexts

open Target PCP

abbrev I (u : ℕ) := Fin u → Bool

end UniqueGames.Foundations.Hastad.SourceContexts

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Basic
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators

noncomputable section

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

end FiniteDistribution

structure Game (Q₁ Q₂ A₁ A₂ : Type*) [Fintype Q₁] [Fintype Q₂]
    [Fintype A₁] [Fintype A₂] where
  questions : FiniteDistribution (Q₁ × Q₂)
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def tupleQuestionEquiv (n : Nat) :
    (Fin n → Q₁ × Q₂) ≃ (Fin n → Q₁) × (Fin n → Q₂) where
  toFun questions := (fun i => (questions i).1, fun i => (questions i).2)
  invFun questions := fun i => (questions.1 i, questions.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { questions := (G.questions.iid n).transport (tupleQuestionEquiv n)
      accepts := fun x y a b => decide (∀ i, G.accepts (x i) (y i) (a i) (b i) = true) }

@[simp] theorem repetition_question_weight (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition n).questions.weight questions =
      ∏ i, G.questions.weight (questions.1 i, questions.2 i) := rfl

end Game

end

end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_Basic
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.CorrelatedSampling

def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

end FiniteWeights

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_FiniteTrials
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                    
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_ThresholdPartition
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                          
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

structure ThresholdInterval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

def splitPoint (I : ThresholdInterval) (t : ℝ) : ℝ := max I.lo (min t I.hi)

def splitLeft (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨I.lo, splitPoint I t, le_max_left _ _⟩

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

theorem split_cdf (I : ThresholdInterval) (t r : ℝ) :
    intervalCDF r (splitLeft I t) + intervalCDF r (splitRight I t) = intervalCDF r I := by
  unfold intervalCDF splitLeft splitRight
  ring

theorem accepted_interval_mass (I : ThresholdInterval) (r : ℝ) (hc : cutAt r I) :
    (if I.lo < r then I.hi - I.lo else 0) = intervalCDF r I := by
  by_cases hl : I.lo < r
  · have hu : I.hi ≤ r := hc.resolve_right (not_le_of_gt hl)
    simp [hl, intervalCDF, min_eq_right hu, min_eq_right (le_of_lt hl)]
  · have hr : r ≤ I.lo := le_of_not_gt hl
    simp [hl, intervalCDF, min_eq_left hr, min_eq_left (hr.trans I.valid)]

theorem splitLeft_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitLeft I t) := by
  by_cases h : I.lo ≤ t
  · exact Or.inl (max_le h (min_le_left _ _))
  · exact Or.inr (le_of_lt (lt_of_not_ge h))

theorem splitRight_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitRight I t) := by
  by_cases h : t ≤ I.hi
  · right
    change t ≤ max I.lo (min t I.hi)
    rw [min_eq_left h]
    exact le_max_right _ _
  · exact Or.inl (le_of_lt (lt_of_not_ge h))

theorem splitLeft_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitLeft I t) := by
  rcases h with h | h
  · exact Or.inl ((max_le I.valid (min_le_right _ _)).trans h)
  · exact Or.inr h

theorem splitRight_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitRight I t) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (le_max_left _ _))

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def unitThresholdInterval : ThresholdInterval := ⟨0, 1, by norm_num⟩

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight]; ring) thresholds
  simpa [unitThresholdInterval] using h

theorem partition_cdf (thresholds : List ℝ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) = r := by
  have h := partition_sum (intervalCDF r) (fun t I => split_cdf I t r) thresholds
  simpa [intervalCDF, unitThresholdInterval, min_eq_left h1, min_eq_right h0] using h

theorem splitAll_new_cuts (intervals : List ThresholdInterval) (t : ℝ) :
    ∀ I ∈ splitAll t intervals, cutAt t I := by
  induction intervals with
  | nil => intro I h; simp [splitAll] at h
  | cons J rest ih =>
      intro I h
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_cut J t
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_cut J t
        · exact ih I h

theorem splitAll_preserves_cuts (intervals : List ThresholdInterval) (t r : ℝ) :
    (∀ I ∈ intervals, cutAt r I) → ∀ I ∈ splitAll t intervals, cutAt r I := by
  induction intervals with
  | nil => intro _ I h; simp [splitAll] at h
  | cons J rest ih =>
      intro hc I h
      have hJ : cutAt r J := hc J (by simp)
      have hrest : ∀ K ∈ rest, cutAt r K := fun K hK => hc K (by simp [hK])
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_preserves_cut J t r hJ
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_preserves_cut J t r hJ
        · exact ih hrest I h

theorem partition_cuts (thresholds : List ℝ) (r : ℝ) :
    r ∈ thresholds → ∀ I ∈ thresholdPartition thresholds, cutAt r I := by
  induction thresholds with
  | nil => intro hr; simp at hr
  | cons t rest ih =>
      intro hr
      rcases List.mem_cons.mp hr with h | h
      · subst r; exact splitAll_new_cuts (thresholdPartition rest) t
      · exact splitAll_preserves_cuts (thresholdPartition rest) t r (ih h)

theorem sumOnIntervals_congr (f g : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∀ I ∈ intervals, f I = g I) → sumOnIntervals f intervals = sumOnIntervals g intervals := by
  induction intervals with
  | nil => intro _; rfl
  | cons J rest ih =>
      intro h
      have hJ := h J (by simp)
      have hr : ∀ I ∈ rest, f I = g I := fun I hI => h I (by simp [hI])
      simp only [sumOnIntervals, hJ, ih hr]

theorem partition_acceptance_mass (thresholds : List ℝ) (r : ℝ)
    (hr : r ∈ thresholds) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (fun I => if I.lo < r then I.hi - I.lo else 0)
      (thresholdPartition thresholds) = r := by
  calc
    _ = sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) :=
      sumOnIntervals_congr _ _ _ (fun I hI =>
        accepted_interval_mass I r (partition_cuts thresholds r hr I hI))
    _ = r := partition_cdf thresholds r h0 h1

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_Rectangle
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

theorem sum_div_const {ι : Type*} [Fintype ι] (f : ι → ℝ) («c» : ℝ) :
    (∑ i, f i) / «c» = ∑ i, f i / «c» := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

def rectangleDistribution [Nonempty α] (thresholds : List ℝ) :
    Games.FiniteDistribution (RectangleSeed thresholds α) where
  weight := rectangleWeight thresholds
  nonnegative := rectangleWeight_nonnegative thresholds
  normalized := rectangleWeight_normalized thresholds

theorem min_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : min x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [min_def, h, hx, hy]

theorem max_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : max x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [max_def, h, hx, hy]

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_TraceLaw
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) («c» : ℝ) :
    traceAverage w n (fun _ => «c») = «c» := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_LabelBound
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_SharedProfiles
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                      
section

namespace UniqueGames.Foundations.CorrelatedSampling

open scoped BigOperators

noncomputable section

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

theorem mem_profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) (k : κ) (s : S) : P k s ∈ profileThresholds P := by
  classical
  exact List.mem_map.mpr ⟨(k, s), by simp, rfl⟩

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

theorem uniformRejectionRate_nonnegative (S : Type*) [Fintype S] [Nonempty S] :
    0 ≤ uniformRejectionRate S := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hc₁ : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hc).2 (by simpa using hc₁)

theorem uniformRejectionRate_lt_one (S : Type*) [Fintype S] [Nonempty S] :
    uniformRejectionRate S < 1 := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hp : (0 : ℝ) < 1 / (Fintype.card S : ℝ) := div_pos (by norm_num) hc
  dsimp [uniformRejectionRate]
  linarith

theorem exists_uniformRejectionRate_pow_lt (S : Type*) [Fintype S] [Nonempty S]
    (η : ℝ) (hη : 0 < η) : ∃ n : ℕ, uniformRejectionRate S ^ n < η := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (uniformRejectionRate_nonnegative S) (uniformRejectionRate_lt_one S)
  exact (ht.eventually (gt_mem_nhds hη)).exists

end

end UniqueGames.Foundations.CorrelatedSampling
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace ExpandMachine

abbrev Data := ℕ × List ℕ

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_DenseEncodingBound
attribute [-simp] _root_.OAI.UniqueGames.BinaryEncoding.literalBits_length _root_.OAI.UniqueGames.BinaryEncoding.namesBitSize_nil _root_.OAI.UniqueGames.BinaryEncoding.parseLiteral_encoded _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace UniqueGames.BinaryFormula
open UniqueGames.Foundations

def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) (i : Fin 3) : «c»[i].name ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨«c», hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Nat :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

def compactClause (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) : Target.Clause (activeNames F).length :=
  #v[compactLiteral F «c»[0] (literal_mem_active F «c» hc 0),
    compactLiteral F «c»[1] (literal_mem_active F «c» hc 1),
    compactLiteral F «c»[2] (literal_mem_active F «c» hc 2)]

def compactClauses (F : Formula) : List (Target.Clause (activeNames F).length) :=
  F.clauses.attach.map (fun «c» => compactClause F «c».val «c».property)

def dense (F : Formula) : Target.Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Nat) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

@[simp] theorem eval_compact_restrict (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) (A : Nat → Bool) :
    (compactClause F «c» hc).eval (restrictAssignment F A) = «c».eval A := by
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F «c» hc).eval B = «c».eval (extendAssignment F B) := by
  have h₀ : «c»[0].name ∈ activeNames F := literal_mem_active F «c» hc 0
  have h₁ : «c»[1].name ∈ activeNames F := literal_mem_active F «c» hc 1
  have h₂ : «c»[2].name ∈ activeNames F := literal_mem_active F «c» hc 2
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, extendAssignment, h₀, h₁, h₂] ; rfl

@[simp] theorem dense_clause_count (F : Formula) :
    (dense F).clauses.length = F.clauses.length := by
  simp [dense, compactClauses]

theorem dense_completeness (F : Formula) (hs : F.Satisfiable) :
    (dense F).Satisfiable := by
  rcases hs with ⟨A, hA⟩
  refine ⟨restrictAssignment F A, ?_⟩
  intro d hd
  change d ∈ F.clauses.attach.map (fun «c» => compactClause F «c».val «c».property) at hd
  rcases List.mem_map.mp hd with ⟨«c», _, rfl⟩
  exact (eval_compact_restrict F «c».val «c».property A).trans (hA «c».val «c».property)

theorem dense_reflects (F : Formula) (hs : (dense F).Satisfiable) : F.Satisfiable := by
  rcases hs with ⟨B, hB⟩
  refine ⟨extendAssignment F B, ?_⟩
  intro «c» hc
  have hm : compactClause F «c» hc ∈ (dense F).clauses := by
    change _ ∈ F.clauses.attach.map (fun d => compactClause F d.val d.property)
    exact List.mem_map.mpr ⟨⟨«c», hc⟩, by simp, rfl⟩
  rw [← eval_compact_extend F «c» hc B]
  exact hB _ hm

end UniqueGames.BinaryFormula


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairEventMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover

noncomputable def finiteMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

end VertexCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


