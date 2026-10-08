-- Prove2me | Definitions.Def_ContingencyTables
-- name    : ContingencyTables
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.061784+00:00
-- url     : https://prove2.me/theorems/a37b26df-4a6d-4d2c-a79e-6e1f04b3669e
-- statement:
--   For finite index sets I and J, a contingency table with margins r:I→ℕ and c:J→ℕ is a matrix X:I→J→ℕ whose row sums are r and column sums are c; a bounded table additionally satisfies Xᵢⱼ≤bᵢⱼ. Every entry is at most its row sum and the total row sum, so both table collections are finite. Computation uses a fixed finite randomized Turing machine with an eight-symbol tape alphabet: each step consumes one fair random bit and writes, moves, or halts, and halted configurations remain unchanged. Natural numbers have delimited binary encodings; integers include a sign, and rationals encode their reduced numerator and positive denominator. Matrices are encoded in row order, and margin inputs include both dimensions. An output requires halting with the specified encoding on the tape to the right of the head, including the head. Output and halting masses at time t are the fractions of the 2ᵗ bit strings producing those events. Three algorithmic existence propositions are defined, each requiring its own uniform machine and natural constants C>0 and d. Write N=Σᵢrᵢ and Sₖ=m+n+⌈log₂(N+1)⌉+k+1. BoundedSamplingStatement requires that, for every pair of natural dimensions, margins with equal totals, and integer k≥1, the machine given the margins and k halts on every random tape within C Sₖᵈ steps with a feasible table; its output distribution has total variation distance at most 2⁻ᵏ from the uniform distribution on all feasible tables. ExactSamplingStatement instead uses only the margins as input: every halted output is feasible, each table's output mass tends to the reciprocal of the number of tables, halting probability tends to one, and the tail sequence 1−P(halted by t) is summable with sum at most C S₀ᵈ. CountingStatement concerns positive dimensions, equal margin totals, arbitrary entry bounds, and rational 0<ε,δ<1. Let M be the number of bounded tables and L the length of the encoded dimensions, margins, bounds, ε, and δ. Within t=C(L+⌈ε⁻¹⌉+⌈log₂⌈δ⁻¹⌉⌉+1)ᵈ steps, every random tape must halt with a nonnegative rational output; if M=0, every output is exactly zero. With probability at least 1−δ, the output q satisfies (1−ε)M≤q≤(1+ε)M. These are definitions of propositions asserting such algorithms, rather than proofs of their existence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContingencyTables.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContingencyTables.lean; bytes 16..9063
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace MatchingFPRAS

abbrev Symbol := Fin 8

/-- Binary numeral followed by a delimiter. Tape blank is 0; bits use 1 and 2. -/
def encodeNat (n : ℕ) : List Symbol :=
  (Nat.bits n).map (fun b => if b then 2 else 1) ++ [3]

def encodeInt (z : ℤ) : List Symbol :=
  (if z < 0 then [5] else [4]) ++ encodeNat z.natAbs

/-- A rational encoded by its reduced numerator and positive denominator. -/
def encodeRat (q : ℚ) : List Symbol := encodeInt q.num ++ encodeNat q.den

/-- A uniform randomized Post-Turing machine: a single finite transition table. -/
structure RandomMachine where
  states : ℕ
  transition : Fin (states + 1) → Symbol → Bool →
    Option (Fin (states + 1) × Turing.TM0.Stmt Symbol)

structure Configuration (A : RandomMachine) where
  state : Option (Fin (A.states + 1))
  tape : Turing.Tape Symbol

/-- A halted configuration is absorbing. Each nonhalting tick is exactly one
write or one move, or the detection of halt. -/
def tick (A : RandomMachine) (c : Configuration A) (bit : Bool) : Configuration A :=
  match c.state with
  | none => c
  | some s => match A.transition s c.tape.head bit with
    | none => ⟨none, c.tape⟩
    | some (s', action) =>
      ⟨some s', match action with
        | .move d => c.tape.move d
        | .write a => c.tape.write a⟩

def initial (A : RandomMachine) (input : List Symbol) : Configuration A :=
  ⟨some 0, Turing.Tape.mk₁ input⟩

/-- Bounded execution on a finite prefix of the random tape. -/
def run (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) : Configuration A :=
  (List.ofFn bits).foldl (tick A) (initial A input)

def Outputs (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) (q : ℚ) : Prop :=
  (run A input bits).state = none ∧
    (run A input bits).tape.right₀ = Turing.ListBlank.mk (encodeRat q)

end MatchingFPRAS

namespace ContingencyTables

open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

def HasMargins (X : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) : Prop :=
  (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j)

def Table (r : I → ℕ) (c : J → ℕ) := {X : I → J → ℕ // HasMargins X r c}

def BoundedTable (r : I → ℕ) (c : J → ℕ) (b : I → J → ℕ) :=
  {X : Table r c // ∀ i j, X.val i j ≤ b i j}

theorem entry_le_row {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) (i : I) (j : J) : X i j ≤ r i := by
  rw [← h.1 i]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)

theorem entry_le_total {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) (i : I) (j : J) : X i j ≤ ∑ i, r i :=
  (entry_le_row h i j).trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i))

instance table_finite (r : I → ℕ) (c : J → ℕ) : Finite (Table r c) := by
  let encode : Table r c → I → J → Fin ((∑ i, r i) + 1) :=
    fun X i j => ⟨X.val i j, Nat.lt_succ_of_le (entry_le_total X.property i j)⟩
  apply Finite.of_injective encode
  intro X Y h
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

noncomputable instance table_fintype (r : I → ℕ) (c : J → ℕ) : Fintype (Table r c) :=
  Fintype.ofFinite _

noncomputable instance boundedTable_fintype (r : I → ℕ) (c : J → ℕ) (b : I → J → ℕ) :
    Fintype (BoundedTable r c b) := by
  classical
  unfold BoundedTable
  infer_instance

end ContingencyTables

namespace ContingencyTables.Algorithms

open scoped BigOperators
open Filter

abbrev Machine := MatchingFPRAS.RandomMachine
abbrev Symbol := MatchingFPRAS.Symbol

def encodeMatrix {m n : ℕ} (X : Fin m → Fin n → ℕ) : List Symbol :=
  ((List.ofFn fun i => (List.ofFn fun j => MatchingFPRAS.encodeNat (X i j)).flatten)).flatten

def encodeMargins {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) : List Symbol :=
  MatchingFPRAS.encodeNat m ++ MatchingFPRAS.encodeNat n ++
    (List.ofFn fun i => MatchingFPRAS.encodeNat (r i)).flatten ++
    (List.ofFn fun j => MatchingFPRAS.encodeNat (c j)).flatten

def encodeSamplingInput {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) : List Symbol :=
  encodeMargins r c ++ MatchingFPRAS.encodeNat k

def encodeCountingInput {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (ε δ : ℚ) : List Symbol :=
  encodeMargins r c ++ encodeMatrix b ++ MatchingFPRAS.encodeRat ε ++ MatchingFPRAS.encodeRat δ

/-- The tape alphabet has positive cardinality. -/
theorem alphabetSize_neZero : NeZero (8 : ℕ) := inferInstance

/-- A halted tape contains the row-major binary matrix encoding. -/
def OutputsTable (A : Machine) (input : List Symbol) {t m n : ℕ}
    (bits : Fin t → Bool) (X : Fin m → Fin n → ℕ) : Prop :=
  (MatchingFPRAS.run A input bits).state = none ∧
    @Turing.Tape.right₀ MatchingFPRAS.Symbol (@Fin.instInhabited 8 alphabetSize_neZero)
      (MatchingFPRAS.run A input bits).tape =
    @Turing.ListBlank.mk Symbol (@Fin.instInhabited 8 alphabetSize_neZero) (encodeMatrix X)

noncomputable def tableMass (A : Machine) (input : List Symbol) (t : ℕ)
    {m n : ℕ} (X : Fin m → Fin n → ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun bits : Fin t → Bool => OutputsTable A input bits X).card : ℝ) /
    (2 : ℝ) ^ t

noncomputable def haltMass (A : Machine) (input : List Symbol) (t : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun bits : Fin t → Bool =>
      (MatchingFPRAS.run A input bits).state = none).card : ℝ) / (2 : ℝ) ^ t

def samplingSize (n : ℕ) {m : ℕ} (r : Fin m → ℕ) (k : ℕ) : ℕ :=
  m + n + Nat.clog 2 ((∑ i, r i) + 1) + k + 1

/-- Paper 200-01, Theorem main(i): bounded runtime on every random tape
and total variation at most `2⁻ᵏ`, with freely varying dimensions. -/
def BoundedSamplingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j → ∀ k : ℕ, 1 ≤ k →
        let input := encodeSamplingInput r c k
        let t := C * (samplingSize n r k) ^ d
        (∀ bits : Fin t → Bool, ∃ X : Table r c, OutputsTable A input bits X.val) ∧
        (∑ X : Table r c,
          |tableMass A input t X.val - (Fintype.card (Table r c) : ℝ)⁻¹|) / 2 ≤
            ((2 : ℝ) ^ k)⁻¹

/-- Paper 200-01, Theorem main(ii): every halted output is feasible, each
table has limiting mass `1/|Ω|`, termination has probability one, and the
expected number of bit operations is bounded by a uniform polynomial. -/
def ExactSamplingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j →
        let input := encodeMargins r c
        let tail : ℕ → ℝ := fun t => 1 - haltMass A input t
        (∀ t (bits : Fin t → Bool), (MatchingFPRAS.run A input bits).state = none →
          ∃ X : Table r c, OutputsTable A input bits X.val) ∧
        (∀ X : Table r c, Tendsto (fun t => tableMass A input t X.val) atTop
          (nhds ((Fintype.card (Table r c) : ℝ)⁻¹))) ∧
        Tendsto (haltMass A input) atTop (nhds 1) ∧
        Summable tail ∧
        tsum tail ≤ C * (samplingSize n r 0) ^ d

noncomputable def count {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) : ℕ := Fintype.card (BoundedTable r c b)

def countingTime (C d : ℕ) {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (ε δ : ℚ) : ℕ :=
  C * ((encodeCountingInput r c b ε δ).length + ⌈ε⁻¹⌉₊ +
    Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ d

noncomputable def goodCountingTapes (A : Machine) {m n : ℕ}
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (ε δ : ℚ) (t : ℕ) : Finset (Fin t → Bool) := by
  classical
  exact Finset.univ.filter fun bits => ∃ q : ℚ,
    MatchingFPRAS.Outputs A (encodeCountingInput r c b ε δ) bits q ∧
      (1 - ε) * count r c b ≤ q ∧ q ≤ (1 + ε) * count r c b

/-- Paper 200-02, Theorem main. The input length includes the rational
accuracy parameters, and infeasible inputs always produce exactly zero. -/
def CountingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j →
      ∀ ε δ : ℚ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        let input := encodeCountingInput r c b ε δ
        let t := countingTime C d r c b ε δ
        (∀ bits : Fin t → Bool, ∃ q : ℚ, 0 ≤ q ∧ MatchingFPRAS.Outputs A input bits q) ∧
        (count r c b = 0 → ∀ bits : Fin t → Bool, MatchingFPRAS.Outputs A input bits 0) ∧
        ((goodCountingTapes A r c b ε δ t).card : ℚ) / (2 : ℚ) ^ t ≥ 1 - δ

end ContingencyTables.Algorithms

namespace ContingencyTables



end ContingencyTables
end OAI


