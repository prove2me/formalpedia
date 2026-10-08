-- Prove2me | Definitions.Def_SATSharpness
-- name    : SATSharpness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.461999+00:00
-- url     : https://prove2.me/theorems/f12d91b6-321b-4696-b2b6-0de58c768bff
-- statement:
--   A clause on n variables of width k is a choice of a k-element set of variables together with a Boolean sign for each chosen variable; there are finitely many clauses, and the clause space carries the discrete measurable structure. An assignment is a Boolean vector in Fin n → Bool, and it satisfies a clause when at least one chosen variable takes exactly the sign prescribed by the clause. clauseLaw is the uniform probability measure on clauses, and streamLaw is the infinite product of countably many independent copies of it, giving a random infinite sequence of clauses. For a finite set S of assignments on u variables and a number g of clauses, SetSAT holds when some assignment in S satisfies each of the first g clauses of the stream, and blockKill is the real-valued probability that this fails, that is, that no assignment in S survives the first g clauses. favg is the average of a real function over a finite type. clauseStep sends a function f on finite sets of assignments to the function that maps S to the average, over all clauses c of width s, of f applied to the subset of S satisfying c. alive(S) is 1 if S is nonempty and 0 otherwise, survival(S,m) is the m-fold iterate of clauseStep applied to alive and evaluated at S, and lifetime(S) is the infinite sum of survival(S,m) over all natural numbers m, a tsum that is zero by Lean convention if the series is not summable. The block only defines these notions and states no theorem about them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SATSharpness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SATSharpness.lean; bytes 16..1728
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

abbrev Assignment (n : ℕ) := Fin n → Bool

def Clause (n k : ℕ) :=
  (s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)

instance clauseFintype (n k : ℕ) : Fintype (Clause n k) := by
  classical
  unfold Clause
  infer_instance

instance clauseMeasurableSpace (n k : ℕ) : MeasurableSpace (Clause n k) := ⊤

instance clauseMeasurableSingletonClass (n k : ℕ) :
    MeasurableSingletonClass (Clause n k) := ⟨fun _ => trivial⟩

def Satisfies {n k : ℕ} (c : Clause n k) (a : Assignment n) : Prop :=
  ∃ v : c.1.1, a v = c.2 v

abbrev Stream (n k : ℕ) := ℕ → Clause n k

def clauseLaw (n k : ℕ) : Measure (Clause n k) := uniformOn Set.univ

def streamLaw (n k : ℕ) : Measure (Stream n k) :=
  Measure.infinitePi (fun _ : ℕ => clauseLaw n k)

def SetSAT {u s : ℕ} (S : Finset (Assignment u)) (ω : Stream u s) (g : ℕ) : Prop :=
  ∃ a ∈ S, ∀ i < g, Satisfies (ω i) a

def blockKill (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) : ℝ :=
  (streamLaw u s {ω | ¬ SetSAT S ω g}).toReal

def favg.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

def clauseStep (u s : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) : ℝ :=
  favg fun c : Clause u s => f (S.filter (Satisfies c))

def alive (u : ℕ) (S : Finset (Assignment u)) : ℝ := if S.Nonempty then 1 else 0

def survival (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) : ℝ :=
  (clauseStep u s)^[m] (alive u) S

def lifetime (u s : ℕ) (S : Finset (Assignment u)) : ℝ := ∑' m, survival u s S m



end RandomKSAT
end
end OAI


