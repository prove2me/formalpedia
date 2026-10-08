-- Prove2me | Definitions.Def_SATVariance
-- name    : SATVariance
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.68144+00:00
-- url     : https://prove2.me/theorems/a551111b-d0d9-4614-a276-3a3f98e70f35
-- statement:
--   For natural numbers n and k, an Assignment is a Boolean value for each of n variables. A Clause of width k is a choice of a k-element set of variables together with a Boolean value for each chosen variable; the space of clauses is finite with the discrete sigma-algebra, and clauseLaw is the uniform probability measure on it. An assignment satisfies a clause if it agrees with the clause on at least one of the clause's variables. A Stream is an infinite sequence of clauses, and streamLaw is the infinite product of clauseLaw, so the clauses are independent and uniform. PrefixSAT(ω,m) says some assignment satisfies each of the first m clauses ω 0,...,ω(m-1). firstFailure(ω) is the least m for which PrefixSAT fails, taken in the extended naturals (infinite if no such m exists), and H(ω) is its real-valued natural-number truncation, which is 0 when it is infinite. cap(n,B) is the floor of B·n, and T(B,ω) is the truncation to a real number of the minimum of firstFailure(ω) and cap(n,B). The normalizing quantity ell(k,n) equals log(e·n) when k=3 and 1 otherwise, and U(k) equals log 2 divided by -log(1-2^(-k)). These are only definitions of the random k-SAT clause-stream setting and the associated quantities; no theorem or variance bound is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SATVariance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SATVariance.lean; bytes 16..1524
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

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

def PrefixSAT {n k : ℕ} (ω : Stream n k) (m : ℕ) : Prop :=
  ∃ a : Assignment n, ∀ i < m, Satisfies (ω i) a

def firstFailure {n k : ℕ} (ω : Stream n k) : ℕ∞ :=
  sInf ((fun m : ℕ => (m : ℕ∞)) '' {m | ¬ PrefixSAT ω m})

def H {n k : ℕ} (ω : Stream n k) : ℝ := (firstFailure ω).toNat

def cap (n : ℕ) (B : ℝ) : ℕ := ⌊B * n⌋₊

def T {n k : ℕ} (B : ℝ) (ω : Stream n k) : ℝ :=
  (min (firstFailure ω) (cap n B : ℕ∞)).toNat

def ell (k n : ℕ) : ℝ :=
  if k = 3 then Real.log (Real.exp 1 * n) else 1

def U (k : ℕ) : ℝ := Real.log 2 / (-Real.log (1 - ((2 : ℝ) ^ k)⁻¹))



end RandomKSAT
end
end OAI


