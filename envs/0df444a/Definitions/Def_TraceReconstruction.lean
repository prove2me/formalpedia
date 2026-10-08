-- Prove2me | Definitions.Def_TraceReconstruction
-- name    : TraceReconstruction
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:33.726674+00:00
-- url     : https://prove2.me/theorems/46a25436-3568-45d8-a949-7214e6246643
-- statement:
--   Words of length n are Boolean strings Fin n → Bool, masks are Boolean vectors of the same length, and a trace is a list of Booleans. traceOfMask(x,a) keeps exactly the bits x_i at positions where a_i is true, in order, so the observer sees only the resulting list. With deletion probability q, maskWeight(q,a) is the product over positions of 1−q when a_i is true and q when it is false, and traceMass(q,x,w) is the sum of the weights of all masks that turn x into the trace w. traceSpace(n) is the finite set of all lists of every length k from 0 to n arising as List.ofFn of a word of length k, and traceTV(q,x,y) is half the sum over this space of |traceMass(q,x,w) − traceMass(q,y,w)|. An estimator from m traces is a function A assigning to each m-tuple of traces z and each word x a real number A(z,x), required to be nonnegative and to sum to 1 over x for every z, so it is a conditional distribution over guessed inputs. reconstructionSuccess(q,A,x) is the sum over m independent masks a₁,…,a_m of the product of their weights times A applied to the traces traceOfMask(x,a_j), evaluated at x; no retained positions are revealed. SufficientBudget(n,q,s,m) says some estimator achieves success probability at least s on every word x. sampleComplexity(n,q,s) is the infimum, in the extended nonnegative reals, of those natural numbers m for which SufficientBudget holds, equal to infinity if none does. minTraceTV(n,q) is the real infimum of traceTV(q,x,y) over pairs of distinct words x≠y of length n. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TraceReconstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TraceReconstruction.lean; bytes 16..2472
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Mask (n : ℕ) := Fin n → Bool
abbrev Trace := List Bool

/-- `true` retains the bit. The observer gets only the resulting list. -/
def traceOfMask {n : ℕ} (x : Word n) (a : Mask n) : Trace :=
  ((List.finRange n).filter fun i => a i).map x

/-- The deletion-mask probability, with deletion probability `q`. -/
def maskWeight {n : ℕ} (q : ℝ) (a : Mask n) : ℝ :=
  ∏ i, if a i then 1 - q else q

/-- Law of a single complete trace. -/
def traceMass {n : ℕ} (q : ℝ) (x : Word n) (w : Trace) : ℝ :=
  ∑ a : Mask n, if traceOfMask x a = w then maskWeight q a else 0

/-- All possible complete outputs from length-n inputs, with lengths included. -/
def traceSpace (n : ℕ) : Finset Trace :=
  Finset.univ.biUnion fun k : Fin (n + 1) =>
    Finset.univ.image fun x : Word k.val => List.ofFn x

/-- 1/2 sum of absolute differences, on the full finite output space. -/
def traceTV {n : ℕ} (q : ℝ) (x y : Word n) : ℝ :=
  (1 / 2 : ℝ) * ∑ w ∈ traceSpace n, |traceMass q x w - traceMass q y w|

/-- The estimator may depend arbitrarily on n, q and every complete sample.
    Its value is its conditional probability of reporting the given input. -/
def IsEstimator {n m : ℕ} (A : (Fin m → Trace) → Word n → ℝ) : Prop :=
  (∀ z x, 0 ≤ A z x) ∧ (∀ z, ∑ x : Word n, A z x = 1)

/-- Independent masks generate independent complete traces; no retained
    positions, boundaries or other latent variables are revealed to A. -/
def reconstructionSuccess {n m : ℕ} (q : ℝ)
    (A : (Fin m → Trace) → Word n → ℝ) (x : Word n) : ℝ :=
  ∑ a : Fin m → Mask n,
    (∏ j, maskWeight q (a j)) * A (fun j => traceOfMask x (a j)) x

def SufficientBudget (n : ℕ) (q s : ℝ) (m : ℕ) : Prop :=
  ∃ A : (Fin m → Trace) → Word n → ℝ,
    IsEstimator A ∧ ∀ x, s ≤ reconstructionSuccess q A x

/-- Natural fixed sample budget; infimum of the empty set is infinity. -/
noncomputable def sampleComplexity (n : ℕ) (q s : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ m : ℕ, SufficientBudget n q s m ∧ t = (m : ℝ≥0∞)}

/-- The real infimum is a minimum for n>0 (a nonempty finite set). -/
noncomputable def minTraceTV (n : ℕ) (q : ℝ) : ℝ :=
  sInf {t | ∃ x y : Word n, x ≠ y ∧ t = traceTV q x y}

open Filter
open scoped Topology Classical ENNReal



end TraceReconstruction
end
end OAI


