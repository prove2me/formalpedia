-- Prove2me | Definitions.Def_ProportionalTSP_Exact_Programs
-- name    : ProportionalTSP_Exact_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:25.944996+00:00
-- url     : https://prove2.me/theorems/f54bacf5-2f6b-49e5-9646-c01a50c9bb2e
-- title:
--   Input/output encodings and uniform computation specifications
-- statement:
--   Graph input contains the size and the adjacency matrix in natural cells, and original edge costs in scalar cells, with zero padding for missing edges. It contains no independent set or optimal-tour certificate. A successful tour output explicitly lists its vertices; malformed output cannot certify success or nonexistence.
--
--   Cross-matrix input supports the two implementation specifications: polynomial computation of the normalized prices and tight tree, and output-sensitive computation of the exact compatible-set list. In each case a single finite program and constants precede all sizes, weights and loads. Price output is a pair of sums per coordinate, interpreted as their difference. These predicates describe conclusions to be proved by the relevant milestones, rather than properties assumed of source inputs.
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), §2.3, Proposition 3.2, and exact arithmetic convention, PDF p. 2, 5–6, 9, 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Trees
import Definitions.Def_ProportionalTSP_Exact_RAM

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

def graphInput {n : ℕ} {K : Type} [Zero K]
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → K) : RAM.Input K where
  naturals := n :: (List.finRange n).flatMap (fun i =>
    (List.finRange n).map (fun j => if G.Adj i j then 1 else 0))
  values := (List.finRange n).flatMap (fun i =>
    (List.finRange n).map (fun j => if G.Adj i j then w s(i,j) else 0))

/-- Output is [0] for failure, or [1,v₀,...,vₙ₋₁] for a recovered tour. Malformed output
cannot certify success or nonexistence. The predicates explicitly test its decoded meaning. -/
def AnswerOutput {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (out : List ℕ) : Prop :=
  (out = [0] ∧ ¬ ∃ H, IsTour G H) ∨
  ∃ xs : List (Fin n), out = 1 :: xs.map Fin.val ∧ xs.length = n ∧ xs.Nodup ∧
    xs.toFinset = Finset.univ ∧ OptimalTour G w (cycleEdges xs)

def promised {n : ℕ} (α : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ R : Finset (Fin n), Independent G R ∧ α * n ≤ (R.card : ℝ)

def crossInput {m k : ℕ} (w : Fin m → Fin k → ℝ) (extra : List ℕ) : RAM.Input ℝ where
  naturals := [m,k] ++ extra
  values := (List.finRange m).flatMap (fun l => (List.finRange k).map (w l))

def subsetCode {m k : ℕ} (U : Finset (Vertex m k)) : ℕ :=
  (∑ l : Fin m, if Sum.inl l ∈ U then 2^l.val else 0) +
  (∑ r : Fin k, if Sum.inr r ∈ U then 2^(m+r.val) else 0)

def enumerationCode {m k : ℕ} (sets : List (Finset (Vertex m k))) : List ℕ := sets.map subsetCode

/-- The signed price output is two successive sums per coordinate. -/
def signedOutput (out : List ℝ) : List ℝ :=
  (List.range (out.length / 2)).map (fun i => out.getD (2*i) 0 - out.getD (2*i+1) 0)

def treeCode {m k : ℕ} [NeZero m] (w : Fin m → Fin k → ℝ) (d : Load m) : List ℕ :=
  (List.finRange m).flatMap (fun l => (List.finRange k).map (fun r =>
    if ∃ j ∈ tailSet d, canonical w (plusUnit (removeFirst d) j) r = l then 1 else 0))

def pricesCode {m k : ℕ} [NeZero m] (w : Fin m → Fin k → ℝ) (d : Load m) : List ℝ :=
  ((List.finRange m).filter (fun j => decide (j ∈ tailSet d))).map (normalizedPrices w d)

/-- Uniform polynomial implementation, including matching, with a signed output convention.
This predicate is asserted as a conclusion by Lemma 2.10, never assumed of an input. -/
def PolynomialTreeComputation : Prop :=
  ∃ P : RAM.Program, ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ,
    ∀ (m k : ℕ) [NeZero m], 1 ≤ k → k ≤ m →
    ∀ (w : Fin m → Fin k → ℝ), Generic w → ∀ d : Load m, feasible k d →
      ∃ t : ℕ, RAM.Halts P (crossInput w ((List.finRange m).map d)) t ∧
        (t : ℝ) ≤ C * (m+k+1)^q ∧
        (RAM.run P (crossInput w ((List.finRange m).map d)) t).out.reverse = treeCode w d ∧
        let out := (RAM.run P (crossInput w ((List.finRange m).map d)) t).realOut.reverse
        out.length = 2 * (pricesCode w d).length ∧ signedOutput out = pricesCode w d

/-- Uniform output-sensitive implementation of the exact enumeration list. -/
def EfficientEnumeration : Prop :=
  ∃ P : RAM.Program, ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ,
    ∀ (m k : ℕ) [NeZero m] [NeZero k], k ≤ m →
    ∀ (w : Fin m → Fin k → ℝ), Generic w →
      ∃ t : ℕ, RAM.Halts P (crossInput w []) t ∧
        (t : ℝ) ≤ C * (m+k+1)^q * outputCount m k ∧
        (RAM.run P (crossInput w []) t).out.reverse = enumerationCode (enumeration w)

end ProportionalTSP.Exact


