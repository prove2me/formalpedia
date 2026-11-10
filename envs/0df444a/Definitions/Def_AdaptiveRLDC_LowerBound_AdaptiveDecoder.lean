-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_AdaptiveDecoder
-- name    : AdaptiveRLDC_LowerBound_AdaptiveDecoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:56:38.361585+00:00
-- url     : https://prove2.me/theorems/f137a579-f997-4782-8694-abeb07da12c5
-- title:
--   Adaptive relaxed decoder with arbitrary randomization
-- statement:
--   A binary code is any map $C:\{0,1\}^k\to\{0,1\}^n$. For each message index $i$, its randomized decoder is a probability law $\tau_i$ over the published adaptive decision trees, whose leaf alphabet here is $\{0,1,\bot\}$. The structural depth of each supported tree is at most $q$. Recursive evaluation and the recursively computed active query set retain adaptive branching and charge repeated queries.
--
--   The source guarantees are
--   $$\Pr[T(C(x))=x_i]\ge\alpha,\qquad\Pr[T(w)\in\{x_i,\bot\}]\ge\beta\quad\text{if }\operatorname{dist}(w,C(x))\le\delta.$$
--   Distance is the fraction of disagreeing coordinates. No linearity, systematic encoding, perfect completeness, spreadness or desired lower bound is part of this predicate. Tree laws allow arbitrary real randomness.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Definition 3.11; decision-tree representation §2.3, printed p.15, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance. Exact per-concept locations: §2.3 printed p.6/PDF p.7; Definition 3.11 printed p.15/PDF p.16.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights
import Definitions.Def_QAlgorithms_Defs_Classical

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- §2.3 / Definition 3.11: reuse the general published adaptive query tree, with an abort leaf. -/
abbrev DecodeTree (n : ℕ) := QAlgorithms.DecisionTree (Fin n) Bool (Option Bool)

/-- Structural maximum path length, charging repeated queries. -/
def treeDepth {n : ℕ} : DecodeTree n → ℕ
  | .leaf _ => 0
  | .node _ next => 1 + max (treeDepth (next false)) (treeDepth (next true))

/-- The set of indices actually queried, by recursion along the input-dependent path. -/
def queriedSet {n : ℕ} : DecodeTree n → Cube n → Sets n
  | .leaf _, _ => ∅
  | .node i next, y => insert i (queriedSet (next (y i)) y)

/-- An exact event probability under arbitrary tree weights, using PMF pushforward to Bool. -/
def treeProb {n : ℕ} (τ : PMF (DecodeTree n)) (E : DecodeTree n → Prop) : ℝ :=
  ((τ.map (fun T => decide (E T))) true).toReal

/-- Relative Hamming distance (only positive blocklengths are used in coding theorems). -/
def relativeDistance {n : ℕ} (y z : Cube n) : ℝ :=
  ((Finset.univ.filter (fun i => y i ≠ z i)).card : ℝ) / (n : ℝ)

/-- The three source decoder axioms only: depth, codeword completeness, and nearby-word soundness.
The tree law is fixed before the oracle word; no spreadness or lower-bound certificate is included. -/
def IsRelaxedDecoder {k n : ℕ} (C : Cube k → Cube n) (q : ℕ) (δ α β : ℝ)
    (τ : Fin k → PMF (DecodeTree n)) : Prop :=
  (∀ i T, T ∈ (τ i).support → treeDepth T ≤ q) ∧
  (∀ x i, α ≤ treeProb (τ i) (fun T => T.eval (C x) = some (x i))) ∧
  (∀ x i w, relativeDistance w (C x) ≤ δ →
    β ≤ treeProb (τ i) (fun T => T.eval w = some (x i) ∨ T.eval w = none))

end AdaptiveRLDC.LowerBound


