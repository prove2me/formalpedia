-- Prove2me | Definitions.Def_ZonotopeContainment_AdaptiveSampling_Supplement_OracleModel
-- name    : ZonotopeContainment_AdaptiveSampling_Supplement_OracleModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:48:31.714296+00:00
-- url     : https://prove2.me/theorems/48df069c-cf63-4780-82c3-3adee926b822
-- title:
--   Symmetric convex bodies, randomized membership-query algorithms and the gap answer
-- statement:
--   This file fixes the oracle model of §1.1 and §4 of the paper for the lower bound on general convex-body containment.
--
--   1. **Bodies.** In dimension $d$, a set $K\subseteq\mathbb R^d$ is an *origin-symmetric body* if it is convex, compact, satisfies $K=-K$, and $\tfrac1d B_2^d\subseteq K\subseteq d\,B_2^d$, where $B_2^d$ is the closed Euclidean unit ball. The radii $1/d$ and $d$ are the inner and outer radii carried by the oracle description, fixed as functions of $d$.
--   2. **Algorithms.** A randomized query algorithm with $q$ queries and $m$ coins reads a uniformly random string $\omega\in\{0,1\}^m$. Its $k$-th query is a pair (which body, $K$ or $Q$; a point $x\in\mathbb R^d$) chosen as an arbitrary function of $\omega$ and of the $k$ previous answers, so queries are adaptive. After $q$ queries it outputs Yes or No as an arbitrary function of $\omega$ and all answers. Computation is not bounded and query points are arbitrary real vectors.
--   3. **Oracle.** Each query is answered by exact membership of the point in the chosen body, boundary points included.
--   4. **Gap answer.** For a factor $s$, the answer Yes is valid when $K\subseteq Q$ and the answer No is valid when $sK\not\subseteq Q$; either answer is valid when both hold.
--   5. **Success.** The success count is the number of coin strings $\omega$ on which the algorithm's answer on $(K,Q)$ is valid; the success probability is this count divided by $2^m$.
--
--   These objects are what the impossibility statement for gap containment (Theorem 4.3) quantifies over.
--
--   **Formalization Note** The query is a pair `Bool × E d` with `true` meaning a query to $K$; `run` evaluates the adaptive interaction by recursion on the query index.
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), §1.1 eq. (2), pp. 2–3; §4, p. 13; Lemma 4.4 and proof of Theorem 4.3, pp. 13–14; §5 gap convention, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Geometry

noncomputable section
open scoped Pointwise

namespace ZonotopeContainment.AdaptiveSampling.Supplement

/-- §1.1 and §4 (pp. 2–3, 13): an origin-symmetric convex body, compact, whose oracle
description carries the inner radius 1/d and the outer radius d. -/
def SymBody (d : ℕ) (K : Set (E d)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (∀ x ∈ K, -x ∈ K) ∧
    Metric.closedBall (0 : E d) (1 / (d : ℝ)) ⊆ K ∧ K ⊆ Metric.closedBall (0 : E d) (d : ℝ)

/-- A randomized adaptive query algorithm in dimension d with exactly q membership queries
and m uniform coin flips. Query k is chosen from the coins and the k previous answers: the
Boolean says which body is asked (true = K, false = Q), the vector is the query point. The
final answer (true = Yes, "K ⊆ Q"; false = No) depends on the coins and all q answers.
There is no bound on the computation. -/
structure QueryAlg (d q m : ℕ) where
  query : (Fin m → Bool) → (k : Fin q) → (Fin k → Bool) → Bool × E d
  output : (Fin m → Bool) → (Fin q → Bool) → Bool

/-- Exact membership oracle for the pair (K, Q): `(true, x)` asks x ∈ K, `(false, x)` asks
x ∈ Q. Boundary points are answered exactly. -/
def oracle {d : ℕ} (K Q : Set (E d)) (a : Bool × E d) : Bool := by
  classical
  exact if a.1 then decide (a.2 ∈ K) else decide (a.2 ∈ Q)

/-- The answer to query i on coins ω, computed from the answers to the earlier queries. -/
def answer {d q m : ℕ} (A : QueryAlg d q m) (K Q : Set (E d)) (ω : Fin m → Bool) :
    (i : ℕ) → i < q → Bool
  | i, hi => oracle K Q (A.query ω ⟨i, hi⟩
      (fun j => answer A K Q ω j.1 (lt_trans j.2 hi)))
termination_by i => i
decreasing_by exact j.2

/-- The algorithm's answer on the instance (K, Q) with coins ω. -/
def run {d q m : ℕ} (A : QueryAlg d q m) (K Q : Set (E d)) (ω : Fin m → Bool) : Bool :=
  A.output ω (fun i => answer A K Q ω i.1 i.2)

/-- Gap convention (eq. (2), p. 2; §5, p. 14): Yes is valid iff K ⊆ Q, No is valid iff
sK ⊈ Q; either is valid when both hold. -/
def Correct {d : ℕ} (s : ℝ) (K Q : Set (E d)) (out : Bool) : Prop :=
  (out = true ∧ K ⊆ Q) ∨ (out = false ∧ ¬ (s • K ⊆ Q))

/-- Number of coin strings on which the answer is correct; the success probability is this
count divided by 2^m. -/
def successCount {d q m : ℕ} (A : QueryAlg d q m) (s : ℝ) (K Q : Set (E d)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ω : Fin m → Bool => Correct s K Q (run A K Q ω))).card

end ZonotopeContainment.AdaptiveSampling.Supplement


