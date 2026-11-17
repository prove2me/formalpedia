-- Prove2me | Definitions.Def_DoublingMST_Supplement_ComparisonAlg
-- name    : DoublingMST_Supplement_ComparisonAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:11.10517+00:00
-- url     : https://prove2.me/theorems/9b4d7809-f339-42ba-941a-079bf7a6bc5b
-- title:
--   $b$-ary comparison algorithms: adaptive tests, transcripts and comparison counts
-- statement:
--   A deterministic **$b$-ary comparison algorithm** on $n$ labelled points is an adaptive strategy $A$: given the outcomes $o_1,\dots,o_k\in\{0,\dots,b-1\}$ of the comparisons made so far, it either performs another comparison, i.e. applies some test $t$ that maps the input metric $d$ to one of $b$ outcomes, or stops and outputs a fixed explicit edge set. Running $A$ on $d$ produces a transcript of outcomes; the **comparison count** $c(A,d)\in\mathbb N\cup\{\infty\}$ is the number of comparisons made before the output ($\infty$ if $A$ never outputs).
--
--   A randomized comparison algorithm is a family $(A_\omega)_{\omega\in\Omega}$ indexed by a probability space $(\Omega,\mu)$; a deterministic one is the case of a one-point $\Omega$.
--
--   This is the decision-tree model of the $\Omega(n\log n)$ lower bound: each internal node has at most $b$ children and each leaf carries one fixed labelled output, which is what the output-counting argument of Lemma 6.4 needs. Definition 6.1's atomic comparisons $d(x,y)\gtreqless d(u,v)$ are the case $b=3$.
--
--   **Formalization Note** Tests are arbitrary functions of the metric with $b$ outcomes; computation between tests is free.
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 6.1, p.30 (PDF p.32); §6.2, p.31 (PDF p.33); Lemma 6.4, p.32 (PDF p.34)

import Mathlib
open scoped Classical

namespace DoublingMST.Supplement

/-!
# b-ary comparison algorithms (§6.1–6.2)

Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759),
Definition 6.1, p.30 (PDF p.32) and §6.2, p.31 (PDF p.33): the lower bound "applies to randomized
algorithms … allowing arbitrary computations between comparisons as long as each comparison has a
constant number of possible outcomes and the comparison transcript determines the labeled output".
Lemma 6.4, p.32: "a correct b-ary comparison tree".

A deterministic b-ary comparison algorithm on `n` labelled points is an adaptive strategy: given
the outcomes so far (a list in `Fin b`), it either performs a test, an arbitrary function from the
input metric to `Fin b`, or stops with a fixed explicit edge set.

**Formalization Note.**
* Tests are arbitrary `b`-outcome functions of the metric `d : Fin n → Fin n → ℝ`, which contains
  Definition 6.1's atomic three-way distance comparisons (`b ≥ 3`) and every finite-outcome
  comparison of computed reals. Computation between tests is free.
* `cmpCount A d ∈ ℕ∞` is the number of tests performed before the output (`⊤` if the strategy
  never outputs). The output is the edge set returned at that point (`CmpOutputs`).
* A randomized algorithm is a family `A : Ω → CmpStrategy n b` over a probability space `(Ω, μ)`;
  the deterministic case is a one-point `Ω`.
-/

/-- A `b`-outcome test of the input metric. -/
abbrev CmpTest (n b : ℕ) := (Fin n → Fin n → ℝ) → Fin b

/-- A deterministic `b`-ary comparison strategy: from the transcript of outcomes, the next test
or the output edge set. -/
abbrev CmpStrategy (n b : ℕ) := List (Fin b) → CmpTest n b ⊕ Finset (Sym2 (Fin n))

/-- The transcript after `k` rounds of `A` on the metric `d`: a test appends its outcome; after the
output the transcript stays fixed. -/
def cmpTranscript {n b : ℕ} (A : CmpStrategy n b) (d : Fin n → Fin n → ℝ) : ℕ → List (Fin b)
  | 0 => []
  | k + 1 =>
    match A (cmpTranscript A d k) with
    | .inl t => cmpTranscript A d k ++ [t d]
    | .inr _ => cmpTranscript A d k

/-- The number of tests `A` performs on `d` before it outputs; `⊤` if it never outputs. -/
noncomputable def cmpCount {n b : ℕ} (A : CmpStrategy n b) (d : Fin n → Fin n → ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : (A (cmpTranscript A d k)).isRight = true), (k : ℕ∞)

/-- `A` run on `d` outputs the edge set `T`. -/
def CmpOutputs {n b : ℕ} (A : CmpStrategy n b) (d : Fin n → Fin n → ℝ)
    (T : Finset (Sym2 (Fin n))) : Prop :=
  ∃ k : ℕ, A (cmpTranscript A d k) = .inr T

end DoublingMST.Supplement


