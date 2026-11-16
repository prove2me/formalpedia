-- Prove2me | Definitions.Def_QuadPTFLearn_Supplement_SQ
-- name    : QuadPTFLearn_Supplement_SQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:40:58.754211+00:00
-- url     : https://prove2.me/theorems/5a9aaf43-4a11-422d-b685-689067cef2ea
-- title:
--   The statistical query model (Definition 10.1): legal queries, valid oracles, randomized adaptive SQ algorithms and the laws $D_q$ with $\{\pm1\}$ labels
-- statement:
--   This definition file formalizes the statistical query (SQ) model of Definition 10.1 and the target laws of the SQ lower bound (Theorem 10.2). Labels follow §10's $\{\pm1\}$ convention.
--
--   1. **Queries.** A query is a pair $(\phi,\tau)$ of a function $\phi:\mathbb R^d\times\mathbb R\to\mathbb R$ and a tolerance $\tau$. It is *legal* when $\phi$ is measurable, $|\phi|\le1$ everywhere, and $\tau>0$.
--   2. **Oracles.** An answer $a$ to $(\phi,\tau)$ is valid for a law $D$ on $\mathbb R^d\times\mathbb R$ when
--   $$\bigl|a-\mathbb E_{(x,y)\sim D}[\phi(x,y)]\bigr|\le\tau .$$
--   An oracle is a function assigning an answer to every query. It is *valid* for $D$ (an instance of $\mathrm{STAT}_D$) when its answer to every legal query is valid.
--   3. **SQ algorithms.** An SQ algorithm on $\mathbb R^d$ has internal randomness, a probability space $(\Omega,\mu)$ of arbitrary type, and a strategy. Given the coin outcome $\omega$ and the list of answers received so far, the strategy either asks the next query or stops and outputs a hypothesis $h:\mathbb R^d\to\mathbb R$. Queries and their tolerances may therefore be chosen adaptively from earlier answers.
--   4. **Runs.** Run against an oracle $O$ with coins $\omega$, the algorithm accumulates the answers of $O$ to its queries. The run *stops with $h$ after $n$ queries* when it asks exactly $n$ queries and then outputs $h$.
--   5. **Hard laws.** For quadratics $q_1,\dots,q_k$, $D_q$ is the law of $(x,\,2f(x)-1)$ with $x\sim N(0,I_d)$ and $f(x)=1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}$. This is the realizable distribution of Definition 1.2 written with $\{\pm1\}$ labels.
--
--   The SQ model measures complexity by the number of queries and the inverse tolerance. Lower bounds in it apply to spectral, moment and tensor methods.
--
--   **Formalization Note** The page's $\phi:\mathbb R^d\times\{\pm1\}\to[-1,1]$ is extended to all real labels; only its values at $\pm1$ matter for the laws used. Measurability of $\phi$ is the standing convention under which $\mathbb E_D[\phi]$ is defined. The oracle is memoryless (its answer depends on the query only). The coin space is not restricted to discrete distributions.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Definition 10.1 (Statistical Query Model), p.93 (PDF p.95); §10 ±1-label convention, p.93; Definition 1.2, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory

namespace QuadPTFLearn

namespace Supplement

/-!
# The statistical query model (Definition 10.1) and the hard laws of Theorem 10.2

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Definition 10.1 (Statistical Query Model), p.93 (PDF p.95); Theorem 10.2, p.93; §10 uses the
`{±1}`-label convention ("Throughout this section, we use the equivalent {±1}-label convention").

**Formalization Note.**
* A query is a pair `(φ, τ)` with `φ : ℝᵈ × ℝ → ℝ` and a tolerance `τ`. It is *legal* when `φ` is
  measurable, `|φ| ≤ 1` everywhere and `τ > 0`. The page's `φ : ℝᵈ × {±1} → [−1, 1]` is the
  restriction to labels `±1`; every such function extends to a legal `φ` (and only its values at
  `±1` matter for the laws below). Measurability is the standing convention that makes
  `E_D[φ]` a defined expectation.
* An answer `a` to `(φ, τ)` is valid for a law `D` on `ℝᵈ × ℝ` when `|a − E_D[φ]| ≤ τ`. An oracle
  is a function from queries to reals (it is memoryless: the answer depends on the query only);
  it is valid for `D` when its answer to every legal query is valid.
* An SQ algorithm on `ℝᵈ` has internal randomness: a probability space `(Ω, μ)` of arbitrary
  type and measure (no restriction to discrete coins), and a strategy `next ω as` that, given the
  coin outcome `ω` and the list `as` of answers received so far, either asks the next query
  (`Sum.inl`) or stops with a hypothesis `h : ℝᵈ → ℝ` (`Sum.inr`). Queries and tolerances are
  chosen adaptively from the previous answers, as on the page.
* `answers A O ω n` is the list of answers after `n` rounds against the oracle `O`; once the
  strategy stops, the list no longer grows. `StopsWith A O ω n h` says the run makes exactly `n`
  queries and then outputs `h`.
* `lawPM q` is the law of `(x, 2 f(x) − 1)`, `x ∼ N(0, I_d)`, `f = ptfInd q`: the target of
  Definition 1.2 written with `{±1}` labels.
-/

/-- A statistical query: a query function `φ` and a tolerance `tol`. -/
structure SQQuery (d : ℕ) where
  φ : Pt d × ℝ → ℝ
  tol : ℝ

/-- A legal query: `φ` measurable with values in `[−1, 1]`, tolerance positive. -/
def SQQuery.Legal {d : ℕ} (Q : SQQuery d) : Prop :=
  Measurable Q.φ ∧ (∀ z, |Q.φ z| ≤ 1) ∧ 0 < Q.tol

/-- An oracle `STAT_D`: a (memoryless) answer to every query. -/
abbrev SQOracle (d : ℕ) := SQQuery d → ℝ

/-- The oracle `O` is valid for the law `D`: every legal query `(φ, τ)` is answered within `τ` of
`E_{(x,y)∼D}[φ(x, y)]`. -/
def ValidOracle {d : ℕ} (D : Measure (Pt d × ℝ)) (O : SQOracle d) : Prop :=
  ∀ Q : SQQuery d, Q.Legal → |O Q - ∫ z, Q.φ z ∂D| ≤ Q.tol

/-- A randomized adaptive SQ algorithm on `ℝᵈ`: a probability space of internal coins and a
strategy that, from the coins and the answers so far, asks the next query or stops with a
hypothesis. -/
structure SQAlg (d : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  next : Ω → List ℝ → SQQuery d ⊕ (Pt d → ℝ)

attribute [instance] SQAlg.mΩ SQAlg.isProb

/-- The answers received after `n` rounds of the run of `A` with coins `ω` against `O`. -/
noncomputable def answers {d : ℕ} (A : SQAlg d) (O : SQOracle d) (ω : A.Ω) : ℕ → List ℝ
  | 0 => []
  | n + 1 =>
    match A.next ω (answers A O ω n) with
    | Sum.inl Q => answers A O ω n ++ [O Q]
    | Sum.inr _ => answers A O ω n

/-- The run of `A` with coins `ω` against `O` asks exactly `n` queries and then stops with the
hypothesis `h`. -/
def StopsWith {d : ℕ} (A : SQAlg d) (O : SQOracle d) (ω : A.Ω) (n : ℕ) (h : Pt d → ℝ) : Prop :=
  (∀ j < n, ∃ Q, A.next ω (answers A O ω j) = Sum.inl Q) ∧
    A.next ω (answers A O ω n) = Sum.inr h

/-- The law `D_q` of `(x, 2·1{q₁(x) ≥ 0, …, q_k(x) ≥ 0} − 1)` with `x ∼ N(0, I_d)`
(`{±1}` labels). -/
noncomputable def lawPM {d k : ℕ} (q : Fin k → Poly d) : Measure (Pt d × ℝ) :=
  (gauss d).map (fun x => (x, 2 * ptfInd q x - 1))

instance {d k : ℕ} (q : Fin k → Poly d) : IsProbabilityMeasure (lawPM q) := by
  unfold lawPM
  refine Measure.isProbabilityMeasure_map ?_
  exact (measurable_id.prodMk
    (((measurable_ptfInd q).const_mul 2).sub_const 1)).aemeasurable

end Supplement

end QuadPTFLearn


