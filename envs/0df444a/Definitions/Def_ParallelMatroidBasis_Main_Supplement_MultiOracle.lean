-- Prove2me | Definitions.Def_ParallelMatroidBasis_Main_Supplement_MultiOracle
-- name    : ParallelMatroidBasis_Main_Supplement_MultiOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:42.242976+00:00
-- url     : https://prove2.me/theorems/8790062d-28fd-4fa8-8ddd-0f8358986f41
-- title:
--   Parallel algorithms with two oracles: matroid intersection and submodular maximization (§1)
-- statement:
--   The round model is that of the base mission: an algorithm is fixed before the input, one procedure for every ground-set size $n$; in each round it submits a finite batch of queries, and each batch and the final output are functions of its private random tape and of the earlier batches with their answers only.
--
--   1. For an algorithm $P$ with oracle $\mathrm{ans}$, *every run uses at most $R$ rounds* means that for every random tape the run halts after at most $R$ batches; *at most $K$ queries per round* means every batch of every run has at most $K$ queries; *at most $K$ queries of a kind in total* means that, on every run, the number of queries of that kind summed over all rounds is at most $K$.
--   2. **Matroid intersection** (PDF p.5). The queries are independence queries to either of two matroids $M_1=(E,\mathcal I_1)$, $M_2=(E,\mathcal I_2)$ on the same ground set $E=[n]$, answered by $\mathbf 1[T\in\mathcal I_1]$ or $\mathbf 1[T\in\mathcal I_2]$. A set $S$ **solves the matroid intersection problem** if $S\in\mathcal I_1\cap\mathcal I_2$ and $|S|\ge|T|$ for every $T\in\mathcal I_1\cap\mathcal I_2$, i.e. $|S|=r=\max_{T\in\mathcal I_1\cap\mathcal I_2}|T|$.
--   3. **Submodular maximization under a matroid constraint** (PDF p.5). The queries are independence queries $\mathrm{Ind}(T)$ to a matroid $M=([n],\mathcal I)$ and value queries returning the exact real value $f(T)$ of a set function $f$. For $\varepsilon\in\mathbb R$, a set $S$ is a **$(1/2-\varepsilon)$-approximate solution** if $S\in\mathcal I$ and
--   $$f(S)\ \ge\ \Big(\tfrac12-\varepsilon\Big)\max_{T\in\mathcal I} f(T).$$
--   4. The success probabilities are the probabilities, over the random tape, that the run halts with a solution in the sense of 2 or 3.
--
--   These are the problems of Theorems 1.4 and 1.5.
--
--   **Formalization Note** Both models instantiate the published `ExactParallelSampling.QuasiUniform.Protocol`: intersection queries are pairs $(i,T)\in\mathrm{Fin}\,2\times 2^{[n]}$ with Boolean answers; submodular queries are `Finset (Fin n) ⊕ Finset (Fin n)` with answers in `Bool ⊕ ℝ`. The maximum over $\mathcal I$ is written as "$f(S)\ge(1/2-\varepsilon)f(T)$ for every independent $T$", which is the same condition since $\mathcal I$ is finite and contains $\emptyset$. Total query counts sum the batch sizes over every step of a run; batches after halting are empty.
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, matroid intersection and submodular maximization: §1 Applications, p.3 (PDF p.5); round model: §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ParallelMatroidBasis_Main_QueryModel

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main.Supplement

/-! # Parallel algorithms with several oracles: matroid intersection and submodular maximization
(Putterman–Khanna–Song, STOC 2027 submission #589, §1 "Applications", PDF p.5 (printed p.3))

The round model is the published `ExactParallelSampling.QuasiUniform.Protocol`, as in the base
mission's `QueryModel`: each batch of queries and the output are functions of the private random
tape and of the earlier batches with their answers only. -/

open ExactParallelSampling.QuasiUniform

/-! ## Round and query counts of a run, for an arbitrary oracle -/

/-- Every run of `P` against the oracle `ans` (every random tape) halts after at most `R` rounds. -/
def RunRoundsAtMost {Q A O : Type} (P : Protocol Q A O) (ans : Q → A) (R : ℝ) : Prop :=
  ∀ ω : Tape, ∃ r : ℕ, P.rounds ans ω = (r : ℕ∞) ∧ (r : ℝ) ≤ R

/-- Every round of every run of `P` against `ans` asks at most `K` queries. -/
def RunQueriesPerRoundAtMost {Q A O : Type} (P : Protocol Q A O) (ans : Q → A) (K : ℕ) : Prop :=
  ∀ (ω : Tape) (r : ℕ), (P.batchAt ans ω r).card ≤ K

/-- Every run of `P` against `ans` asks, over all its rounds together, at most `K` queries of the
kind selected by `sel`. (Batches after halting are empty, so summing over any number `R` of steps
counts all queries of the run.) -/
def RunTotalQueriesAtMost {Q A O : Type} (P : Protocol Q A O) (ans : Q → A) (sel : Q → Prop)
    (K : ℕ) : Prop :=
  ∀ (ω : Tape) (R : ℕ),
    ∑ r ∈ Finset.range R, ((P.batchAt ans ω r).filter sel).card ≤ K

/-! ## Matroid intersection (PDF p.5) -/

/-- A query of a matroid-intersection algorithm: an independence query `(0, T)` to `M₁` or
`(1, T)` to `M₂`. -/
abbrev IntersectionQuery (n : ℕ) := Fin 2 × Finset (Fin n)

/-- The two independence oracles of `M₁` and `M₂` on the same ground set. -/
def pairOracle {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : IntersectionQuery n → Bool :=
  fun q => if q.1 = 0 then indOracle M₁ q.2 else indOracle M₂ q.2

/-- A parallel matroid-intersection algorithm: one protocol for every ground-set size `n`, asking
independence queries to the two matroids and outputting a subset of `Fin n`. -/
abbrev IntersectionAlgorithm :=
  (n : ℕ) → Protocol (IntersectionQuery n) Bool (Finset (Fin n))

/-- `S` solves the matroid intersection problem for `M₁, M₂`: it is independent in both and at
least as large as every common independent set. -/
def IsMaxCommonIndep {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (S : Finset (Fin n)) : Prop :=
  M₁.Indep (↑S : Set (Fin n)) ∧ M₂.Indep (↑S : Set (Fin n)) ∧
    ∀ T : Finset (Fin n), M₁.Indep (↑T : Set (Fin n)) → M₂.Indep (↑T : Set (Fin n)) →
      T.card ≤ S.card

/-- The probability, over the random tape, that `A` halts on `(M₁, M₂)` with a maximum common
independent set. -/
def intersectionSuccessProb (A : IntersectionAlgorithm) (n : ℕ) (M₁ M₂ : Matroid (Fin n)) :
    ENNReal :=
  tapeLaw {ω | ∃ S : Finset (Fin n), (A n).output (pairOracle M₁ M₂) ω = some S ∧
    IsMaxCommonIndep M₁ M₂ S}

/-! ## Submodular maximization under a matroid constraint (PDF p.5) -/

/-- A query of a submodular-maximization algorithm: an independence query `inl T` to `M` or a
value query `inr T` to `f`. -/
abbrev SubmodQuery (n : ℕ) := Finset (Fin n) ⊕ Finset (Fin n)

/-- The combined oracle: `inl T ↦ inl (Ind(T))`, `inr T ↦ inr (f(T))` (exact real values). -/
def submodOracle {n : ℕ} (M : Matroid (Fin n)) (f : Finset (Fin n) → ℝ) :
    SubmodQuery n → Bool ⊕ ℝ
  | .inl T => .inl (indOracle M T)
  | .inr T => .inr (f T)

/-- Independence queries. -/
def IsIndepQuery {n : ℕ} : SubmodQuery n → Prop
  | .inl _ => True
  | .inr _ => False

/-- Value queries. -/
def IsValueQuery {n : ℕ} : SubmodQuery n → Prop
  | .inl _ => False
  | .inr _ => True

/-- A parallel algorithm for submodular maximization under a matroid constraint: one protocol for
every ground-set size `n`, outputting a subset of `Fin n`. -/
abbrev SubmodAlgorithm := (n : ℕ) → Protocol (SubmodQuery n) (Bool ⊕ ℝ) (Finset (Fin n))

/-- `S` is a `(1/2 − ε)`-approximate solution: `S ∈ I` and `f(S) ≥ (1/2 − ε) f(T)` for every
`T ∈ I`, i.e. `f(S) ≥ (1/2 − ε) max_{T ∈ I} f(T)`. -/
def IsHalfApprox {n : ℕ} (M : Matroid (Fin n)) (f : Finset (Fin n) → ℝ) (ε : ℝ)
    (S : Finset (Fin n)) : Prop :=
  M.Indep (↑S : Set (Fin n)) ∧
    ∀ T : Finset (Fin n), M.Indep (↑T : Set (Fin n)) → (1 / 2 - ε) * f T ≤ f S

/-- The probability, over the random tape, that `A` halts on `(M, f)` with a
`(1/2 − ε)`-approximate solution. -/
def submodSuccessProb (A : SubmodAlgorithm) (n : ℕ) (M : Matroid (Fin n))
    (f : Finset (Fin n) → ℝ) (ε : ℝ) : ENNReal :=
  tapeLaw {ω | ∃ S : Finset (Fin n), (A n).output (submodOracle M f) ω = some S ∧
    IsHalfApprox M f ε S}

end ParallelMatroidBasis.Main.Supplement


