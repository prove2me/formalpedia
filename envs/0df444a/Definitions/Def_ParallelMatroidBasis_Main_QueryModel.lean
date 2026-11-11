-- Prove2me | Definitions.Def_ParallelMatroidBasis_Main_QueryModel
-- name    : ParallelMatroidBasis_Main_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:53.068761+00:00
-- url     : https://prove2.me/theorems/f59e64e8-776a-481a-9bb8-673fe855987b
-- title:
--   §1 — parallel algorithms with an independence oracle: rounds, queries per round, success probability
-- statement:
--   A matroid $M$ on $n$ elements is given only through its **independence oracle** $\mathrm{Ind}:2^{E}\to\{0,1\}$, $\mathrm{Ind}(S)=\mathbf 1[S\in\mathcal I]$ (PDF p.3). A **parallel algorithm** is fixed before the matroid, one procedure for every ground-set size $n$ (it knows $n$ and the labels $[n]$). It runs in **rounds**: in each round it submits a finite batch of subsets of $[n]$ and receives the answers $\mathrm{Ind}(T)$ to exactly those queries; the batch of a round, and the final output (a subset of $[n]$), are functions of the algorithm's private randomness and of the earlier batches and their answers only. Computation between rounds is free.
--
--   For such an algorithm $A$, a matroid $M$ on $[n]$ with ground set $[n]$ and a budget $R$:
--   1. $A$ uses at most $R$ rounds on $M$ if every run, for every value of the randomness, halts after at most $R$ rounds;
--   2. $A$ asks at most $Q$ queries per round on $M$ if every batch of every run has at most $Q$ sets;
--   3. the success probability is the probability that $A$ halts on $M$ with an output that is a basis of $M$.
--
--   The round budget of the main theorem is $C\,(1+n^{1/3}(\log_2 n)^{1/3})$.
--
--   **Formalization Note.** The round model is the published definition `ExactParallelSampling.QuasiUniform.Protocol` with queries `Finset (Fin n)`, answers `Bool` and outputs `Finset (Fin n)`: `next` maps the transcript (the earlier batches with the answers to exactly those queries) and a random tape $\omega\in[0,1]^{\mathbb N}$ (uniform product law `tapeLaw`) to "halt with output" or "ask a batch"; for each transcript it is a measurable function of the tape. `rounds` counts the batches asked before halting; halting itself costs no round. The answers come from `indOracle M`, so the algorithm cannot read $M$ in any other way.
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, §1, p.1 (PDF p.3): the parallel independence-query model of [KUW85, KUW88]; Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-! # Parallel algorithms with an independence oracle
(Putterman–Khanna–Song, STOC 2027 submission #589, §1, PDF p.3)

The adaptive randomized round model is the published `ExactParallelSampling.QuasiUniform.Protocol`:
the next batch of queries (or the output) is a function of the private random tape and of the
earlier batches with the answers to exactly those queries; nothing else about the input is
visible. Here queries are subsets of the ground set `Fin n`, answers are booleans and the output
is a subset of `Fin n`. -/

open ExactParallelSampling.QuasiUniform

/-- The independence oracle `Ind : 2^E → {0,1}`, `Ind(T) = 1[T ∈ I]` (PDF p.3). -/
def indOracle {n : ℕ} (M : Matroid (Fin n)) : Finset (Fin n) → Bool :=
  fun T => decide (M.Indep (↑T : Set (Fin n)))

/-- A parallel basis-finding algorithm: one protocol for every ground-set size `n`, fixed before
the matroid. -/
abbrev BasisAlgorithm := (n : ℕ) → Protocol (Finset (Fin n)) Bool (Finset (Fin n))

/-- Every run of `A` on `M` (every random tape) halts after at most `R` rounds. -/
def RoundsAtMost (A : BasisAlgorithm) (n : ℕ) (M : Matroid (Fin n)) (R : ℝ) : Prop :=
  ∀ ω : Tape, ∃ r : ℕ, (A n).rounds (indOracle M) ω = (r : ℕ∞) ∧ (r : ℝ) ≤ R

/-- Every round of every run of `A` on `M` asks at most `Q` independence queries. -/
def QueriesPerRoundAtMost (A : BasisAlgorithm) (n : ℕ) (M : Matroid (Fin n)) (Q : ℕ) : Prop :=
  ∀ (ω : Tape) (r : ℕ), ((A n).batchAt (indOracle M) ω r).card ≤ Q

/-- The probability, over the random tape, that `A` halts on `M` and outputs a basis of `M`. -/
def successProb (A : BasisAlgorithm) (n : ℕ) (M : Matroid (Fin n)) : ENNReal :=
  tapeLaw {ω | ∃ B : Finset (Fin n), (A n).output (indOracle M) ω = some B ∧
    M.IsBase (↑B : Set (Fin n))}

/-- The round budget `C · (1 + n^{1/3} (log₂ n)^{1/3})`. -/
def roundBound (C : ℝ) (n : ℕ) : ℝ :=
  C * (1 + (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.logb 2 n) ^ ((1 : ℝ) / 3))

end ParallelMatroidBasis.Main


