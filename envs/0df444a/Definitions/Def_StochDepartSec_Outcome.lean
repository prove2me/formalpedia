-- Prove2me | Definitions.Def_StochDepartSec_Outcome
-- name    : StochDepartSec_Outcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:02.290661+00:00
-- url     : https://prove2.me/theorems/436259f4-5cba-4f0f-8475-0f68623ebd11
-- title:
--   Sample space of the stochastic departure secretary problem
-- statement:
--   There are $n$ candidates, labelled $i\in\{0,\dots,n-1\}$. An **outcome** is a quadruple $\omega=(a,\ell,\sigma,u)$ where
--
--   1. $a_i\in\mathbb R$ is the arrival time of candidate $i$;
--   2. $\ell_i\in\mathbb R$ is its waiting time (how long it stays in the system);
--   3. $\sigma$ is a permutation of the labels giving the overall order of the candidates: $\sigma(i)=0$ means that $i$ is the best candidate overall, smaller is better;
--   4. $u\in\mathbb R$ is an external randomization seed that a policy may use.
--
--   The accessors $\mathrm{arrival}(\omega,i)=a_i$, $\mathrm{waiting}(\omega,i)=\ell_i$, $\mathrm{rank}(\omega)=\sigma$ and $\mathrm{seed}(\omega)=u$ are defined with it, and the finite set of permutations carries the discrete $\sigma$-algebra.
--
--   This is the probability space on which every event of the paper (arrivals, departures, the history of a policy, success) is defined.
--
--   **Formalization Note** Candidates carry fixed labels; the paper's indexing by arrival order $A_1\le\dots\le A_n$ is a relabelling recovered from $a$. Ranks are 0-based: $\sigma(i)=0$ is the paper's $\pi(i)=1$.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5

import Mathlib
open MeasureTheory

namespace StochDepartSec

/-- The sample space of the stochastic departure secretary problem with `n` candidates: an
outcome `ω = (a, ℓ, σ, u)` records, for every candidate `i : Fin n`, its arrival time `a i`, its
waiting time `ℓ i`, the overall order `σ` of the candidates (`σ i = 0` is the best overall), and
an external randomization seed `u` available to policies.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5 (Model): "For each i ∈ S, an arrival time A_i is drawn independently from the arrival
distribution A and a waiting time L_i … is a non-negative real number drawn i.i.d. from some
distribution L"; "the total order can be expressed as a permutation π : [n] → [n]".

**Formalization Note** Candidates carry fixed labels `Fin n`; the paper's indexing by arrival
order (`A_1 ≤ … ≤ A_n`) is a relabelling and is recovered from `a`. Ranks are 0-based:
`σ i = 0` is the paper's `π(i) = 1`. The seed `u` lets policies randomize (the paper's own
simulation policies in Lemmas 9, 10 draw auxiliary random variables). -/
abbrev Outcome (n : ℕ) : Type := (Fin n → ℝ) × (Fin n → ℝ) × Equiv.Perm (Fin n) × ℝ

/-- The discrete σ-algebra on the overall orders `Equiv.Perm (Fin n)` (a finite set). -/
instance permMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance permDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) :=
  ⟨fun _ => trivial⟩

/-- Arrival time `a i` of candidate `i` in outcome `ω`. -/
def arrival {n : ℕ} (ω : Outcome n) (i : Fin n) : ℝ := ω.1 i

/-- Waiting time `ℓ i` of candidate `i` in outcome `ω`. -/
def waiting {n : ℕ} (ω : Outcome n) (i : Fin n) : ℝ := ω.2.1 i

/-- The overall order `σ` in outcome `ω`; `rank ω i` is the 0-based overall rank of `i`. -/
def rank {n : ℕ} (ω : Outcome n) : Equiv.Perm (Fin n) := ω.2.2.1

/-- The external randomization seed `u` in outcome `ω`. -/
def seed {n : ℕ} (ω : Outcome n) : ℝ := ω.2.2.2

end StochDepartSec


