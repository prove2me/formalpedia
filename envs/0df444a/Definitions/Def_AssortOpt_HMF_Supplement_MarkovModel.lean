-- Prove2me | Definitions.Def_AssortOpt_HMF_Supplement_MarkovModel
-- name    : AssortOpt_HMF_Supplement_MarkovModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:14:28.437852+00:00
-- url     : https://prove2.me/theorems/e56d6ed5-4adb-448e-b926-307221f51a59
-- title:
--   Definition 9 — Markov-chain stopped-walk law and its first-visit list distribution
-- statement:
--   A Markov-chain choice model has states $N\cup\{0\}$, stochastic nonnegative transition probabilities, an initial probability vector, and terminal state $0$. Let $t=(i_1,\ldots,i_m)$ record every visit before the first arrival at $0$, including repeated visits. Its mass is
--   $$\Pr[t]=\lambda_{i_1}\sigma_{i_1i_2}\cdots\sigma_{i_{m-1}i_m}\sigma_{i_m0},\qquad \Pr[()]=\lambda_0.$$
--   The stopped-walk masses form a probability mass function, expressing almost sure absorption under the initial law. The buyer's list retains the first visit to each item in order. Pushing forward the walk law yields a normalized finite distribution of strictly ordered subsets, then its strictly positive support is represented by the published `ListDist` type.
--
--   The stochastic matrix itself is the published general finite-chain object. State `none` denotes $0$. A self-loop pads the terminal state after stopping and never enters a stopped-walk probability. Initial mass at $0$ is allowed; inaccessible states need not be transient. Finite walks have no common length bound. The reverse–deduplicate–reverse operation retains first occurrences, rather than last occurrences.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 14, Definition 9; p. 45, proof of Proposition 4

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_Reports
import Definitions.Def_LeastSquaresTD_Absorbing_Chain

namespace AssortOpt.HMF.Supplement
open Finset

/-- A walk records every item visit before the first visit to the terminal state `none`.
This recursive product is its continuation probability, starting at state `i`. -/
def walkTail {n : ℕ} (C : LeastSquaresTD.Absorbing.Chain (Option (Fin n))) :
    Fin n → List (Fin n) → ℝ
  | i, [] => C.P (some i) none
  | i, j :: t => C.P (some i) (some j) * walkTail C j t

/-- Probability of exactly this finite pre-absorption walk, including its final transition to 0.
The empty walk means the initial state was 0. -/
def walkWeight {n : ℕ} (C : LeastSquaresTD.Absorbing.Chain (Option (Fin n)))
    (initial : Option (Fin n) → ℝ) : List (Fin n) → ℝ
  | [] => initial none
  | i :: t => initial (some i) * walkTail C i t

/-- Definition 9, p. 14. The normalized law of finite stopped walks expresses almost sure
absorption under the specified initial law. It imposes no bound on the walk length and no
absorption requirement from inaccessible states. The terminal self-loop simply pads a stopped
chain; it is never read by `walkWeight`. -/
structure MarkovModel (n : ℕ) where
  chain : LeastSquaresTD.Absorbing.Chain (Option (Fin n))
  terminal : ∀ s, chain.P none s = if s = none then 1 else 0
  initial : Option (Fin n) → ℝ
  initial_nonneg : ∀ s, 0 ≤ initial s
  initial_sum : ∑ s, initial s = 1
  walks : PMF (List (Fin n))
  walks_eq : ∀ t, walks t = ENNReal.ofReal (walkWeight chain initial t)

/-- Retain first visits, preserving their order. Reversing before and after `dedup` is necessary:
Mathlib's `dedup` itself keeps LAST occurrences. -/
def firstVisits {n : ℕ} (t : List (Fin n)) : Report n :=
  ⟨t.reverse.dedup.reverse, List.nodup_reverse.mpr (List.nodup_dedup _)⟩

/-- Pushforward of the full stopped-walk law to the first-visit list. -/
noncomputable def listLaw {n : ℕ} (C : MarkovModel n) : PMF (Report n) :=
  C.walks.map firstVisits

/-- Extend a law on ordered subsets by zero on lists with repeated items. -/
noncomputable def reportProb {n : ℕ} (P : PMF (Report n)) (ℓ : List (Fin n)) : ℝ :=
  if h : ℓ.Nodup then (P ⟨ℓ, h⟩).toReal else 0

/-- Canonical positive support representation of a finite first-visit list law in the published
`ListDist` interface. Only structural normalization proofs occur here. -/
noncomputable def lawToListDist {n : ℕ} (P : PMF (Report n)) : ListDist n := by
  classical
  let A := allReports n
  let p := reportProb P
  refine ⟨A.filter (fun ℓ => 0 < p ℓ), p, ?_, ?_, ?_⟩
  · intro ℓ h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    exact a.property
  · intro ℓ h
    exact (Finset.mem_filter.mp h).2
  · have hp : ∀ ℓ, 0 ≤ p ℓ := by
      intro ℓ
      dsimp [p, reportProb]
      split <;> positivity
    have heq : ∑ ℓ ∈ A.filter (fun ℓ => 0 < p ℓ), p ℓ = ∑ ℓ ∈ A, p ℓ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro ℓ hA h
      have hn : ¬ 0 < p ℓ := by
        intro hpos
        exact h (Finset.mem_filter.mpr ⟨hA, hpos⟩)
      exact le_antisymm (le_of_not_gt hn) (hp ℓ)
    rw [heq]
    dsimp [A, allReports]
    rw [Finset.sum_image]
    · have hprob : ∀ a : Report n, p a.val = (P a).toReal := by
        intro a
        simp [p, reportProb, a.property]
      simp_rw [hprob]
      rw [← ENNReal.toReal_sum (fun a _ => P.apply_ne_top a)]
      have hsum : ∑ a : Report n, P a = 1 := by simpa using P.tsum_coe
      rw [hsum]
      rfl
    · intro a _ b _ h
      exact Subtype.ext h

/-- The list distribution actually constructed from Definition 9, rather than an arbitrary
list distribution constrained by the conclusion of Proposition 4. -/
noncomputable def inducedDist {n : ℕ} (C : MarkovModel n) : ListDist n :=
  lawToListDist (listLaw C)

end AssortOpt.HMF.Supplement


