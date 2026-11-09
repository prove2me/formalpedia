-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Domain
-- name    : RankingQueryCost_Joint_Domain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:25.379523+00:00
-- url     : https://prove2.me/theorems/df70a61b-5a79-4915-9081-63b7422c692c
-- title:
--   Comparison identities, continuous estimates, and squared rank loss
-- statement:
--   There are $n$ labelled objects, with $n\ge16$ divisible by four, and $N=\binom n2$ unordered distinct comparison identities. The supplied budget is $0\le s\le\lfloor N/32\rfloor$. A true rank $r$ permutes $0,\ldots,n-1$; larger ranks win. Estimates may have equal or nonintegral coordinates:
--
--   $$Q=\{q\in[0,n-1]^n:\sum_iq_i=N\},\quad D_2(q,z)=\sum_i(q_i-z_i)^2,\quad L_r(q)=D_2(q,r)/n^3.$$
--
--   The uninformed output is $q^0_i=(n-1)/2$, with baseline $\beta_n=(n^2-1)/(12n^2)$, and the precision ceiling is $\varepsilon_0=1/1024$. These objects are shared by all tasks and bounds.
--
--   **Formalization Note** Labels use `Fin n`; a pair is its increasing representative. A true reply means the larger public label wins. Definitions are total, but theorems use the standing admissible domain.
--
--   Comparison stars are traversed in the explicit public lexicographic pair order `pairList n`; no classically chosen list order is required by a finite implementation.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.1, equation (1), p. 3, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Mathlib

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

/-- §2.1: one unordered distinct pair, represented by its increasing public labels. -/
abbrev Pair (n : ℕ) := { ij : Fin n × Fin n // ij.1 < ij.2 }

/-- Public lexicographic traversal of comparison identities. Unlike `Finset.toList`,
this fixes an effective order uniformly in n for the finite-program contracts. -/
def pairList (n : ℕ) : List (Pair n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
    if hij : i < j then some ⟨(i, j), hij⟩ else none

/-- The exact number of physical comparison identities. -/
def pairCount (n : ℕ) : ℕ := n.choose 2

/-- The paper's standing domain, including the supplied total fault budget. -/
def Admissible (n s : ℕ) : Prop :=
  16 ≤ n ∧ 4 ∣ n ∧ s ≤ pairCount n / 32

/-- Rank assigned to each label, with larger ranks winning. -/
abbrev Rank (n : ℕ) := Equiv.Perm (Fin n)

/-- The continuous output space of equation (1). -/
def estimateSet (n : ℕ) : Set (Fin n → ℝ) :=
  {q | (∀ i, 0 ≤ q i ∧ q i ≤ (n : ℝ) - 1) ∧ ∑ i, q i = (pairCount n : ℝ)}

/-- Squared Euclidean displacement; there is no permutation restriction on either argument. -/
def squaredError {n : ℕ} (q z : Fin n → ℝ) : ℝ := ∑ i, (q i - z i) ^ 2

def rankVector {n : ℕ} (r : Rank n) : Fin n → ℝ := fun i => (r i : ℕ)

def loss {n : ℕ} (q : Fin n → ℝ) (r : Rank n) : ℝ :=
  squaredError q (rankVector r) / (n : ℝ) ^ 3

def fallback (n : ℕ) : Fin n → ℝ := fun _ => ((n : ℝ) - 1) / 2

def baseline (n : ℕ) : ℝ := ((n : ℝ) ^ 2 - 1) / (12 * (n : ℝ) ^ 2)

def precisionCeiling : ℝ := 1 / 1024

/-- A reply is true precisely when the larger public label wins. -/
def truthful {n : ℕ} (r : Rank n) (e : Pair n) : Bool :=
  decide (r e.1.1 < r e.1.2)

end RankingQueryCost.Joint


