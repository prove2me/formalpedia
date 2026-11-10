-- Prove2me | Definitions.Def_RandOrderKnapGAP_Integral_RandomOrder
-- name    : RandOrderKnapGAP_Integral_RandomOrder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:06.542965+00:00
-- url     : https://prove2.me/theorems/67420513-7be7-4051-8bb6-98f5c539837e
-- title:
--   Uniformly random arrival order: the prefix $Q_k$ and probabilities over permutations
-- statement:
--   Let $\pi$ be a uniformly random permutation of the $n$ items, $\pi(r)$ the item of (0-based) round $r$. The revealed set after $k$ rounds is $Q_k=\{\pi(0),\dots,\pi(k-1)\}$ (the paper's $\{\pi(1),\dots,\pi(k)\}$). For events $E,F$ of permutations, $\Pr_\pi(E)=|E|/n!$, $\Pr_\pi(E\mid F)=|E\cap F|/|F|$ and $\mathbb E_\pi[f\mid F]=\sum_{\pi\in F}f(\pi)/|F|$.
--
--   **Formalization Note.** `prefixSet π k` is the image of the first $k$ positions. The ratios are $0$ when $F$ is empty (Lean's $x/0=0$); every statement of the mission conditions on events of positive probability.
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 3 (PDF 5), §2

import Mathlib

open scoped BigOperators

namespace RandOrderKnapGAP.Integral

/-!
# The uniformly random arrival order and its prefixes

Agrawal, Khan, Pareek, *Improved Algorithms in the Random-Order Model: Knapsack, GAP, and
Beyond*, STOC 2027 submission, p. 3 (§2).

`π : Equiv.Perm (Fin n)` is uniform; `π r` is the item arriving in (0-based) round `r`, so the
paper's `π(k)` is `π ⟨k - 1, _⟩`. `prefixSet π k = Q_k = {π(1), …, π(k)}` is the unordered set
of the first `k` arrivals. Probabilities and conditional expectations over `π` are finite
ratios of counts (a conditional quantity given an event of probability zero is `0`; every
statement below conditions on events of positive probability).
-/

/-- `Q_k = {π(1), …, π(k)}`: the unordered set of items revealed in the first `k` rounds. -/
def prefixSet {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin n => j.val < k)).image π

open Classical in
/-- `Pr_π(E)` for a uniformly random permutation `π` of `Fin n`. -/
noncomputable def probPerm {n : ℕ} (E : Equiv.Perm (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Nat.factorial n : ℝ)

open Classical in
/-- `Pr_π(E | F)` for a uniformly random permutation `π` of `Fin n`. -/
noncomputable def condProbPerm {n : ℕ} (E F : Equiv.Perm (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter (fun π => E π ∧ F π)).card : ℝ) / ((Finset.univ.filter F).card : ℝ)

open Classical in
/-- `E_π[f | F]` for a uniformly random permutation `π` of `Fin n`. -/
noncomputable def condExpPerm {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ)
    (F : Equiv.Perm (Fin n) → Prop) : ℝ :=
  (∑ π ∈ Finset.univ.filter F, f π) / ((Finset.univ.filter F).card : ℝ)

end RandOrderKnapGAP.Integral


