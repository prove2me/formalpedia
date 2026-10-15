-- Prove2me | Definitions.Def_SeqLoss_LiabilityGame_Nucleolus
-- name    : SeqLoss_LiabilityGame_Nucleolus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:50.627871+00:00
-- url     : https://prove2.me/theorems/6076c463-50b6-44b4-bca0-a7af9e5687c5
-- title:
--   Imputations, excesses, the sorted excess vector and the nucleolus (Schmeidler 1969)
-- statement:
--   Let $v$ be a transferable-utility game on the player set $N=\{1,\dots,n\}$, i.e. a function assigning a real number $v(S)$ to every coalition $S\subseteq N$.
--
--   1. A payoff vector $x\in\mathbb R^N$ is an **imputation** of $v$ if it is efficient and individually rational:
--   $$\sum_{i\in N}x_i=v(N),\qquad x_i\ge v(\{i\})\ \text{ for every } i\in N.$$
--   2. The **excess** of a coalition $S$ at $x$ is $e(S,x)=v(S)-\sum_{i\in S}x_i$: how much $S$ could still claim beyond what $x$ gives it.
--   3. The **excess vector** $\theta(x)\in\mathbb R^{2^n}$ lists the $2^n$ excesses $e(S,x)$, $S\subseteq N$, in non-increasing order.
--   4. An imputation $x$ is the **nucleolus** of $v$ if no imputation $y$ has a lexicographically smaller excess vector, that is, there is no imputation $y$ with $\theta(y)<_{\mathrm{lex}}\theta(x)$.
--
--   The nucleolus (Schmeidler 1969) successively minimizes the largest excess, then the second largest, and so on, over the imputations. Schmeidler proved that when the imputation set is nonempty there is exactly one such $x$, written $\nu(v)$; so "$x$ is the nucleolus" and "$x=\nu(v)$" say the same thing.
--
--   **Formalization Note.** The excess vector is the multiset of the $2^n$ excesses (over `Finset.univ : Finset (Finset (Fin n))`, so $\emptyset$ and $N$ included) sorted by `≥` into a `List ℝ`; the comparison is `List.Lex (· < ·)` on lists of equal length $2^n$. The coalitions $\emptyset$ and $N$ have excess $0$ at every imputation, and adding the same entries to two multisets does not change the lexicographic order of their sorted lists, so including them agrees with the common convention over proper nonempty coalitions. The definition is stated for an arbitrary game and does not assume existence or uniqueness.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 15, §4.2 and p. 24, proof of Theorem 3 (the nucleolus, cited from Schmeidler 1969 and Muto et al. 1988; the paper gives no definition). Standard definition: D. Schmeidler, The nucleolus of a characteristic function game, SIAM J. Appl. Math. 17(6):1163–1170, 1969, https://doi.org/10.1137/0117107

import Mathlib

namespace SeqLoss.LiabilityGame

/-- `x` is an imputation of the game `v` on the player set `N = Fin n`: it is efficient,
`∑_{i ∈ N} x_i = v(N)`, and individually rational, `v({i}) ≤ x_i` for every player `i`. -/
def IsImputation {n : ℕ} (v : Finset (Fin n) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∑ i, x i = v Finset.univ ∧ ∀ i, v {i} ≤ x i

/-- The excess `e(S, x) = v(S) - ∑_{i ∈ S} x_i` of coalition `S` at the payoff vector `x`. -/
def excess {n : ℕ} (v : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  v S - ∑ i ∈ S, x i

/-- The excess vector `θ(x)`: the `2^n` excesses `e(S, x)`, one for every coalition `S ⊆ N`
(including `∅` and `N`), arranged in non-increasing order. -/
noncomputable def excessVector {n : ℕ} (v : Finset (Fin n) → ℝ) (x : Fin n → ℝ) : List ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).val.map (excess v x)).sort (· ≥ ·)

/-- `x` is the nucleolus of `v` (Schmeidler 1969): `x` is an imputation and no imputation `y`
has an excess vector `θ(y)` that is lexicographically smaller than `θ(x)`. -/
def IsNucleolus {n : ℕ} (v : Finset (Fin n) → ℝ) (x : Fin n → ℝ) : Prop :=
  IsImputation v x ∧
    ∀ y, IsImputation v y → ¬ List.Lex (· < ·) (excessVector v y) (excessVector v x)

end SeqLoss.LiabilityGame


