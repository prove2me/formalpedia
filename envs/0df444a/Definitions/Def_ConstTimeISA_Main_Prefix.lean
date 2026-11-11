-- Prove2me | Definitions.Def_ConstTimeISA_Main_Prefix
-- name    : ConstTimeISA_Main_Prefix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:41:24.587573+00:00
-- url     : https://prove2.me/theorems/eb54766a-af6e-472a-9efb-a716134fb177
-- title:
--   Strings over [0..σ), the base-σ value val_σ, and prefix rank, prefix special rank and prefix select (Definitions 2.3 = 3.24, 4.1)
-- statement:
--   Strings over the alphabet $[0..\sigma)$ are lists of natural numbers below $\sigma$ (`IsStr`); a sequence $W \in ([0..\sigma)^\ell)^m$ is a list of $m$ such strings, each of length $\ell$ (`IsSeq`). Positions are 1-based: $W[i]$ is the $i$-th string.
--
--   * **Value** (Definition 4.1): $\mathrm{val}_\sigma(X) = \sum_{i=1}^{|X|} X[i]\,\sigma^{|X|-i}$, with $\mathrm{val}_\sigma(\varepsilon) = 0$.
--   * **Prefix rank:** $\text{prefix-rank}_W(j, X) = |\{ i \in [1..j] : X \text{ is a prefix of } W[i]\}|$.
--   * **Prefix special rank:** $\text{prefix-special-rank}_W(j, p) = \text{prefix-rank}_W(j, W[j][1..p])$.
--   * **Prefix select:** $\text{prefix-select}_W(r, X)$ is the $r$-th smallest $i \in [1..m]$ such that $X$ is a prefix of $W[i]$ when $1 \le r \le \text{prefix-rank}_W(m, X)$, and $\infty$ otherwise.
--
--   **Formalization Note.** The value $\infty$ of prefix select is encoded as $0$, which is never a valid index.
-- source:
--   Kempa, Kociumaka, Constant-Time Inverse Suffix Array Queries in Compact Space and Sublinear-Time Construction of Suffix Array Indexes, STOC 2027 submission, arXiv:2608.19123 (manuscript sha256 f5bb728a…), p. 6, Definition 2.3; p. 17, Definition 3.24; p. 18, Definition 4.1

import Mathlib

set_option autoImplicit false

namespace ConstTimeISA.Main

/-!
# Strings over `[0..σ)`, their base-σ value, and prefix range queries

Kempa, Kociumaka, *Constant-Time Inverse Suffix Array Queries in Compact Space and Sublinear-Time
Construction of Suffix Array Indexes*, STOC 2027 submission, arXiv:2608.19123 (manuscript sha256
f5bb728a…): Definition 2.3, p. 6 (PDF 7) = Definition 3.24, p. 17 (PDF 18); Definition 4.1,
p. 18 (PDF 19).

**Formalization Note.** Strings are lists of natural numbers; positions are 1-based as in the
paper (`W[i]` is entry `i − 1` of the list). "`X` is a prefix of `Y`" is `X <+: Y`. The value `∞`
of a prefix select query is encoded as `0`, which is never a valid index (indices are in `[1..m]`).
-/

/-- A string over the alphabet `[0..σ)`. -/
def IsStr (σ : ℕ) (X : List ℕ) : Prop := ∀ c ∈ X, c < σ

/-- A sequence `W ∈ ([0..σ)^ℓ)^m` of `m` strings of length `ℓ` over `[0..σ)`. -/
def IsSeq (σ m ℓ : ℕ) (W : List (List ℕ)) : Prop :=
  W.length = m ∧ ∀ x ∈ W, x.length = ℓ ∧ IsStr σ x

/-- Definition 4.1: `val_σ(X) = ∑_{i=1}^{|X|} X[i] · σ^{|X|−i}` (big-endian base σ); `val_σ(ε) = 0`.
Written 0-based: entry `i` of the list has weight `σ^{|X|−1−i}`. -/
def val (σ : ℕ) (X : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range X.length, X.getD i 0 * σ ^ (X.length - 1 - i)

/-- Definition 3.24, prefix rank: `prefix-rank_W(j, X) = |{i ∈ [1..j] : X is a prefix of W[i]}|`. -/
def prefixRank {α : Type} [DecidableEq α] (W : List (List α)) (j : ℕ) (X : List α) : ℕ :=
  ((Finset.Icc 1 j).filter fun i => X <+: W.getD (i - 1) []).card

/-- Definition 3.24, prefix special rank:
`prefix-special-rank_W(j, p) = prefix-rank_W(j, W[j][1..p])`. -/
def prefixSpecialRank {α : Type} [DecidableEq α] (W : List (List α)) (j p : ℕ) : ℕ :=
  prefixRank W j ((W.getD (j - 1) []).take p)

/-- Definition 3.24, prefix select: the `r`-th smallest `i ∈ [1..m]` such that `X` is a prefix of
`W[i]` if `r ≤ prefix-rank_W(m, X)`, and `∞` otherwise; `∞` is encoded as `0`. -/
def prefixSelect {α : Type} [DecidableEq α] (W : List (List α)) (r : ℕ) (X : List α) : ℕ :=
  if 1 ≤ r ∧ r ≤ prefixRank W W.length X then
    ((List.range' 1 W.length).filter fun i => X <+: W.getD (i - 1) []).getD (r - 1) 0
  else 0

end ConstTimeISA.Main


