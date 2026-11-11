-- Prove2me | Definitions.Def_SubadditiveMMS580_Amplification_Setting
-- name    : SubadditiveMMS580_Amplification_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T19:53:41.54653+00:00
-- url     : https://prove2.me/theorems/5d34e86d-038a-47e1-8b93-29f5c0df6daa
-- title:
--   Iterated logarithm $\log_2^* n$, the factor $\alpha(n)=1/(4D(n)-2)$, disjoint valuable families and finitely supported distributions
-- statement:
--   This file fixes the paper-specific vocabulary of the mission. Goods form a finite set $M$ (written $\{0,\dots,m-1\}$) and agents a set $[n]$.
--
--   1. The **tower** of equation (2): $E_0=1$ and $E_{r+1}=2^{E_r}$, so $E_1=2$, $E_2=4$, $E_3=16$, $E_4=65536$.
--   2. The **iterated logarithm** of a natural number $n$ (equation (2)):
--   $$\log_2^* n=\min\{r\ge 0:\ n\le E_r\}.$$
--   The minimum exists because $n\le E_n$ for every $n$; for example $\log_2^*2=1$, $\log_2^*3=\log_2^*4=2$ and $\log_2^* n=3$ for $5\le n\le 16$.
--   3. $d(n)=1+\log_2^* n$ and $D(n)=2^{\lceil\log_2 d(n)\rceil}$, the smallest power of two that is **at least** $d(n)$ (equality allowed).
--   4. The guarantee
--   $$\alpha(n)=\frac{1}{4D(n)-2}.$$
--   For instance $\alpha(2)=1/6$, $\alpha(n)=1/14$ for $3\le n\le 16$, and $\alpha(n)=1/30$ for $17\le n\le 65536$.
--   5. For a valuation $v$ on $2^M$, a **valuable family** $W_1,\dots,W_n\subseteq M$ consists of $n$ pairwise disjoint sets with $v(W_r)\ge1$ for every $r$. The family need not cover $M$.
--   6. A **finitely supported probability distribution** $\sigma$ on a set $X$ is a finite support $\operatorname{supp}(\sigma)\subseteq X$ together with strictly positive weights $\sigma(x)$, $x\in\operatorname{supp}(\sigma)$, summing to one; the probability of an event $E$ is $\Pr_{x\sim\sigma}[E]=\sum_{x\in\operatorname{supp}(\sigma),\,E(x)}\sigma(x)$.
--
--   These objects appear in the statement of Theorem 1.1 (the factor $\alpha(n)$ and its lower bound) and in the supporting results of §3 (valuable families, bidding and allocation distributions, the multiplicity bound $1+\log_2^*n$).
--
--   **Formalization Note** $\log_2^*$ is defined through the natural-number tower exactly as in equation (2), so no real logarithm is iterated; $\lceil\log_2 d\rceil$ is `Nat.clog 2 d`, the least $k$ with $d\le 2^k$. Since $D(n)\ge1$, the denominator of $\alpha(n)$ is at least $2$. The file also contains the one-line fact $n\le E_n$, used only to make the minimum total. Normalization, monotonicity, subadditivity, allocations, multi-allocations and the maximin share are taken from published definitions (`MultiAllocToAlloc.Subadditive.*`, `SubmodOrder.Subadditive`, `LittleCharity.MMS.mms`).
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), §1.1 p. 2 (d(n), D(n), α(n)); §2.1 eq. (2) p. 8 (E_r, log*₂ n); §3.1–3.3 pp. 11–17 (disjoint valuable sets, finitely supported distributions)

import Mathlib

/-!
# Iterated logarithm, the guarantee `α(n)`, valuable families and finite distributions

Bo Li, Ankang Sun, *Toward Constant-Factor Maximin Share Guarantees for Subadditive
Valuations*, STOC 2027 submission #580 (October 2026): §1.1 p. 2 (`d(n)`, `D(n)`, `α(n)`),
§2.1 eq. (2) p. 8 (tower `E_r` and `log*₂ n`), §3 pp. 11–17 (disjoint valuable sets,
finitely supported distributions).

Conventions. Goods are `Fin m`, agents `Fin n`; a valuation is a real set function
`Finset (Fin m) → ℝ` (normalization, monotonicity and subadditivity are the published
predicates `MultiAllocToAlloc.Subadditive.IsNormalized`, `…IsMonotone`,
`SubmodOrder.Subadditive`, stated as hypotheses where used).
-/

set_option autoImplicit false

namespace SubadditiveMMS580.Amplification

/-- Eq. (2), p. 8: the tower `E₀ = 1`, `E_{r+1} = 2^{E_r}`. -/
def tower : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 ^ tower r

/-- Every natural number is bounded by some tower value: `n ≤ E_n`
(used only to make `log*₂` a total, terminating minimum). -/
theorem le_tower_self (n : ℕ) : n ≤ tower n := by
  induction n with
  | zero => simp [tower]
  | succ k ih =>
    show k + 1 ≤ 2 ^ tower k
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (Nat.lt_two_pow_self))

/-- Eq. (2), p. 8: `log*₂ n = min {r ≥ 0 : n ≤ E_r}`. -/
def logStar (n : ℕ) : ℕ :=
  Nat.find (⟨n, le_tower_self n⟩ : ∃ r, n ≤ tower r)

/-- p. 2: `d(n) = 1 + log*₂ n`. -/
def dFun (n : ℕ) : ℕ := 1 + logStar n

/-- p. 2: `D(n) = 2^{⌈log₂ d(n)⌉}`, the smallest power of two at least `d(n)`
(`Nat.clog 2 x` is the least `k` with `x ≤ 2^k`). -/
def bigD (n : ℕ) : ℕ := 2 ^ Nat.clog 2 (dFun n)

/-- p. 2: `α(n) = 1 / (4 D(n) − 2)`. Since `D(n) ≥ 1`, the denominator is at least `2`. -/
noncomputable def alpha (n : ℕ) : ℝ := 1 / (4 * (bigD n : ℝ) - 2)

/-- §3, pp. 13–17: a family `W 1, …, W n` of pairwise disjoint sets of goods, each of value at
least one under `v` ("`n` pairwise disjoint sets of value at least one"). The family need not
cover the goods. -/
def IsValuableFamily {m n : ℕ} (v : Finset (Fin m) → ℝ) (W : Fin n → Finset (Fin m)) : Prop :=
  (∀ r s : Fin n, r ≠ s → Disjoint (W r) (W s)) ∧ ∀ r : Fin n, 1 ≤ v (W r)

/-- A finitely supported probability distribution on a type `α` (pp. 11, 13): a finite support,
strictly positive weights on it, summing to one. -/
structure FinDist (α : Type*) where
  /-- The support of the distribution. -/
  support : Finset α
  /-- The probability of each point (only its values on `support` matter). -/
  weight : α → ℝ
  weight_pos : ∀ x ∈ support, 0 < weight x
  sum_weight : ∑ x ∈ support, weight x = 1

open Classical in
/-- The probability `P_{x ∼ σ}[E x]` of an event `E` under a finitely supported distribution. -/
noncomputable def FinDist.prob {α : Type*} (σ : FinDist α) (E : α → Prop) : ℝ :=
  ∑ x ∈ σ.support.filter E, σ.weight x

end SubadditiveMMS580.Amplification


