-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_MarketD
-- name    : PLCMarkets_ExactCover_MarketD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:03:53.896984+00:00
-- url     : https://prove2.me/theorems/ed9817ed-62ff-42e9-a9f6-cd4f3bc6acbe
-- title:
--   The Arrow–Debreu market $D(\mathcal C)$ built from an X3C instance (§8)
-- statement:
--   Let $\mathcal C=(C_1,\dots,C_n)$ be a family of subsets of $X=\{x_1,\dots,x_n\}$. The Arrow–Debreu market $D=D(\mathcal C)$ has $2n+1$ goods — good $0$, a good $C_i$ for each set and a good $x_j$ for each element — and $2n+2$ agents: the price-regulating agent $0$, an agent $C_i$ for each set, an agent $x_j$ for each element, and an extra agent. Let $e_0=n^3$.
--
--   1. **Agent $0$** owns $e_0$ units of every good. His utility for every good has slope $2$ until $e_0$ units and slope $1$ from then on until infinity.
--   2. **Agent $C_i$** owns $1$ unit of good $C_i$. His utility has a segment of slope $1$ and length $1/2$ for good $0$, a segment of slope $1/3$ and length $1/6$ for each good $x_j$ with $x_j\in C_i$, and a segment of slope $1/9$ and length $1/4$ for good $C_i$; apart from these segments his functions are flat.
--   3. **Agent $x_j$** owns $1/6$ unit of good $x_j$. His utility has one segment of slope $1$ and length $1/12$ for good $0$, and is flat otherwise.
--   4. **The extra agent** owns $n/2$ units of good $0$. His utility has a segment of slope $1$ and length $3/4$ for each good $C_i$, and is flat otherwise.
--
--   The total supplies are therefore $n^3+n/2$ of good $0$, $n^3+1$ of each good $C_i$, and $n^3+1/6$ of each good $x_j$.
--
--   For a price vector $p$ on the goods, $p_m=\min_j p(j)$ is the **minimum price**, and $S\subseteq\{1,\dots,n\}$ is the set of indices $i$ with
--
--   $$
--   p(C_i)\ \ge\ p_m+\frac16\sum_{x_j\in C_i}p(x_j),
--   $$
--
--   the subcollection $S$ that the proof of Lemma 8.3 extracts from an approximate equilibrium.
--
--   **Formalization Note.** The page (p. 10:20) prints the extra agent's segment for each good $C_i$ as "slope 1 and length $3n/4$". Every computation with it in the paper uses length $3/4$ per good: the extra agent's income $n\,p_m$ "is just enough to buy the segments of length $3/4$ of all the goods $C_i$", the surplus of $1/4$ unit of each unused $C_i$ (p. 10:21), and "only the extra agent buys (at most) $3/4$ units of good $C_i$" (pp. 10:22–10:23). With length $3n/4$ the prices of Lemma 8.2 are not an equilibrium, so the length here is $3/4$. Indices are 0-based; goods and agents are small inductive types named as in the paper. Only the Arrow–Debreu market $D$ is defined; the Fisher market $F$ of the same section is not part of this mission.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, pp. 10:19-10:20, §8 (construction of D); p. 10:21, proof of LEMMA 8.3 (p_m); p. 10:22 (definition of S)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_ADMarket

namespace PLCMarkets.ExactCover

/-- The `2n + 1` goods of the §8 markets (p. 10:19): good `0`, a good `C_i` for each set, and a good
`x_j` for each element (indices `i, j : Fin n`). -/
inductive Good (n : ℕ) where
  | zero : Good n
  | set : Fin n → Good n
  | elem : Fin n → Good n
  deriving DecidableEq, Fintype

/-- The `2n + 2` agents of the §8 markets (pp. 10:19–10:20): the price-regulating agent `0`,
an agent `C_i` for each set, an agent `x_j` for each element, and the extra agent. -/
inductive Agent (n : ℕ) where
  | regulator : Agent n
  | setAgent : Fin n → Agent n
  | elemAgent : Fin n → Agent n
  | extra : Agent n
  deriving DecidableEq, Fintype

instance (n : ℕ) : Nonempty (Good n) := ⟨Good.zero⟩

/-- Initial endowments of the Arrow–Debreu market `D` (p. 10:20): agent `0` owns `n³` units of
every good, agent `C_i` one unit of good `C_i`, agent `x_j` `1/6` unit of good `x_j`, and the
extra agent `n/2` units of good `0`. -/
def endowD (n : ℕ) : Agent n → Good n → ℚ
  | .regulator, _ => (n : ℚ) ^ 3
  | .setAgent i, .set i' => if i' = i then 1 else 0
  | .elemAgent j, .elem j' => if j' = j then 1 / 6 else 0
  | .extra, .zero => (n : ℚ) / 2
  | _, _ => 0

theorem endowD_nonneg (n : ℕ) (i : Agent n) (j : Good n) : 0 ≤ endowD n i j := by
  cases i <;> cases j <;> simp only [endowD] <;> (try split_ifs) <;> positivity

/-- Agent `0`'s utility for every good: slope `2` until `e₀ = n³` units, then slope `1` until
infinity. -/
def regulatorUtil (n : ℕ) : PLUtility :=
  PLUtility.oneSeg 2 ((n : ℚ) ^ 3) 1 (by norm_num) (by positivity) (by norm_num) (by norm_num)

/-- Utility functions of the Arrow–Debreu market `D` (p. 10:20):
* agent `0`: `regulatorUtil n` for every good;
* agent `C_i`: a segment of slope `1`, length `1/2` for good `0`; slope `1/3`, length `1/6` for each
  good `x_j` with `x_j ∈ C_i`; slope `1/9`, length `1/4` for good `C_i`; flat otherwise;
* agent `x_j`: a segment of slope `1`, length `1/12` for good `0`; flat otherwise;
* extra agent: a segment of slope `1`, length `3/4` for each good `C_i`; flat otherwise.

The page prints the extra agent's length as `3n/4` (p. 10:20); every computation of the paper
uses `3/4` per good (proof of Lemma 8.2, p. 10:21; Claim 8.6, p. 10:22; end of Lemma 8.3,
pp. 10:22–10:23), and with `3n/4` the prices of Lemma 8.2's proof are not an equilibrium, so the
printed `3n/4` is a typo and `3/4` is used here. -/
def utilD {n : ℕ} (C : Fin n → Finset (Fin n)) : Agent n → Good n → PLUtility
  | .regulator, _ => regulatorUtil n
  | .setAgent _, .zero => PLUtility.oneSeg 1 (1 / 2) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
  | .setAgent i, .elem j =>
      if j ∈ C i then PLUtility.oneSeg (1 / 3) (1 / 6) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
      else PLUtility.flat
  | .setAgent i, .set i' =>
      if i' = i then PLUtility.oneSeg (1 / 9) (1 / 4) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
      else PLUtility.flat
  | .elemAgent _, .zero => PLUtility.oneSeg 1 (1 / 12) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
  | .elemAgent _, _ => PLUtility.flat
  | .extra, .set _ => PLUtility.oneSeg 1 (3 / 4) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
  | .extra, _ => PLUtility.flat

/-- The Arrow–Debreu market `D(C)` built from an X3C instance `C` (Vazirani–Yannakakis 2011, §8,
pp. 10:19–10:20), with goods `Good n`, agents `Agent n`, endowments `endowD n` and utilities
`utilD C`. -/
def marketD {n : ℕ} (C : Fin n → Finset (Fin n)) : ADMarket (Agent n) (Good n) where
  endow := endowD n
  endow_nonneg := endowD_nonneg n
  util := utilD C

/-- The minimum price `p_m = min_j p(j)` of a price vector on the goods of `D(C)`. -/
noncomputable def minPrice {n : ℕ} (p : Good n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

/-- The subcollection `S` of p. 10:22: the indices `i` with
`p(C_i) ≥ p_m + (1/6) Σ_{x_j ∈ C_i} p(x_j)`. -/
noncomputable def coverSet {n : ℕ} (C : Fin n → Finset (Fin n)) (p : Good n → ℝ) :
    Finset (Fin n) :=
  by classical exact
    Finset.univ.filter (fun i => minPrice p + (1 / 6) * ∑ j ∈ C i, p (Good.elem j) ≤ p (Good.set i))

end PLCMarkets.ExactCover


