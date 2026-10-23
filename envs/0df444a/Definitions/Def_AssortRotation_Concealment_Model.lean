-- Prove2me | Definitions.Def_AssortRotation_Concealment_Model
-- name    : AssortRotation_Concealment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:36.624031+00:00
-- url     : https://prove2.me/theorems/8168b23d-8c74-40c8-9f0b-2619f080ca44
-- title:
--   §2–§4, pp. 7–12 — multi-purchase consumer with diminishing marginal utility: sequential revenue (5)–(7), fixed revenue (4), utility (3), optimized strategies $R^s_*$, $R^f_*$
-- statement:
--   This file sets up the model of Ferreira and Goh's *Assortment Rotation and the Value of Concealment*.
--
--   A retailer has $N$ products with prices $p_1,\dots,p_N$. A consumer's realized valuation shock for product $i$ is $X_i$, and $X_i-p_i$ is its **price-adjusted valuation**. The consumer may buy several products; her utility from buying a set $S$ is
--   $$
--   u(S)=\sum_{j\in S}(X_j-p_j)+\sum_{j=0}^{|S|-1}v(j),
--   $$
--   where the **marginal utility** $v:\mathbb N_0\to\mathbb R$ is nonnegative and (weakly) decreasing. A product is recorded as a pair (price, realized shock).
--
--   1. **Sequential revenue** (rules (5)–(7)). Products are shown one per period. A consumer who has already bought $k$ items buys the current product $(p,X)$ iff $v(k)+X-p\ge 0$. The quantity $\mathrm{seqRev}(v,L,k)$ is the revenue from the list $L$ of products for a consumer who starts with $k$ purchases. Thus $R^s=\mathrm{seqRev}(v,L,0)$ and $R_k(n)=\mathrm{seqRev}(v,L,k)$ when $L$ is the list of the last $n$ products.
--   2. **Fixed revenue** (4). For products listed in an order $\sigma$ of decreasing price-adjusted valuation (Definition 1),
--   $$
--   R^f=\sum_{i=1}^{M}p_{\sigma(i)}\,\mathbb 1\{v(i-1)+X_{\sigma(i)}-p_{\sigma(i)}\ge 0\}.
--   $$
--   3. **Highest remaining price** $\rho^*$: the largest price in a list, and $0$ for the empty list.
--   4. **The optimized strategies.** On a probability space $(\Omega,\mathbb P)$ with shocks $X_i(\omega)$, $R^f(S)$ is the fixed revenue of the subset $S$, and $\mathbb E[R^f_*]$ is the largest expected fixed revenue over all subsets $S\subseteq\{1,\dots,N\}$, the empty set and strict subsets included. $R^s(\tau)$ is the sequential revenue when all $N$ products are shown in the order $\tau$, and $\mathbb E[R^s_*]$ is the largest expected sequential revenue over all orders $\tau$ of the $N$ products.
--
--   These objects state the paper's main result, Theorem 1, and the lemmas used in its proof.
--
--   **Formalization Note.** Positions are 0-based in Lean: the paper's position $i$ with $v(i-1)$ is list position $i-1$ with $v(i-1)$. The marginal utility $v$ is taken directly, with $v\ge 0$ and $v$ antitone, rather than through $V$. The sequential rule uses $\ge 0$ throughout, also for $R_k(n)$, where (7) prints $>0$. The two rules differ only when $v(k)+X_i-p_i=0$, a null event for continuous shocks. In $R^f(S)$ the order $\sigma$ is the canonical one: decreasing $X_i-p_i$, ties broken by smaller index. Product $i$ sits at position $\mathrm{rank}(i)$, the number of products of $S$ ahead of it, and the sum in (4) is written over the products of $S$. Every order of Definition 1 gives the same revenue except on the null event of a tie. Both optima are maxima over finite index sets; the revenues are bounded and measurable, so the integrals are genuine.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), pp. 7–13, §2 (2)–(3), Notation p. 10, Definition 1 p. 10, (4)–(6) p. 11, VoC p. 12, (7) and Lemma 2's ρ*_n p. 13

import Mathlib

namespace AssortRotation.Concealment

open MeasureTheory

noncomputable section

/-- Standing hypotheses on the marginal-utility sequence `v : ℕ₀ → ℝ₊` of (3), p. 8:
`v` is nonnegative and decreasing (in the weak sense, p. 10). -/
def MarginalUtility (v : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ v j) ∧ Antitone v

/-- Sequential revenue, rules (5)–(7), pp. 11 and 13. A product is a pair
`(price, realized shock)`; `seqRev v L k` is the revenue the retailer earns when the
products of `L` are shown one per period in list order to a consumer who has already
bought `k` items, and who buys the current product `a` iff `v(k) + X − p ≥ 0`.
Thus `R^s = seqRev v L 0` ((6)) and `R_k(n) = seqRev v (last n products) k` ((7)). -/
def seqRev (v : ℕ → ℝ) : List (ℝ × ℝ) → ℕ → ℝ
  | [], _ => 0
  | a :: t, k => if 0 ≤ v k + a.2 - a.1 then a.1 + seqRev v t (k + 1) else seqRev v t k

/-- Fixed-assortment revenue, (4), p. 11, along a list `L'` (intended to be sorted by
decreasing price-adjusted valuation, Definition 1): the product at 0-based list position
`i` (the paper's position `i + 1`) pays its price iff `v(i) + X − p ≥ 0`. The second
argument is the position of the head of the list. -/
def fixedRevAux (v : ℕ → ℝ) : List (ℝ × ℝ) → ℕ → ℝ
  | [], _ => 0
  | a :: t, i => (if 0 ≤ v i + a.2 - a.1 then a.1 else 0) + fixedRevAux v t (i + 1)

/-- `R^f = ∑_{i=1}^M p_{σ(i)} 1{v(i−1) + X_{σ(i)} − p_{σ(i)} ≥ 0}` for the list
`L' = ((p_{σ(1)}, X_{σ(1)}), …, (p_{σ(M)}, X_{σ(M)}))`, (4), p. 11. -/
def fixedRev (v : ℕ → ℝ) (L' : List (ℝ × ℝ)) : ℝ :=
  fixedRevAux v L' 0

/-- Consumer's utility (3), p. 8, from buying the set `S` of the `M` products with
prices `p` and realized shocks `x`:
`u(S) = ∑_{j ∈ S} (x_j − p_j) + ∑_{j=0}^{|S|−1} v(j)`. -/
def utility {M : ℕ} (v : ℕ → ℝ) (p x : Fin M → ℝ) (S : Finset (Fin M)) : ℝ :=
  (∑ j ∈ S, (x j - p j)) + ∑ j ∈ Finset.range S.card, v j

/-- `ρ*` of Lemma 2, p. 13: the highest price in a list of products (`0` for the empty
list; for nonnegative prices this is exactly `max` of the prices). -/
def rhoStar : List (ℝ × ℝ) → ℝ
  | [] => 0
  | a :: t => max a.1 (rhoStar t)

/-! ### The random model and the optimized strategies (§2, §4, pp. 7–12) -/

variable {Ω : Type*} {N : ℕ}

/-- The products of the subset `S` at outcome `ω`, in increasing index order:
`(p_i, X_i(ω))` for `i ∈ S`. -/
def products (p : Fin N → ℝ) (X : Fin N → Ω → ℝ) (S : Finset (Fin N)) (ω : Ω) :
    List (ℝ × ℝ) :=
  (S.sort (· ≤ ·)).map (fun i => (p i, X i ω))

/-- Position (0-based) of product `i` in the canonical Definition-1 order of the subset `S`
at `ω`: the number of products of `S` with strictly larger price-adjusted valuation
`X_j(ω) − p_j`, plus those with equal valuation and smaller index. This is `σ⁻¹(i) − 1`
for the permutation σ of Definition 1 that breaks ties by index. -/
def rankIn (p : Fin N → ℝ) (X : Fin N → Ω → ℝ) (S : Finset (Fin N)) (ω : Ω) (i : Fin N) : ℕ :=
  (S.filter (fun j => X i ω - p i < X j ω - p j ∨ (X j ω - p j = X i ω - p i ∧ j < i))).card

/-- Fixed-assortment revenue (4), p. 11, of the subset `S` at outcome `ω`, with σ the
canonical Definition-1 order (decreasing `X_i − p_i`, ties by index): product `i ∈ S`
at 0-based position `r = rankIn … i` pays `p_i` iff `v(r) + X_i(ω) − p_i ≥ 0`. -/
def RfSet (v : ℕ → ℝ) (p : Fin N → ℝ) (X : Fin N → Ω → ℝ) (S : Finset (Fin N)) (ω : Ω) : ℝ :=
  ∑ i ∈ S, if 0 ≤ v (rankIn p X S ω i) + X i ω - p i then p i else 0

/-- Sequential revenue (6) when all `N` products are shown in the order `τ`: period `j`
(0-based) shows product `τ j`. -/
def RsPerm (v : ℕ → ℝ) (p : Fin N → ℝ) (X : Fin N → Ω → ℝ) (τ : Equiv.Perm (Fin N)) (ω : Ω) :
    ℝ :=
  seqRev v (List.ofFn fun j => (p (τ j), X (τ j) ω)) 0

/-- `E[R^s_*]`, p. 12: the expected revenue of an optimized sequential assortment, the
maximum over all orders of all `N` products (Remark 1) of the expected sequential revenue. -/
def ERsStar [MeasurableSpace Ω] (μ : Measure Ω) (v : ℕ → ℝ) (p : Fin N → ℝ)
    (X : Fin N → Ω → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun τ : Equiv.Perm (Fin N) => ∫ ω, RsPerm v p X τ ω ∂μ)

/-- `E[R^f_*]`, p. 12: the expected revenue of an optimized fixed assortment, the maximum
over all subsets `S` of the `N` products (including `∅` and strict subsets) of the expected
fixed-assortment revenue. -/
def ERfStar [MeasurableSpace Ω] (μ : Measure Ω) (v : ℕ → ℝ) (p : Fin N → ℝ)
    (X : Fin N → Ω → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin N) => ∫ ω, RfSet v p X S ω ∂μ)

end

end AssortRotation.Concealment


