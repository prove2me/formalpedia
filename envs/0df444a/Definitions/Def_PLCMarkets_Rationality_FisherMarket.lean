-- Prove2me | Definitions.Def_PLCMarkets_Rationality_FisherMarket
-- name    : PLCMarkets_Rationality_FisherMarket
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:57:03.189768+00:00
-- url     : https://prove2.me/theorems/cb62e4fc-ea3b-4139-9ecf-a65d6bb05f0b
-- title:
--   Fisher market with additively separable piecewise-linear concave utilities, and its equilibrium prices (§2)
-- statement:
--   **Piecewise-linear concave utilities.** A utility function $f:\mathbb R_+\to\mathbb R_+$ of one good is given by rational data: a finite list of bounded **segments** $(c_1,a_1),\dots,(c_m,a_m)$, each with a slope $c_k\ge 0$ and an amount $a_k>0$, and the slope $c_\infty\ge0$ of a last, unbounded segment, with nonincreasing slopes
--   $$c_1\ge c_2\ge\cdots\ge c_m\ge c_\infty\ge 0 .$$
--   The function has slope $c_k$ on $[a_1+\dots+a_{k-1},\,a_1+\dots+a_k]$ and slope $c_\infty$ beyond $A=a_1+\dots+a_m$:
--   $$f(x)=\sum_{k=1}^m c_k\min\bigl(\max(x-a_1-\dots-a_{k-1},0),\,a_k\bigr)+c_\infty\max(x-A,0).$$
--   So $f$ is nonnegative, nondecreasing, concave and piecewise linear with $f(0)=0$.
--
--   **Fisher market.** There are $n$ buyers $B=\{1,\dots,n\}$ and $g$ divisible goods $G=\{1,\dots,g\}$, one unit of each good. Buyer $i$ has money $e(i)\in\mathbb Q$, $e(i)>0$, and for each good $j$ a piecewise-linear concave utility $f^i_j$ as above. Her utility for a bundle $x=(x_1,\dots,x_g)$ is additively separable:
--   $$u_i(x)=\sum_{j\in G}f^i_j(x_j).$$
--
--   **Equilibrium.** Given prices $p=(p_1,\dots,p_g)$, a bundle $x\ge 0$ is *optimal* for buyer $i$ if $\sum_j p_jx_j\le e(i)$ and $u_i(y)\le u_i(x)$ for every $y\ge0$ with $\sum_jp_jy_j\le e(i)$. The prices $p$ are *equilibrium (market clearing) prices* if $p\ge 0$ and there is an allocation $(x_{ij})$ in which every buyer receives an optimal bundle and every good is exactly sold out:
--   $$\sum_{i\in B}x_{ij}=1\qquad\text{for every } j\in G.$$
--
--   This is the model all results of the mission are stated about.
--
--   **Formalization Note.** Buyers and goods are `Fin n` and `Fin g`; market data are rationals, and prices and allocations are reals. Each $f^i_j$ is a structure `PLConcave` holding the list of `(slope, amount)` pairs of its bounded segments and the slope `tail` of its last, unbounded segment, with the well-formedness conditions (nonnegative slopes, positive amounts, slopes nonincreasing down to the tail slope) as fields, so no statement can forget them. A piecewise-linear function on $\mathbb R_+$ has an unbounded last piece, which the paper calls "the last (infinite) segment of $f^i_j$" (§6, p. 10:10); $c_\infty=0$ gives a function that is flat after its bounded segments. The normalization $f^i_j(0)=0$ changes no optimal bundle. The supply of every good is one unit, the paper's normalization "without loss of generality", and budgets are positive (the paper's $e(i)\in\mathbb Q_+$). The paper's footnote 3 allows goods of price zero to be left partly unsold; since utilities are nondecreasing, such goods can always be handed out without lowering anyone's utility, so requiring exact clearing of every good defines the same set of equilibrium prices.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, pp. 10:6-10:7, §2 (model, segments, footnote 3)

import Mathlib

namespace PLCMarkets.Rationality

/-- A nondecreasing, concave, piecewise-linear function `f : ℝ₊ → ℝ₊` with `f 0 = 0` and rational
data (Vazirani–Yannakakis 2011, §2, pp. 10:6–10:7; the last, unbounded piece is "the last
(infinite) segment of `f^i_j`" of §6, p. 10:10).

The bounded segments are listed from the origin: `segs = [(c₁, a₁), (c₂, a₂), …, (c_m, a_m)]`
means that `f` has slope `c₁` on `[0, a₁]`, slope `c₂` on `[a₁, a₁ + a₂]`, and so on (a pair is
`(slope, amount)`); beyond `a₁ + ⋯ + a_m` the function has slope `tail` forever (`tail = 0`: `f`
is flat there). Slopes are nonnegative (`f` is nondecreasing), amounts are positive, and slopes
are nonincreasing along the list and down to `tail` (`f` is concave). -/
structure PLConcave where
  /-- The segments, as `(slope, amount)` pairs, in order from the origin. -/
  segs : List (ℚ × ℚ)
  slope_nonneg : ∀ s ∈ segs, 0 ≤ s.1
  amount_pos : ∀ s ∈ segs, 0 < s.2
  slope_antitone : segs.Pairwise (fun s t => t.1 ≤ s.1)
  /-- The slope of the last, unbounded piece `[a₁ + ⋯ + a_m, ∞)`. -/
  tail : ℚ
  tail_nonneg : 0 ≤ tail
  tail_le : ∀ s ∈ segs, tail ≤ s.1

/-- Evaluation of the piecewise-linear function with segments `segs` at the point `x`
(negative `x` is treated as `0`):
`f(x) = Σ_k c_k · min(max(x − a₁ − ⋯ − a_{k−1}, 0), a_k)`. -/
noncomputable def plEval : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 0
  | (c, a) :: rest, x => (c : ℝ) * min (max x 0) (a : ℝ) + plEval rest (x - (a : ℝ))

/-- The value `f(x)` of a piecewise-linear concave function: the bounded segments, plus the
unbounded last piece of slope `tail` beyond `a₁ + ⋯ + a_m`. -/
noncomputable def PLConcave.eval (f : PLConcave) (x : ℝ) : ℝ :=
  plEval f.segs x + (f.tail : ℝ) * max (x - (((f.segs.map Prod.snd).sum : ℚ) : ℝ)) 0

/-- A Fisher market with `n` buyers (`Fin n`) and `g` divisible goods (`Fin g`), one unit of each
good, rational positive budgets `e(i)`, and additively separable piecewise-linear concave
utilities: `f^i_j` is `util i j` (Vazirani–Yannakakis 2011, §2, p. 10:6). -/
structure FisherMarket (n g : ℕ) where
  /-- The money `e(i)` of buyer `i`. -/
  budget : Fin n → ℚ
  budget_pos : ∀ i, 0 < budget i
  /-- `util i j` is the function `f^i_j` giving buyer `i`'s utility from good `j`. -/
  util : Fin n → Fin g → PLConcave

namespace FisherMarket

variable {n g : ℕ}

/-- Buyer `i`'s utility `u_i(x) = Σ_j f^i_j(x_j)` for a bundle `x`. -/
noncomputable def utility (M : FisherMarket n g) (i : Fin n) (x : Fin g → ℝ) : ℝ :=
  ∑ j, (M.util i j).eval (x j)

/-- `x` is an optimal bundle (a utility-maximizing bundle in the budget set) for buyer `i`
at prices `p`: `x ≥ 0`, `Σ_j p_j x_j ≤ e(i)`, and no bundle `y ≥ 0` with
`Σ_j p_j y_j ≤ e(i)` gives `i` more utility. -/
def IsOptimalBundle (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (x : Fin g → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∑ j, p j * x j ≤ (M.budget i : ℝ) ∧
    ∀ y : Fin g → ℝ, (∀ j, 0 ≤ y j) → ∑ j, p j * y j ≤ (M.budget i : ℝ) →
      M.utility i y ≤ M.utility i x

/-- `p` are equilibrium (market clearing) prices (Vazirani–Yannakakis 2011, §2, p. 10:6): prices
are nonnegative, and there is an allocation giving every buyer an optimal bundle such that
every good is exactly cleared (its unit supply is fully sold). -/
def IsEquilibrium (M : FisherMarket n g) (p : Fin g → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧
    ∃ x : Fin n → Fin g → ℝ, (∀ i, M.IsOptimalBundle p i (x i)) ∧ ∀ j, ∑ i, x i j = 1

end FisherMarket

end PLCMarkets.Rationality


