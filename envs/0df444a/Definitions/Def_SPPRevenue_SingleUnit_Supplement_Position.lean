-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_Position
-- name    : SPPRevenue_SingleUnit_Supplement_Position
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:12:45.674166+00:00
-- url     : https://prove2.me/theorems/e9281875-a012-4a88-a7fb-97fb676beb74
-- title:
--   §6.1, pp. 20–22 — click-through rates, feasible expected clicks, inequalities (8), the mechanism of Lemma 6
-- statement:
--   The position-auction (PA) setting of §6.1: $n$ positions and $n$ buyers.
--
--   1. **Click-through rates.** $1\ge\alpha_1\ge\alpha_2\ge\dots\ge\alpha_n\ge0$, with $\alpha_{n+1}=0$ and gaps $\alpha_j-\alpha_{j+1}$.
--   2. **Feasible allocation.** An assignment of buyers to positions, each position receiving at most one buyer and each buyer at most one position; buyer $i$ assigned to position $J_i(a)$ receives $\alpha_{J_i(a)}$ clicks, and an unassigned buyer none.
--   3. **Feasible expected clicks.** $x\in\mathbb R^n$ is feasible if some probability distribution $y$ on feasible allocations has $x_i=\sum_ay_a\alpha_{J_i(a)}$ for all $i$.
--   4. **Inequalities (8).** $\sum_{i\in S}x_i\le\sum_{j=1}^{|S|}\alpha_j$ for every $S\subseteq[n]$.
--   5. **The mechanism of Lemma 6.** From mechanisms $(x^j,\pi^j)$ for $j$ units, $j\in[n]$:
--   $$x_i(v)=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})x_i^j(v),\qquad\pi_i(v)=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})\pi_i^j(v).$$
--
--   **Formalization Note** Positions and buyers are `Fin n`; position index $j$ is the paper's $j+1$, and the mechanism for $j+1$ units sits at index $j$. An allocation is a map from buyers to `Option` positions that is injective on assigned buyers; a buyer cannot hold two positions by construction.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 20–22, §6.1, Lemma 5 (8), Lemma 6

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Mechanism

namespace SPPRevenue.SingleUnit.Supplement

/-- Click-through rates of the `n` positions (§6.1, p. 20): `1 ≥ α_1 ≥ α_2 ≥ … ≥ α_n ≥ 0`. -/
def IsCTR {n : ℕ} (α : Fin n → ℝ) : Prop :=
  Antitone α ∧ ∀ j, 0 ≤ α j ∧ α j ≤ 1

/-- `α_j − α_{j+1}`, with `α_{n+1} = 0` (Lemma 6, p. 22). -/
noncomputable def ctrGap {n : ℕ} (α : Fin n → ℝ) (j : Fin n) : ℝ :=
  α j - (if h : (j : ℕ) + 1 < n then α ⟨(j : ℕ) + 1, h⟩ else 0)

/-- A feasible allocation of buyers to positions (§6.1, p. 20): `a i = some j` assigns buyer `i` to
position `j`, `a i = none` leaves it unassigned; no position receives two buyers. -/
def IsPAAllocation {n : ℕ} (a : Fin n → Option (Fin n)) : Prop :=
  ∀ i k j, a i = some j → a k = some j → i = k

/-- The clicks `α_{J_i(a)}` buyer `i` receives under allocation `a` (`0` if unassigned). -/
noncomputable def paClicks {n : ℕ} (α : Fin n → ℝ) (a : Fin n → Option (Fin n)) (i : Fin n) : ℝ :=
  (a i).elim 0 α

/-- A vector of expected clicks is feasible (§6.1, pp. 20–21) if it is produced by a randomized
allocation: a probability distribution `y` on feasible allocations with
`x_i = Σ_{a} y_a α_{J_i(a)}` for every buyer `i`. -/
def PAFeasibleClicks {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ y : (Fin n → Option (Fin n)) → ℝ, (∀ a, 0 ≤ y a) ∧ (∀ a, ¬ IsPAAllocation a → y a = 0) ∧
    ∑ a, y a = 1 ∧ ∀ i, x i = ∑ a, y a * paClicks α a i

/-- Inequalities (8) (Lemma 5, p. 21): `Σ_{i ∈ S} x_i ≤ Σ_{j=1}^{|S|} α_j` for every `S ⊆ [n]`. -/
def ClickIneq {n : ℕ} (α : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ S : Finset (Fin n),
    ∑ i ∈ S, x i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < S.card), α j

/-- The position-auction mechanism built from the mechanisms `M j` for `j + 1` units (Lemma 6,
p. 22): `x_i(v) = Σ_j (α_j − α_{j+1}) x_i^j(v)` and `π_i(v) = Σ_j (α_j − α_{j+1}) π_i^j(v)`. -/
noncomputable def paMech {n : ℕ} (α : Fin n → ℝ) (M : Fin n → DirectMech n) : DirectMech n where
  alloc v i := ∑ j, ctrGap α j * (M j).alloc v i
  pay v i := ∑ j, ctrGap α j * (M j).pay v i

end SPPRevenue.SingleUnit.Supplement


