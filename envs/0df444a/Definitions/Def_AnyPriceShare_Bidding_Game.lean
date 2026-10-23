-- Prove2me | Definitions.Def_AnyPriceShare_Bidding_Game
-- name    : AnyPriceShare_Bidding_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:18.306113+00:00
-- url     : https://prove2.me/theorems/e2b3744a-d3b3-4edb-8d46-2357d3120c5b
-- title:
--   The Bidding Game, p. 14 — rounds, budgets, legal plays, strategies, guarantees, and the strategies of Lemmas 4.4 and D.3
-- statement:
--   This file encodes the **Bidding Game** of p. 14 of Babaioff, Ezra and Feige, together with what it means for a strategy to guarantee an agent a value "regardless of the strategies of the other agents".
--
--   **The game.** Agents $k$ start with budgets $b_k$. At the beginning of round $t$ write $M^{(t)}$ for the items still available, $b_k^{(t)}$ for the budget of agent $k$ and $B^{(t)}=\sum_k b_k^{(t)}$ for the total budget. While $M^{(t)}\ne\emptyset$:
--   1. every agent $k$ bids an amount $r_k^{(t)}\in[0,b_k^{(t)}]$;
--   2. a highest bidder $w^{(t)}$ wins (ties broken arbitrarily);
--   3. the winner selects a non-empty set $W^{(t)}\subseteq M^{(t)}$ she can afford, $|W^{(t)}|\cdot r^{(t)}_{w^{(t)}}\le b^{(t)}_{w^{(t)}}$, pays $r^{(t)}_{w^{(t)}}$ per item, and $M^{(t+1)}=M^{(t)}\setminus W^{(t)}$.
--
--   A **play** is the list of rounds (all bids, the winner, the set taken) in which every round obeys these rules; it is **complete** when no item is left. Agent $i$'s bundle is the union of the sets she took.
--
--   **Strategies and guarantees.** A strategy of agent $i$ maps the history so far to a bid and the set she takes if she wins. A strategy **guarantees** agent $i$ (with additive item values $u$) the value $x$ if
--   1. at every history reachable while $i$ follows it with items left, it prescribes a legal move (a bid in $[0,b_i^{(t)}]$ and a non-empty set of available items affordable at that bid), and
--   2. in every complete play in which $i$ follows it — whatever the other agents bid, however ties are broken and whatever the other winners take — $i$'s bundle has value at least $x$.
--
--   **Named strategies.**
--   - *Bid-your-max-value* (p. 15): bid $\min\{x_i^{(t)}/v_i(M),\,b_i^{(t)}\}$, where $x_i^{(t)}$ is the highest value of an available item, and take one available item of that value.
--   - *The strategy of Lemma D.3* (p. 34), with $x_i^{(t)},y_i^{(t)}$ the largest and second-largest available values and $s_i^{(t)}=v_i(M^{(t)})$: (1) if $x_i^{(t)}\ge\frac{b_i^{(t)}}{B^{(t)}}s_i^{(t)}$, bid $b_i^{(t)}$ and take the most valuable item, then drop out; (2) else if $x_i^{(t)}<\frac{b_i^{(t)}}{2B^{(t)}-b_i^{(t)}}s_i^{(t)}$ and $x_i^{(t)}+y_i^{(t)}\ge\frac{b_i^{(t)}}{B^{(t)}}s_i^{(t)}$, bid $b_i^{(t)}/2$ and take the two most valuable items, then drop out; (3) else bid $\frac{x_i^{(t)}}{s_i^{(t)}}B^{(t)}$ and take the most valuable item. After dropping out the agent bids $0$.
--
--   These are the objects of Lemmas 4.4, 4.6, 4.7, D.3 and Theorem 4.3, through which the paper proves its main allocation theorem.
--
--   **Formalization Note** Agents are `Fin n`, items `Fin m`, both 0-based; a history is a chronological list of rounds. Initial budgets are a free real vector: positivity and $\sum_k b_k=1$ are hypotheses of the theorems, so a suffix of a play is again a play of the game. The winner is required only to be *a* highest bidder, so every tie-break, including against or in favour of agent $i$, is covered; quantifying over all legal plays that $i$ follows is quantifying over all behaviours of the other agents (each play has at most $m$ rounds). A strategy may read the whole history (all past bids); the paper's strategies use only public quantities. The legality clause of a guarantee is essential: without it an illegal strategy would have no consistent play and would guarantee anything. In the named strategies ties among equally valuable items are resolved arbitrarily (the predicates admit every choice), and divisions by $0$ follow Lean's convention $a/0=0$: with $v_i(M)=0$ bid-your-max-value bids $0$; in Lemma D.3, $B^{(t)}=0$ or $s_i^{(t)}=0$ puts the agent in rule 1. Rule 2 is additionally guarded by "at least two items remain": with one item left and $b_i^{(t)}\le B^{(t)}$ (always the case in a play), its first condition fails anyway. "Drop out" is a function of the history: the agent has won an earlier round in which rule 1 or 2 was in force; if she still wins a tie at bid $0$ she takes one available item.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 14 (the Bidding Game), p. 15 (bid-your-max-value strategy), pp. 33–34 (notation and the strategy of Lemma D.3)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace AnyPriceShare.Bidding

/-- One round of the Bidding Game (p. 14): every agent's bid `r_k^(t)`, the winner `w^(t)` and the
set `W^(t)` she takes. -/
structure Round (n m : ℕ) where
  bids : Fin n → ℝ
  winner : Fin n
  taken : Finset (Fin m)

/-- `M^(t)` (p. 14): the items not taken in any round of the history `h` (chronological list). -/
def remaining {n m : ℕ} (h : List (Round n m)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ∀ r ∈ h, j ∉ r.taken)

/-- `b_k^(t)` (p. 14, lines 2, 7–8): the initial budget `b k` minus `|W^(t)| · r_k^(t)` for every
round of `h` won by `k`. -/
def budget {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) (k : Fin n) : ℝ :=
  b k - (h.map (fun r => if r.winner = k then (r.taken.card : ℝ) * r.bids k else 0)).sum

/-- `B^(t) = ∑_k b_k^(t)` (p. 14): the total remaining budget. -/
def totalBudget {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) : ℝ :=
  ∑ k, budget b h k

/-- A legal round after history `h` (p. 14, lines 4–6): every agent bids in `[0, b_k^(t)]`; the
winner is a highest bidder (any tie-break); she takes a non-empty set of available items that she
can afford at her bid. -/
def ValidRound {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) (r : Round n m) : Prop :=
  (∀ k, 0 ≤ r.bids k ∧ r.bids k ≤ budget b h k) ∧
  (∀ k, r.bids k ≤ r.bids r.winner) ∧
  r.taken.Nonempty ∧
  r.taken ⊆ remaining h ∧
  (r.taken.card : ℝ) * r.bids r.winner ≤ budget b h r.winner

/-- A play of the Bidding Game from initial budgets `b`: each round is legal for the history
before it. (Since each round takes a non-empty set of available items, a round only happens
while items remain, as in line 3.) -/
def ValidPlay {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) : Prop :=
  ∀ (k : ℕ) (hk : k < h.length), ValidRound b (h.take k) (h.get ⟨k, hk⟩)

/-- The items won by agent `i` in the play `h`: her bundle once the play is complete. -/
def wonBy {n m : ℕ} (i : Fin n) (h : List (Round n m)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ∃ r ∈ h, r.winner = i ∧ j ∈ r.taken)

/-- A strategy of an agent: as a function of the history so far, a bid and the set she takes if
she wins the round. -/
abbrev Strategy (n m : ℕ) := List (Round n m) → ℝ × Finset (Fin m)

/-- Agent `i` follows the strategy `σ` in the play `h`: in every round her bid is the one `σ`
prescribes, and if she wins she takes the set `σ` prescribes. -/
def FollowedBy {n m : ℕ} (σ : Strategy n m) (i : Fin n) (h : List (Round n m)) : Prop :=
  ∀ (k : ℕ) (hk : k < h.length),
    (h.get ⟨k, hk⟩).bids i = (σ (h.take k)).1 ∧
    ((h.get ⟨k, hk⟩).winner = i → (h.get ⟨k, hk⟩).taken = (σ (h.take k)).2)

/-- A move (bid, set) of agent `i` after history `h` is legal (p. 14, lines 4 and 6): the bid lies
in `[0, b_i^(t)]` and the set is a non-empty set of available items affordable at that bid. -/
def LegalMove {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) (i : Fin n)
    (mv : ℝ × Finset (Fin m)) : Prop :=
  0 ≤ mv.1 ∧ mv.1 ≤ budget b h i ∧ mv.2.Nonempty ∧ mv.2 ⊆ remaining h ∧
    (mv.2.card : ℝ) * mv.1 ≤ budget b h i

/-- The strategy `σ` of agent `i` guarantees her the value `x` (under the additive valuation with
item values `u`) in the Bidding Game with initial budgets `b`, regardless of the strategies of the
other agents: (1) at every reachable history with items left, `σ` prescribes a legal move; (2) in
every complete play in which `i` follows `σ` — whatever the other agents bid, whoever wins ties,
and whatever the other winners take — `i` ends with value at least `x`. -/
def Guarantees {n m : ℕ} (b : Fin n → ℝ) (σ : Strategy n m) (i : Fin n) (u : Fin m → ℝ)
    (x : ℝ) : Prop :=
  (∀ h, ValidPlay b h → FollowedBy σ i h → remaining h ≠ ∅ → LegalMove b h i (σ h)) ∧
  (∀ h, ValidPlay b h → FollowedBy σ i h → remaining h = ∅ → x ≤ addVal u (wonBy i h))

/-- The bid-your-max-value strategy (p. 15): at every history with items left, agent `i` bids
`min { x_i^(t) / v_i(M), b_i^(t) }`, where `x_i^(t)` is the highest value of a remaining item, and
takes one remaining item of value `x_i^(t)` (any one, if several). -/
def IsBidYourMaxValue {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (σ : Strategy n m) : Prop :=
  ∀ h, remaining h ≠ ∅ → ∃ j ∈ remaining h, (∀ j' ∈ remaining h, u j' ≤ u j) ∧
    σ h = (min (u j / addVal u Finset.univ) (budget b h i), {j})

/-- The rule of the strategy of Lemma D.3 (p. 34) that is in force after history `h`, ignoring
drop-out: `1` if `x ≥ (b^(t)/B^(t)) · s`; else `2` if at least two items remain,
`x < b^(t)/(2B^(t) − b^(t)) · s` and `x + y ≥ (b^(t)/B^(t)) · s`; else `3`. Here `x`, `y` are the
largest and second-largest remaining values, `s = v_i(M^(t))`, `b^(t)` is `i`'s budget and `B^(t)`
the total budget. -/
noncomputable def lemmaD3Rule {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (h : List (Round n m)) : ℕ :=
  let R := remaining h
  let s := addVal u R
  let x := rankedValue u R 1
  let y := rankedValue u R 2
  let bt := budget b h i
  let B := totalBudget b h
  if bt / B * s ≤ x then 1
  else if 2 ≤ R.card ∧ x < bt / (2 * B - bt) * s ∧ bt / B * s ≤ x + y then 2
  else 3

/-- Agent `i` has dropped out after history `h` (Lemma D.3, rules 1–2): she won some earlier round
in which rule 1 or rule 2 was in force. -/
def lemmaD3DroppedOut {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (h : List (Round n m)) : Prop :=
  ∃ (k : ℕ) (hk : k < h.length), (h.get ⟨k, hk⟩).winner = i ∧ lemmaD3Rule u b i (h.take k) ≤ 2

/-- The strategy of Lemma D.3 (p. 34). At every history with items left (`x`, `y`, `s`, `b^(t)`,
`B^(t)` as in `lemmaD3Rule`):
after dropping out, bid `0` (and take one remaining item if still winning a tie);
rule 1: bid `b^(t)` and take a most valuable remaining item ("item 1");
rule 2: bid `b^(t)/2` and take two distinct remaining items of values `x` and `y`
("items 1 and 2");
rule 3: bid `(x / s) · B^(t)` and take a most valuable remaining item. -/
def IsLemmaD3Strategy {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (σ : Strategy n m) : Prop :=
  ∀ h, remaining h ≠ ∅ →
    let R := remaining h
    let s := addVal u R
    let x := rankedValue u R 1
    let y := rankedValue u R 2
    let bt := budget b h i
    let B := totalBudget b h
    (lemmaD3DroppedOut u b i h → (σ h).1 = 0 ∧ ∃ j ∈ R, (σ h).2 = {j}) ∧
    (¬ lemmaD3DroppedOut u b i h → lemmaD3Rule u b i h = 1 →
      ∃ j ∈ R, u j = x ∧ σ h = (bt, {j})) ∧
    (¬ lemmaD3DroppedOut u b i h → lemmaD3Rule u b i h = 2 →
      ∃ j₁ ∈ R, ∃ j₂ ∈ R, j₁ ≠ j₂ ∧ u j₁ = x ∧ u j₂ = y ∧ σ h = (bt / 2, {j₁, j₂})) ∧
    (¬ lemmaD3DroppedOut u b i h → lemmaD3Rule u b i h = 3 →
      ∃ j ∈ R, u j = x ∧ σ h = (x / s * B, {j}))

end AnyPriceShare.Bidding


