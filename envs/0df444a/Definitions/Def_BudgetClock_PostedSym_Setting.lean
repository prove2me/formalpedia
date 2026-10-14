-- Prove2me | Definitions.Def_BudgetClock_PostedSym_Setting
-- name    : BudgetClock_PostedSym_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:23:49.095715+00:00
-- url     : https://prove2.me/theorems/d45e1c9f-8844-41e8-a4b9-36a478352e5d
-- title:
--   §B.2, p. 25 and Mechanism 5, p. 27 — symmetric submodular valuations and the posted-price Mechanism 5
-- statement:
--   This file fixes the model of Appendix B.2 of Balkanski et al. A set $N = \{0, 1, \dots, n-1\}$ of $n$ bidders sells services to an auctioneer with budget $B$; bidder $i$ has a private cost $c_i \ge 0$ and accepts an offered price $p$ exactly when $c_i \le p$.
--
--   1. **Symmetric submodular valuations** (p. 25). A valuation $v : 2^N \to \mathbb{R}_{\ge 0}$ is *symmetric submodular* if there are numbers $r_1 \ge r_2 \ge \cdots \ge r_n \ge 0$ such that
--   $$v(S) = \sum_{i=1}^{|S|} r_i \qquad \text{for all } S \subseteq N.$$
--   The value of a set depends only on its size, with diminishing marginal returns.
--
--   2. **Mechanism 5** (p. 27). Fix a bidder $j$ to be set aside. Starting from a counter $a = 0$ and the empty winning set $W$, the mechanism scans the other bidders once each. To the current bidder $i$ it offers
--   $$p_i = \begin{cases} \dfrac{B}{2\ln n} & a = 0,\\[2mm] \dfrac{B}{a \cdot 2\ln n} & a \ge 1;\end{cases}$$
--   if $i$ accepts, then $a$ increases by one and $i$ joins $W$. After the scan, if nobody accepted ($a = 0$), the set-aside bidder $j$ is offered the whole budget $B$ and joins $W$ if it accepts. The mechanism returns $W$, and each winner is paid the price it accepted. The mechanism never looks at the valuation.
--
--   These are the objects of Theorem 15, which bounds the value of $W$ against the best budget-feasible set.
--
--   **Formalization Note.** Bidders are `Fin n`; the scan visits $[n]\setminus\{j\}$ in increasing index order, and the paper's "arbitrarily ordered" bidders and "arbitrary agent $j$" are covered by stating every theorem for all cost vectors and all $j$. The sequence $r$ is indexed from $0$ ($r_0$ is the paper's $r_1$). `mech5` returns the winning set together with the price offered to each bidder ($0$ for a bidder never offered anything); `scan` is the for-loop of lines 1–11, exposing the counter $a$. The printed pseudocode offers $B$ to $j$ on line 13 but never adds $j$ to $W$; the proof of Theorem 15 (Case 1, p. 28) says the mechanism "would return the agent $j$", and this definition follows the proof. The input line of Mechanism 5 says "additive valuation"; the mechanism does not use the valuation, and the theorems take it symmetric submodular as Theorem 15 does.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 25, §B.2 (definition of symmetric submodular); p. 27, Mechanism 5; p. 5, §2 Preliminaries

import Mathlib

namespace BudgetClock.PostedSym

/-- §B.2, p. 25: a valuation `v : 2^N → ℝ≥0` on the bidders `N = Fin n` is *symmetric submodular*
if there exist `r₁ ≥ r₂ ≥ ⋯ ≥ rₙ ≥ 0` with `v(S) = ∑_{i=1}^{|S|} rᵢ` for every `S ⊆ N`.
The sequence is indexed from `0`: `r 0` is the paper's `r₁`, `r (n-1)` is `rₙ`; values of `r` at
indices `≥ n` are never used, since `|S| ≤ n`. -/
def IsSymmetricSubmodular (n : ℕ) (v : Finset (Fin n) → ℝ) : Prop :=
  ∃ r : ℕ → ℝ,
    (∀ k, k < n → 0 ≤ r k) ∧
    (∀ k l, k ≤ l → l < n → r l ≤ r k) ∧
    ∀ S : Finset (Fin n), v S = ∑ k ∈ Finset.range S.card, r k

/-- The price Mechanism 5 offers while its acceptance counter is `a`
(lines 5–8, p. 27): `B / (2 ln n)` if `a = 0`, and `B / (a · 2 ln n)` otherwise. -/
noncomputable def offerPrice (n : ℕ) (B : ℝ) (a : ℕ) : ℝ :=
  if a = 0 then B / (2 * Real.log n) else B / ((a : ℝ) * 2 * Real.log n)

/-- State of the scan of Mechanism 5 (lines 1–11): the counter `a` of accepted offers, the winning
set `W`, and the price offered to each bidder so far (`0` for a bidder not yet offered anything). -/
structure ScanState (n : ℕ) where
  count : ℕ
  winners : Finset (Fin n)
  price : Fin n → ℝ

/-- One iteration of the for-loop of Mechanism 5 (lines 5–11) on bidder `i`: offer
`offerPrice n B a` to `i`; bidder `i` accepts iff `c i ≤` the offered price, in which case `a`
is incremented and `i` joins `W`. -/
noncomputable def step (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (s : ScanState n) (i : Fin n) :
    ScanState n :=
  if c i ≤ offerPrice n B s.count then
    { count := s.count + 1
      winners := insert i s.winners
      price := Function.update s.price i (offerPrice n B s.count) }
  else
    { count := s.count
      winners := s.winners
      price := Function.update s.price i (offerPrice n B s.count) }

/-- The for-loop of Mechanism 5 (lines 1–11): starting from `a = 0`, `W = ∅`, scan the bidders of
`[n] \ {j}` once each, in increasing index order. -/
noncomputable def scan (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (j : Fin n) : ScanState n :=
  ((List.finRange n).filter (fun i => i ≠ j)).foldl (step n B c)
    { count := 0, winners := ∅, price := fun _ => 0 }

/-- Mechanism 5, p. 27: a posted-price mechanism for symmetric submodular valuations, run on
budget `B`, costs `c`, and the set-aside bidder `j`. Returns the winning set `W` and the price
offered to each bidder (`0` for a bidder never offered anything); each winner is paid its offered
price. After the scan, if no bidder accepted (`a = 0`), the set-aside bidder `j` is offered `B`
(line 13) and **joins `W` if it accepts** (`c j ≤ B`). The printed pseudocode omits
`W ← W ∪ {j}` after line 13, but the proof of Theorem 15 (Case 1, p. 28) says the mechanism
"would return the agent j"; this definition follows the proof. The valuation is never read. -/
noncomputable def mech5 (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (j : Fin n) :
    Finset (Fin n) × (Fin n → ℝ) :=
  let s := scan n B c j
  if s.count = 0 then
    (if c j ≤ B then insert j s.winners else s.winners, Function.update s.price j B)
  else
    (s.winners, s.price)

end BudgetClock.PostedSym


