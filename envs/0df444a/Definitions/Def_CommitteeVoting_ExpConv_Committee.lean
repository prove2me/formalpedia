-- Prove2me | Definitions.Def_CommitteeVoting_ExpConv_Committee
-- name    : CommitteeVoting_ExpConv_Committee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:39.569376+00:00
-- url     : https://prove2.me/theorems/1a87a4fd-e03d-4e87-8112-970fe555a3a3
-- title:
--   Definitions 1 and 3, pp. 8–11 — approval scores, admissible k-committees and the honest-committee event 𝕋 = H
-- statement:
--   This file fixes the deterministic part of $k$-winner approval voting and of the honest-committee event.
--
--   There are $n$ voters $v_1,\dots,v_n$ and $m$ candidates (block producers) $c_1,\dots,c_m$. A **ballot profile** records, for every voter $i$ and candidate $j$, whether voter $i$ approves candidate $j$; equivalently, voter $i$ casts an approval set $\mathcal C_{v_i}\subseteq\mathcal C$.
--
--   1. **Score.** The score of candidate $j$ is the number of voters who approve it:
--   $$\operatorname{score}(j)=\bigl|\{\,i : j\in\mathcal C_{v_i}\,\}\bigr|.$$
--
--   2. **Admissible committee.** Given scores $s$, a set $T$ of candidates is an *admissible committee of size $k$* if
--   $$|T|=k\quad\text{and}\quad s(b)\le s(a)\ \text{ for all } a\in T,\ b\notin T.$$
--   These are exactly the outcomes of "elect the $k$ highest scores" when ties at the lowest elected score are broken arbitrarily and, if fewer than $k$ candidates have a non-zero score, the committee is filled arbitrarily with zero-score candidates.
--
--   3. **Honest outcome.** Given a tolerance $p$ and a set $\mathrm{Hon}$ of honest candidates, the scores $s$ produce an *honest committee*, $\mathbb T=H$, if **every** admissible committee $T$ contains at least $\lceil(1-p)\,k\rceil$ honest members:
--   $$\forall T \text{ admissible}:\qquad |T\cap \mathrm{Hon}|\ \ge\ \lceil (1-p)\,k\rceil .$$
--
--   The universal quantifier over admissible committees encodes the paper's adversarial resolution of ties and of under-filled committees: the committee counts as honest only if no adversarial choice among the admissible committees can make it dishonest. Every statement of the mission about $\Pr[\mathbb T=H]$ refers to this predicate.
--
--   **Formalization Note** Voters are indexed by $\{0,\dots,n-1\}$ and candidates by $\{0,\dots,m-1\}$ (the paper's $v_i$ and $c_j$ are indices $i-1$ and $j-1$). A ballot profile is a Boolean matrix `C : Fin n → Fin m → Bool`. The threshold is the integer ceiling `⌈(1 - p) * k⌉ : ℤ`, compared with the cast cardinality. The cap $|\mathcal C_v|\le t$ of Definition 2 is not built in: it restricts which profiles occur, and no result of this mission uses it.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 8, Definition 1, eq. (1); p. 9, Definition 2 and the standing assumption m ≥ k; pp. 10–11, Definition 3

import Mathlib

namespace CommitteeVoting.ExpConv

/-- Approval score (Definition 1, eq. (1)): for a ballot profile `C`, where `C i j = true`
means that voter `i` approves candidate `j`, the score of `j` is the number of voters
approving `j`. Voters are `Fin n`, candidates `Fin m` (0-based). -/
def score {n m : ℕ} (C : Fin n → Fin m → Bool) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun i => C i j = true).card

/-- Admissible committees (Definition 3): a set `T` of exactly `k` candidates such that every
candidate outside `T` scores at most as much as every member of `T`. Every way of breaking ties
at the lowest elected score, and every way of filling the committee with zero-score candidates,
is admissible. -/
def Admissible {m : ℕ} (k : ℕ) (s : Fin m → ℕ) (T : Finset (Fin m)) : Prop :=
  T.card = k ∧ ∀ a ∈ T, ∀ b ∉ T, s b ≤ s a

/-- The event `𝕋 = H` of Definition 3 with adversarial tie-breaking and filling: every admissible
committee for the scores `s` has at least `⌈(1 - p) k⌉` members in the honest set `Hon`. -/
def IsHonestOutcome {m : ℕ} (k : ℕ) (p : ℝ) (Hon : Finset (Fin m)) (s : Fin m → ℕ) : Prop :=
  ∀ T : Finset (Fin m), Admissible k s T → ⌈(1 - p) * (k : ℝ)⌉ ≤ ((T ∩ Hon).card : ℤ)

end CommitteeVoting.ExpConv


