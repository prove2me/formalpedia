-- Prove2me | Definitions.Def_PrizeAlloc_Interval_Companions
-- name    : PrizeAlloc_Interval_Companions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:35.134143+00:00
-- url     : https://prove2.me/theorems/3854b7b5-ebb9-45db-a442-23b3359dc7af
-- title:
--   pp. 9, 13–15 — ED, WTA and WTS rules; strict and winner-loser strict order preservation; strict and winner strict endowment monotonicity; endowment additivity; scale invariance
-- statement:
--   This file adds the rules and the strengthened axioms of §2.3 to the model of the Setting file.
--
--   **Rules.** For a competition $(N, \mathcal R, E)$ and $i \in N$:
--
--   1. The *Equal Division* rule: $\mathrm{ED}_i(N, \mathcal R, E) = E / |N|$.
--   2. The *Winner-Takes-All* rule: $\mathrm{WTA}_i(N, \mathcal R, E) = E$ if $\mathcal R(i) = 1$, and $0$ otherwise.
--   3. A *Winner-Takes-Surplus* rule with parameter $a \in \mathbb R_+ \cup \{+\infty\}$:
--   $$\varphi_i(N, \mathcal R, E) = \begin{cases} E - (|N| - 1) a & \text{if } E \ge |N| a \text{ and } \mathcal R(i) = 1; \\ a & \text{if } E \ge |N| a \text{ and } \mathcal R(i) \ne 1; \\ E / |N| & \text{otherwise.} \end{cases}$$
--
--   Two rules *coincide* if they assign the same prize to every competitor in every competition.
--
--   **Axioms.** For every competition $(N, \mathcal R, E)$ and $i, j \in N$:
--
--   1. *Strict order preservation*: if $E > 0$ and $\mathcal R(i) < \mathcal R(j)$, then $\varphi_i > \varphi_j$.
--   2. *Winner-loser strict order preservation*: if $E > 0$ and $\mathcal R(i) < \mathcal R(j)$, then $\varphi_i \ge \varphi_j$, and if moreover $\mathcal R(i) = 1$ and $\mathcal R(j) = |N|$, then $\varphi_i > \varphi_j$.
--   3. *Strict endowment monotonicity*: if $E < E'$, then $\varphi_i(N, \mathcal R, E) < \varphi_i(N, \mathcal R, E')$.
--   4. *Winner strict endowment monotonicity*: endowment monotonicity, and if $E < E'$ and $\mathcal R(i) = 1$, then $\varphi_i(N, \mathcal R, E) < \varphi_i(N, \mathcal R, E')$.
--   5. *Endowment additivity*: $\varphi_i(N, \mathcal R, E + E') = \varphi_i(N, \mathcal R, E) + \varphi_i(N, \mathcal R, E')$ for $E, E' \ge 0$.
--   6. *Scale invariance*: $\varphi_i(N, \mathcal R, E) = E\, \varphi_i(N, \mathcal R, 1)$.
--
--   These are the objects of Lemma 4 and Corollaries 1–4.
--
--   **Formalization Note** Same encoding of competitions as the Setting file (rankings as duplicate-free nonempty lists, best first). The WTS parameter $a$ is an extended real with $a \ge 0$; for $a = +\infty$ the condition $E \ge |N| a$ never holds and the rule is ED. "Coincide" quantifies over rankings, $E \ge 0$ and competitors only. Winner-loser strict order preservation requires $\mathcal R(i) < \mathcal R(j)$ for its strict clause as well, which is how the page's sentence reads (the strict clause is part of the same "if $i$ has a higher position than $j$").
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 9 (ED, WTA), p. 13 (strict and winner-loser strict order preservation), p. 14 (strict and winner strict endowment monotonicity, Winner-Takes-Surplus rules), p. 15 (endowment additivity, scale invariance)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

variable {U : Type*} [DecidableEq U]

/-- The Equal Division rule (p. 9): `ED_i(N, R, E) = E / |N|`. -/
noncomputable def ED (l : List U) (E : ℝ) (_i : U) : ℝ := E / l.length

/-- The Winner-Takes-All rule (p. 9): `WTA_i(N, R, E) = E` if `R(i) = 1`, and `0` otherwise. -/
def WTA (l : List U) (E : ℝ) (i : U) : ℝ := if pos l i = 1 then E else 0

/-- Two rules coincide on every competition: same prize for every ranking, every `E ≥ 0` and
every competitor. -/
def Coincide (φ ψ : List U → ℝ → U → ℝ) : Prop :=
  ∀ (l : List U) (E : ℝ), IsRanking l → 0 ≤ E → ∀ i ∈ l, φ l E i = ψ l E i

/-- Strict order preservation (p. 13). -/
def StrictOrderPreserving (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ (l : List U) (E : ℝ), IsRanking l → 0 < E →
    ∀ i ∈ l, ∀ j ∈ l, pos l i < pos l j → φ l E j < φ l E i

/-- Winner-loser strict order preservation (p. 13). -/
def WinnerLoserStrictOrderPreserving (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ (l : List U) (E : ℝ), IsRanking l → 0 < E →
    ∀ i ∈ l, ∀ j ∈ l, pos l i < pos l j →
      φ l E j ≤ φ l E i ∧ (pos l i = 1 → pos l j = l.length → φ l E j < φ l E i)

/-- Strict endowment monotonicity (p. 14). -/
def StrictEndowmentMonotone (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ (l : List U) (E E' : ℝ), IsRanking l → 0 ≤ E → E < E' → ∀ i ∈ l, φ l E i < φ l E' i

/-- Winner strict endowment monotonicity (p. 14). -/
def WinnerStrictMonotone (φ : List U → ℝ → U → ℝ) : Prop :=
  EndowmentMonotone φ ∧
    ∀ (l : List U) (E E' : ℝ), IsRanking l → 0 ≤ E → E < E' →
      ∀ i ∈ l, pos l i = 1 → φ l E i < φ l E' i

/-- Endowment additivity (p. 15). -/
def EndowmentAdditive (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ (l : List U) (E E' : ℝ), IsRanking l → 0 ≤ E → 0 ≤ E' →
    ∀ i ∈ l, φ l (E + E') i = φ l E i + φ l E' i

/-- Scale invariance (p. 15). -/
def ScaleInvariant (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ (l : List U) (E : ℝ), IsRanking l → 0 ≤ E → ∀ i ∈ l, φ l E i = E * φ l 1 i

/-- Winner-Takes-Surplus rules (p. 14): there is `a ∈ ℝ₊ ∪ {+∞}` (in `EReal`) such that the winner
gets `E − (|N| − 1) a` and every other competitor `a` when `E ≥ |N| a`, and `E / |N|` otherwise.
For `a = +∞` the first two cases never apply. -/
def IsWTSRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∃ a : EReal, 0 ≤ a ∧
    ∀ (l : List U) (E : ℝ), IsRanking l → 0 ≤ E → ∀ i ∈ l,
      (((l.length : ℕ) : EReal) * a ≤ E → pos l i = 1 →
        (φ l E i : EReal) = (E : EReal) - ((l.length - 1 : ℕ) : EReal) * a) ∧
      (((l.length : ℕ) : EReal) * a ≤ E → pos l i ≠ 1 → (φ l E i : EReal) = a) ∧
      (¬ ((l.length : ℕ) : EReal) * a ≤ E → φ l E i = E / l.length)

end PrizeAlloc.Interval


