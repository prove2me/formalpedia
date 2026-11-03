-- Prove2me | Definitions.Def_MobilePromo_Policy
-- name    : MobilePromo_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:39.846522+00:00
-- url     : https://prove2.me/theorems/4362b006-5e72-4ade-acb9-90e22739ebc3
-- title:
--   Bid rules, histories and the class of admissible rules
-- statement:
--   A **history** is the list of the outcomes of all past periods. It determines the next period $(i,t)$, the part $\hat x$ of the history inside season $i$, the state $\boldsymbol c_i(\hat x)$, and whether some campaign is active.
--
--   A deterministic non-anticipating **bid rule** $\pi$ gives, for each history and location $l$, the bid $b^\pi$ for an impression arriving from $l$. The allocation is FEFS. A rule is **admissible** if it places no bid (bid $0$) when no campaign is active, and otherwise places either no bid or a bid in $B$.
--
--   **Formalization Note** The bid rule reads the history $x$ of (2), the campaign data being the fixed schedule. A policy of the paper with FEFS allocation is exactly such a rule; a period's no-bid is the value $0$, which is not in $B$.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, pp.8–9; p.15; (2), p.9

import Mathlib
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- The season of the next period, after the history `h` (0-based; `h` lists all past outcomes in
order). -/
def seasonIdx {α : Type*} (T : ℕ) (h : List α) : ℕ := h.length / T

/-- The next period within its season, in `1, …, T`, after the history `h`. -/
def periodIdx {α : Type*} (T : ℕ) (h : List α) : ℕ := h.length % T + 1

/-- The part `x̂` of the history `h` inside the current season (SSRN 3523491, p.15). -/
def seasonHist {α : Type*} (T : ℕ) (h : List α) : List α := h.drop (seasonIdx T h * T)

/-- The state `c_i(x̂)` at the next period after the history `h` (SSRN 3523491, p.15). -/
def curState {T L : ℕ} (S : Schedule T) (h : List (Outcome L)) :
    Fin (S (seasonIdx T h)).m → ℕ :=
  (S (seasonIdx T h)).state (seasonHist T h)

/-- Whether some campaign is active in the next period after the history `h` (`F ≠ ∅`). -/
def activeB {T L : ℕ} (S : Schedule T) (h : List (Outcome L)) : Bool :=
  decide ((S (seasonIdx T h)).activeSet (periodIdx T h) (curState S h)).Nonempty

/-- `b*_{i,t,l}(c_i(x̂); γ)` at the next period after the history `h`. -/
noncomputable def bStarAt (M : Model) {T : ℕ} (S : Schedule T) (γ : M.ParamVec)
    (h : List (Outcome M.L)) (l : Fin M.L) : ℝ :=
  bStar M (S (seasonIdx T h)) γ (periodIdx T h) (curState S h) l

/-- A deterministic non-anticipating bid rule (SSRN 3523491, p.9): the bid `π h l` for an impression
from `l`, given the history `h` of arrivals and win outcomes.

**Formalization Note** Bids are computed from the history `x` of (2), the campaign data being the fixed
schedule, as on p.9. The allocation is not part of the rule: it is FEFS (p.11). -/
abbrev Policy (L : ℕ) := List (Outcome L) → Fin L → ℝ

/-- The class of bid rules of Lemma 2 (SSRN 3523491, pp.8, 15): no bid (bid `0`) when no campaign is
active, and otherwise either no bid or a bid in `B`. -/
def IsAdmissible (M : Model) {T : ℕ} (S : Schedule T) (π : Policy M.L) : Prop :=
  ∀ h l, (activeB S h = false → π h l = 0) ∧ (π h l = 0 ∨ π h l ∈ M.B)

end MobilePromo


