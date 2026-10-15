-- Prove2me | Definitions.Def_AdDataSharing_Base_Model
-- name    : AdDataSharing_Base_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:24.441983+00:00
-- url     : https://prove2.me/theorems/ad78f11b-148a-40f0-a116-cc37ad51b495
-- title:
--   pp. 4–9 — advertisers, exchanges, payoffs (1)–(4), ADX1 revenue, subgame-perfect pure equilibria, Assumption 1
-- statement:
--   This file sets up the base model of Johnson, Jungbauer and Preuss.
--
--   There are two advertisers $A_1, A_2$ and two ad exchanges, $ADX_1$ and $ADX_2$. A unit mass of consumers has shown purchase intent: a mass $\alpha$ has visited only $A_1$'s website, a mass $\alpha$ only $A_2$'s, and $1-2\alpha$ both. Each ad costs $w$; an advertiser earns the monopoly profit $M$ from a consumer who sees only its ad and the competition profit $C$ from one who sees both ads. $ADX_1$ earns $\varphi w$ per ad it facilitates. If one advertiser shares data with $ADX_1$, a look-alike audience of $\eta_1$ further consumers can be targeted by both advertisers; if both do, $\eta_2$. The **standing assumptions** are
--   $$
--   0<\alpha<\tfrac12,\quad 0<w<C<M<2C,\quad 0<\varphi<1,\quad 0<\eta_1<\eta_2 .
--   $$
--
--   The game has three stages: $ADX_1$ chooses whether to allow cross-targeting (**open**) or not (**closed**); each advertiser chooses one exchange to share data with; then advertisers place ads. An advertiser's **plan** is its exchange together with its **snipe** decision: whether, when $ADX_1$ is open, it is itself on $ADX_2$ and its rival is on $ADX_1$, it cross-targets the rival's visitors on $ADX_1$. Every other stage-3 action is fixed: each advertiser retargets its own visitors, targets the whole look-alike audience, and cross-targets its rival whenever both are on an open $ADX_1$.
--
--   The advertisers' payoffs are:
--   1. open, both on $ADX_1$ (full cross-targeting): $(1+\eta_2)(C-w)$, display (2);
--   2. open, on $ADX_2$ against a rival on $ADX_1$: $\alpha M+(1-\alpha)C-2(1-\alpha)w+\eta_1(C-w)$ when sniping, display (3), and $\alpha M+(1-2\alpha)C-(1-\alpha)w+\eta_1(C-w)$ when not, display (4);
--   3. open, on $ADX_1$ against a rival on $ADX_2$: $(1-\alpha+\eta_1)(C-w)$ if the rival snipes, $\alpha(M-w)+(1-2\alpha)(C-w)+\eta_1(C-w)$ otherwise;
--   4. open, both on $ADX_2$: $\alpha M+(1-2\alpha)C-(1-\alpha)w$;
--   5. closed: $\alpha M+(1-2\alpha)C-(1-\alpha)w+\ell(C-w)$, where $\ell=\eta_2,\eta_1,0$ when two, one, or no advertisers are on $ADX_1$, display (1).
--
--   $ADX_1$'s revenue is $\varphi w$ times the mass of ads placed on it.
--
--   A profile of plans is a **subgame-perfect equilibrium** of stages 2–3, given $ADX_1$'s choice, when (if open) each advertiser's snipe decision is optimal in its subgame for every rival plan, and neither advertiser gains by sharing data with the other exchange. **Assumption 1** removes every such equilibrium that is strictly Pareto dominated, in the advertisers' payoffs, by another equilibrium of the same subgame. An **equilibrium** of the whole game consists of a selected continuation after each of $ADX_1$'s choices and a choice of $ADX_1$ that maximizes its revenue given them.
--
--   Finally, with $\alpha(M-C)$ the gain from keeping monopoly power over one's exclusive visitors,
--   $$
--   \text{(No Leave)}\quad \alpha(M-C)\le\alpha(C-w)+(\eta_2-\eta_1)(C-w),
--   $$
--   $$
--   \text{(No Leave \& Snipe)}\quad \alpha(M-C)\le(1-2\alpha)w+(\eta_2-\eta_1)(C-w),
--   $$
--   and **NoKnifeEdge** says that neither of them holds with equality.
--
--   These objects are the game whose equilibria Proposition 1 describes, and on which Lemmas 1–5 are stated.
--
--   **Formalization Note.** $C>w$ is not stated in §1 but is used throughout. The paper's footnote 3 (p. 5) and §4.2 (p. 21: "We maintain the assumption that it is profitable to target all customers interested in the product category") rely on it, and without it the look-alike consumers are worthless. Reducing stage 3 to one snipe decision follows pp. 7–8: quitting any other targeting activity is strictly unprofitable when $C>w$ and $M>w$. "Strictly Pareto dominated" is read as both advertisers strictly better off. $ADX_1$'s optimality is weak. `NoKnifeEdge` is not in the paper; it is used only as a disclosed hypothesis of the corrected Lemmas 3, 4 and of one half of Proposition 1.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), pp. 4–9 (§1, displays (1)–(4), (No Leave), (No Leave & Snipe), Assumption 1) and Appendix pp. 25–28 (payoffs in the proofs of Lemmas 4–5, ADX1 profits (13)–(15))

import Mathlib

namespace AdDataSharing.Base

/-- The two advertising exchanges: ADX1 (may allow cross-targeting, owns the look-alike audiences)
and ADX2 (never allows cross-targeting). -/
inductive Exchange where
  | adx1 | adx2
  deriving DecidableEq

/-- Parameters of the base model (pp. 4–6): mass `α` of website visitors exclusive to each
advertiser, monopoly profit `M`, competition profit `C`, ad price `w`, ADX1's revenue share `φ`,
look-alike masses `η₁` (one advertiser shares data with ADX1) and `η₂` (both do). -/
structure Params where
  α : ℝ
  M : ℝ
  C : ℝ
  w : ℝ
  φ : ℝ
  η₁ : ℝ
  η₂ : ℝ

/-- Standing assumptions (pp. 4–6): `0 < α < 1/2`, `w > 0`, `C < M`, `2C > M`, `0 < φ < 1`,
`0 < η₁ < η₂`; plus `w < C` (disclosed: used throughout but not stated in §1; footnote 3, p. 5,
"as long as this value still exceeds the cost of an advertisement", and p. 21, "We maintain the
assumption that it is profitable to target all customers interested in the product category"). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α < 1 / 2 ∧ 0 < P.w ∧ P.w < P.C ∧ P.C < P.M ∧ P.M < 2 * P.C ∧
  0 < P.φ ∧ P.φ < 1 ∧ 0 < P.η₁ ∧ P.η₁ < P.η₂

/-- An advertiser's plan for stages 2–3: the exchange it shares data with, and whether it
cross-targets its rival on ADX1 ("snipes") in the one subgame where that is a choice: ADX1 open,
itself on ADX2, the rival on ADX1. In every other subgame its stage-3 actions are fixed by the
strict-dominance arguments of pp. 7–8 (retarget own visitors, target look-alikes, cross-target
when both are on ADX1). -/
structure Plan where
  ex : Exchange
  snipe : Bool
  deriving DecidableEq

/-- Payoff of an advertiser with plan `p` against a rival with plan `r` when ADX1 allows
cross-targeting (§1.2, pp. 7–8, displays (2)–(4); Appendix, pp. 25–26). -/
def payoffOpen (P : Params) (p r : Plan) : ℝ :=
  match p.ex, r.ex with
  -- (2): full cross-targeting
  | .adx1, .adx1 => (1 + P.η₂) * (P.C - P.w)
  | .adx2, .adx1 =>
      -- (3): leave and snipe
      if p.snipe then P.α * P.M + (1 - P.α) * P.C - 2 * (1 - P.α) * P.w + P.η₁ * (P.C - P.w)
      -- (4): leave
      else P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w + P.η₁ * (P.C - P.w)
  | .adx1, .adx2 =>
      -- (Being Sniped), p. 26
      if r.snipe then (1 - P.α + P.η₁) * (P.C - P.w)
      -- the rival leaves without sniping, p. 26
      else P.α * (P.M - P.w) + (1 - 2 * P.α) * (P.C - P.w) + P.η₁ * (P.C - P.w)
  -- both on ADX2, proof of Lemma 4, p. 25
  | .adx2, .adx2 => P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w

/-- Look-alike audience available to each advertiser (p. 6): `η₂` if both share data with ADX1,
`η₁` if exactly one does, none otherwise. -/
def lookAlike (P : Params) (p r : Plan) : ℝ :=
  match p.ex, r.ex with
  | .adx1, .adx1 => P.η₂
  | .adx2, .adx2 => 0
  | _, _ => P.η₁

/-- Payoff when ADX1 does not allow cross-targeting (§1.1, p. 7, display (1) and the deviation
after it). -/
def payoffClosed (P : Params) (p r : Plan) : ℝ :=
  P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w + lookAlike P p r * (P.C - P.w)

/-- Payoff of an advertiser, given ADX1's stage-1 choice `isOpen`. -/
def payoff (P : Params) (isOpen : Bool) (p r : Plan) : ℝ :=
  if isOpen then payoffOpen P p r else payoffClosed P p r

/-- Mass of ads placed on ADX1 (p. 9 and (13)–(15), pp. 27–28; footnote 9: both advertisers buy
their look-alike ads on ADX1). -/
def adsOnADX1 (P : Params) (isOpen : Bool) (p₁ p₂ : Plan) : ℝ :=
  match p₁.ex, p₂.ex with
  | .adx1, .adx1 => if isOpen then 2 * (1 + P.η₂) else 2 * (1 - P.α + P.η₂)
  | .adx2, .adx2 => 0
  | .adx1, .adx2 => (1 - P.α) + 2 * P.η₁ + (if isOpen && p₂.snipe then 1 - P.α else 0)
  | .adx2, .adx1 => (1 - P.α) + 2 * P.η₁ + (if isOpen && p₁.snipe then 1 - P.α else 0)

/-- ADX1's revenue: it earns `φ w` for every ad placed on it (pp. 6 and 9). -/
def revenue (P : Params) (isOpen : Bool) (σ : Plan × Plan) : ℝ :=
  P.φ * P.w * adsOnADX1 P isOpen σ.1 σ.2

/-- Stage 3: the snipe decision of plan `p` is optimal in the subgame where it is a choice
(ADX1 open, `p` on ADX2, the rival on ADX1), for every rival plan, on and off the path. -/
def SnipeOptimal (P : Params) (p : Plan) : Prop :=
  ∀ r : Plan, r.ex = .adx1 →
    payoffOpen P ⟨.adx2, !p.snipe⟩ r ≤ payoffOpen P ⟨.adx2, p.snipe⟩ r

/-- Subgame-perfect pure equilibrium of stages 2–3, given ADX1's stage-1 choice: stage-3
optimality of both snipe decisions (when ADX1 is open), and no profitable stage-2 deviation to
another exchange for either advertiser. -/
def IsSPE (P : Params) (isOpen : Bool) (σ : Plan × Plan) : Prop :=
  (isOpen = true → SnipeOptimal P σ.1 ∧ SnipeOptimal P σ.2) ∧
  (∀ e : Exchange, payoff P isOpen ⟨e, σ.1.snipe⟩ σ.2 ≤ payoff P isOpen σ.1 σ.2) ∧
  (∀ e : Exchange, payoff P isOpen ⟨e, σ.2.snipe⟩ σ.1 ≤ payoff P isOpen σ.2 σ.1)

/-- Assumption 1 (p. 9): `σ'` strictly Pareto-dominates `σ` in the advertisers' payoffs (both
advertisers strictly better off). -/
def ParetoDominates (P : Params) (isOpen : Bool) (σ' σ : Plan × Plan) : Prop :=
  payoff P isOpen σ.1 σ.2 < payoff P isOpen σ'.1 σ'.2 ∧
  payoff P isOpen σ.2 σ.1 < payoff P isOpen σ'.2 σ'.1

/-- An equilibrium of the stage-2–3 subgame that survives Assumption 1: it is not strictly
Pareto-dominated by another equilibrium of the same subgame. -/
def IsSelected (P : Params) (isOpen : Bool) (σ : Plan × Plan) : Prop :=
  IsSPE P isOpen σ ∧ ¬ ∃ σ', IsSPE P isOpen σ' ∧ ParetoDominates P isOpen σ' σ

/-- A strategy profile of the whole game: ADX1's stage-1 choice, and the advertisers'
continuation after each of its two choices. -/
structure Outcome where
  isOpen : Bool
  σOpen : Plan × Plan
  σClosed : Plan × Plan

/-- The continuation actually played. -/
def Outcome.path (x : Outcome) : Plan × Plan := if x.isOpen then x.σOpen else x.σClosed

/-- Equilibrium of the whole game: selected continuations after both stage-1 choices, and ADX1's
stage-1 choice maximizes its revenue given them. -/
def IsEquilibrium (P : Params) (x : Outcome) : Prop :=
  IsSelected P true x.σOpen ∧ IsSelected P false x.σClosed ∧
  revenue P true x.σOpen ≤ revenue P x.isOpen x.path ∧
  revenue P false x.σClosed ≤ revenue P x.isOpen x.path

/-- (No Leave), p. 8. -/
def NoLeave (P : Params) : Prop :=
  P.α * (P.M - P.C) ≤ P.α * (P.C - P.w) + (P.η₂ - P.η₁) * (P.C - P.w)

/-- (No Leave & Snipe), p. 8. -/
def NoLeaveSnipe (P : Params) : Prop :=
  P.α * (P.M - P.C) ≤ (1 - 2 * P.α) * P.w + (P.η₂ - P.η₁) * (P.C - P.w)

/-- Neither (No Leave) nor (No Leave & Snipe) holds with equality. Off this knife edge the best
deviation from full cross-targeting is never exactly break-even. -/
def NoKnifeEdge (P : Params) : Prop :=
  P.α * (P.M - P.C) ≠ P.α * (P.C - P.w) + (P.η₂ - P.η₁) * (P.C - P.w) ∧
  P.α * (P.M - P.C) ≠ (1 - 2 * P.α) * P.w + (P.η₂ - P.η₁) * (P.C - P.w)

end AdDataSharing.Base


