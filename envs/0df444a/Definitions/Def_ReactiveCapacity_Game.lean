-- Prove2me | Definitions.Def_ReactiveCapacity_Game
-- name    : ReactiveCapacity_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:28.313808+00:00
-- url     : https://prove2.me/theorems/71adc969-6fcf-4f39-afb8-09dca752ea72
-- title:
--   The pull-contract game with reactive capacity $\bar Q$, its subgame-perfect equilibria and their outcomes
-- statement:
--   The game of p.13, with reactive capacity $\bar Q$ (the most the supplier can produce and deliver within the season):
--
--   1. The retailer chooses quality $q\ge 0$ and a take-it-or-leave-it wholesale price $w\ge 0$.
--   2. The supplier chooses its pre-season inventory $I\ge 0$, at unit cost $kq^2$.
--   3. The market state $\alpha\in\{\alpha_g,\alpha_b\}$ is drawn ($\alpha_g$ with probability $\rho$) and observed by both firms.
--   4. The retailer orders $Q\ge 0$. If $Q\le I$ it receives $Q$. If $Q>I$, the supplier chooses in-season production $I'\in[0,\bar Q]$, at unit cost $kq^2$, and the retailer receives $R=\min\{I+I',Q\}$.
--   5. The retailer sets the retail price $p\ge 0$ and sells $\min\{D(q,\alpha,p),R\}$.
--
--   In a realized state the retailer earns $p\min\{D(q,\alpha,p),R\}-wR$ and the supplier earns $wR-kq^2(I+I')$ (with $I'=0$ when $Q\le I$); unsold units are worth $0$. Expected payoffs weight the states by $\rho$ and $1-\rho$.
--
--   A pure strategy profile $\sigma$ specifies $(q,w)$ and, as functions of the history, the inventory $I(q,w)$, the order $Q(q,w,I,\alpha)$, the in-season production $I'(q,w,I,\alpha,Q)$ and the price $p(q,w,I,\alpha,Q,I')$. It is a **subgame-perfect equilibrium** when at every feasible history, on or off the path, the mover's choice is feasible and no feasible alternative, followed by play according to $\sigma$, gives the mover a higher payoff: the price maximizes the retailer's state payoff; $I'$ maximizes the supplier's state payoff $w\min\{I+I',Q\}-kq^2(I+I')$; the order maximizes the retailer's state payoff; the inventory maximizes the supplier's expected payoff; and $(q,w)$ maximizes the retailer's expected payoff. The first three conditions alone ("optimal play after the inventory decision") are also named, because the supplier's response is stated under them.
--
--   An **equilibrium outcome** at $\bar Q$ records the on-path $q$, $w$, $I$, and per state the order $Q$, the in-season production $I'$, the units received $R$ and the price $p$, together with the expected profits $\pi_R$ and $\pi_S$. The paper's $q^*,w^*,p^*,\pi_R^*,\pi_S^*$ are the fields of an equilibrium outcome.
--
--   The game is solved by backward induction (p.13); every result of the mission is a statement about these equilibria, never about the paper's tables.
--
--   **Formalization Note** There is no separate accept/reject stage: rejecting the contract is $I=0$ with no in-season production. There is no tie-breaking rule and no $\varepsilon$ (the paper's $w=kq^2+\varepsilon$, OA p.7, fn 3): ties are resolved by the optimality conditions of the earlier stages. The step-one payoff $p\min\{D,\min\{Q,S\}\}-w\min\{Q,S\}$ of the retailer facing an in-season supply $S$ (Online Appendix §I.1) is also defined here.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), §3, "The sequence of decisions in the game", p.13 (PDF 13); payoffs pp.11, 13; backward induction p.13; step one, Online Appendix §I.1, OA pp.1–5 (PDF 46–50)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model

namespace ReactiveCapacity

/-- Units the retailer receives (p.13): with pre-season inventory `I`, order `Q` and in-season
production `I'`, it receives `Q` if `Q ≤ I`, and `min[I + I', Q]` if `Q > I`. -/
noncomputable def received (I Q I' : ℝ) : ℝ := if Q ≤ I then Q else min (I + I') Q

/-- In-season production actually carried out (p.13): none if `Q ≤ I` (the order is served from
inventory), the supplier's choice `I'` if `Q > I`. -/
noncomputable def inSeason (I Q I' : ℝ) : ℝ := if Q ≤ I then 0 else I'

/-- The retailer's payoff in a realized state (pp.11, 13): it receives `R` units, pays `w R`, sets
retail price `p` and sells `min[demand, R]`. Unsold units have salvage value `0` (p.11). -/
noncomputable def Params.retailerState (P : Params) (q w : ℝ) (s : State) (R p : ℝ) : ℝ :=
  p * min (P.demand q (P.alpha s) p) R - w * R

/-- The supplier's payoff in a realized state (pp.11, 13): revenue `w R` from the `R` units
delivered, minus the production cost `k q²` of the pre-season inventory `I` and of the in-season
production `I'`. Excess inventory has salvage value `0` (p.11). -/
noncomputable def Params.supplierState (P : Params) (q w I R I' : ℝ) : ℝ :=
  w * R - P.cost q * (I + I')

/-- The retailer's step-one problem (Online Appendix §I.1, OA pp.1–5): when the supplier can deliver
at most `S` units in the season and fills every order up to `S`, an order `Q` yields `min[Q, S]`
units, and the retailer's payoff from order `Q` and price `p` in a market with high-valuation
fraction `α` is `p · min[demand, min[Q, S]] − w · min[Q, S]`. -/
noncomputable def Params.stepOnePayoff (P : Params) (q w α S Q p : ℝ) : ℝ :=
  p * min (P.demand q α p) (min Q S) - w * min Q S

/-- A pure strategy profile of the game of p.13. A history is
`(q, w)` → `I` → state `α` → `Q` → (if `Q > I`) `I'` → `p`.

1. `q`, `w`: the retailer's quality and take-it-or-leave-it wholesale price;
2. `inv q w`: the supplier's pre-season inventory `I`;
3. `order q w I s`: the retailer's order `Q` once the state `s` is known;
4. `react q w I s Q`: the supplier's in-season production `I'` (used only when `Q > I`);
5. `price q w I s Q I'`: the retailer's retail price, given the realized in-season production
   `I'` (`0` when `Q ≤ I`).

**Formalization Note** Strategies depend on the whole history. There is no separate
accept/reject stage: rejecting the contract is `I = 0` with no in-season production. -/
structure Profile where
  q : ℝ
  w : ℝ
  inv : ℝ → ℝ → ℝ
  order : ℝ → ℝ → ℝ → State → ℝ
  react : ℝ → ℝ → ℝ → State → ℝ → ℝ
  price : ℝ → ℝ → ℝ → State → ℝ → ℝ → ℝ

namespace Profile

/-- In-season production realized after order `Q` under `σ`. -/
noncomputable def made (σ : Profile) (q w I : ℝ) (s : State) (Q : ℝ) : ℝ :=
  inSeason I Q (σ.react q w I s Q)

/-- Units received after order `Q` under `σ`. -/
noncomputable def recv (σ : Profile) (q w I : ℝ) (s : State) (Q : ℝ) : ℝ :=
  received I Q (σ.react q w I s Q)

/-- Retail price set after order `Q` under `σ`. -/
noncomputable def priceAfter (σ : Profile) (q w I : ℝ) (s : State) (Q : ℝ) : ℝ :=
  σ.price q w I s Q (σ.made q w I s Q)

/-- The retailer's payoff in state `s` from order `Q`, play following `σ` afterwards. -/
noncomputable def orderValue (σ : Profile) (P : Params) (q w I : ℝ) (s : State) (Q : ℝ) : ℝ :=
  P.retailerState q w s (σ.recv q w I s Q) (σ.priceAfter q w I s Q)

/-- The supplier's payoff in state `s` when its inventory is `I`, play following `σ` afterwards. -/
noncomputable def supplierStateValue (σ : Profile) (P : Params) (q w I : ℝ) (s : State) : ℝ :=
  P.supplierState q w I (σ.recv q w I s (σ.order q w I s)) (σ.made q w I s (σ.order q w I s))

/-- The supplier's expected payoff from inventory `I` after contract `(q, w)`, play following `σ`
afterwards: `ρ π_S(α_g) + (1 − ρ) π_S(α_b)`. -/
noncomputable def supplierValue (σ : Profile) (P : Params) (q w I : ℝ) : ℝ :=
  P.prob .good * σ.supplierStateValue P q w I .good +
    P.prob .bad * σ.supplierStateValue P q w I .bad

/-- The retailer's expected payoff from contract `(q, w)`, play following `σ` afterwards. -/
noncomputable def retailerValue (σ : Profile) (P : Params) (q w : ℝ) : ℝ :=
  P.prob .good * σ.orderValue P q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) +
    P.prob .bad * σ.orderValue P q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad)

end Profile

/-- `σ` plays optimally in every subgame that starts after the supplier's pre-season inventory
decision (stages 3–5 of p.13): at every feasible history, on or off the path, the mover's choice is
feasible and no feasible alternative, followed by play according to `σ`, gives the mover a higher
payoff in the realized state.

1. Price: after every feasible history the price `p ≥ 0` maximizes the retailer's state payoff.
2. In-season production: after every order `Q > I`, `I' ∈ [0, Q̄]` maximizes the supplier's state
   payoff `w · min[I + I', Q] − k q² (I + I')`.
3. Order: after every `(q, w, I, s)` the order `Q ≥ 0` maximizes the retailer's state payoff.

Feasible histories have `q ≥ 0`, `w ≥ 0`, `I ≥ 0`, `Q ≥ 0`, `0 ≤ I' ≤ Q̄`. -/
def IsPostInventorySPE (P : Params) (Qbar : ℝ) (σ : Profile) : Prop :=
  -- the retailer's price
  (∀ q w I : ℝ, ∀ s : State, ∀ Q I' : ℝ, 0 ≤ q → 0 ≤ w → 0 ≤ I → 0 ≤ Q → 0 ≤ I' → I' ≤ Qbar →
      0 ≤ σ.price q w I s Q I' ∧
      ∀ p : ℝ, 0 ≤ p →
        P.retailerState q w s (received I Q I') p ≤
          P.retailerState q w s (received I Q I') (σ.price q w I s Q I')) ∧
  -- the supplier's in-season production
  (∀ q w I : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ q → 0 ≤ w → 0 ≤ I → I < Q →
      0 ≤ σ.react q w I s Q ∧ σ.react q w I s Q ≤ Qbar ∧
      ∀ I' : ℝ, 0 ≤ I' → I' ≤ Qbar →
        P.supplierState q w I (received I Q I') I' ≤
          P.supplierState q w I (received I Q (σ.react q w I s Q)) (σ.react q w I s Q)) ∧
  -- the retailer's order
  (∀ q w I : ℝ, ∀ s : State, 0 ≤ q → 0 ≤ w → 0 ≤ I →
      0 ≤ σ.order q w I s ∧
      ∀ Q : ℝ, 0 ≤ Q → σ.orderValue P q w I s Q ≤ σ.orderValue P q w I s (σ.order q w I s))

/-- `σ` is a subgame-perfect equilibrium of the game of p.13 with reactive capacity `Q̄`, the
paper's "backward induction" (p.13): it plays optimally after the inventory decision
(`IsPostInventorySPE`), and in addition

4. Inventory: after every contract `(q, w)` with `q, w ≥ 0`, the inventory `I ≥ 0` maximizes the
   supplier's expected payoff `ρ π_S(α_g) + (1 − ρ) π_S(α_b)`;
5. Contract: `(q, w)` with `q, w ≥ 0` maximizes the retailer's expected payoff.

**Formalization Note** No tie-breaking rule is imposed and there is no `ε` (the paper's
`w = kq² + ε`, OA p.7 fn 3): where a mover is indifferent, any optimal choice is allowed, and the
optimality conditions at the earlier stages select among them. In this finite-horizon game the
one-shot-deviation condition at every history is subgame perfection. -/
def IsSPE (P : Params) (Qbar : ℝ) (σ : Profile) : Prop :=
  IsPostInventorySPE P Qbar σ ∧
  -- the supplier's pre-season inventory
  (∀ q w : ℝ, 0 ≤ q → 0 ≤ w →
      0 ≤ σ.inv q w ∧
      ∀ I : ℝ, 0 ≤ I → σ.supplierValue P q w I ≤ σ.supplierValue P q w (σ.inv q w)) ∧
  -- the retailer's quality and wholesale price
  (0 ≤ σ.q ∧ 0 ≤ σ.w ∧
      ∀ q w : ℝ, 0 ≤ q → 0 ≤ w → σ.retailerValue P q w ≤ σ.retailerValue P σ.q σ.w)

/-- The equilibrium outcome: quality `q`, wholesale price `w`, inventory `I`, and per state the
order `Q`, the in-season production `I'`, the units received `R` and the retail price `p`, with the
retailer's and the supplier's expected profits `π_R`, `π_S`. -/
structure Outcome where
  q : ℝ
  w : ℝ
  I : ℝ
  Q : State → ℝ
  I' : State → ℝ
  R : State → ℝ
  p : State → ℝ
  πR : ℝ
  πS : ℝ

/-- The on-path outcome of the profile `σ`. -/
noncomputable def Profile.outcome (σ : Profile) (P : Params) : Outcome where
  q := σ.q
  w := σ.w
  I := σ.inv σ.q σ.w
  Q := fun s => σ.order σ.q σ.w (σ.inv σ.q σ.w) s
  I' := fun s => σ.made σ.q σ.w (σ.inv σ.q σ.w) s (σ.order σ.q σ.w (σ.inv σ.q σ.w) s)
  R := fun s => σ.recv σ.q σ.w (σ.inv σ.q σ.w) s (σ.order σ.q σ.w (σ.inv σ.q σ.w) s)
  p := fun s => σ.priceAfter σ.q σ.w (σ.inv σ.q σ.w) s (σ.order σ.q σ.w (σ.inv σ.q σ.w) s)
  πR := σ.retailerValue P σ.q σ.w
  πS := σ.supplierValue P σ.q σ.w (σ.inv σ.q σ.w)

/-- `e` is an equilibrium outcome of the game with parameters `P` and reactive capacity `Q̄`: the
on-path outcome of some subgame-perfect equilibrium. The paper's `q*`, `w*`, `p*`, `π*_R`, `π*_S`
are the fields of such an `e`. -/
def IsEquilibrium (P : Params) (Qbar : ℝ) (e : Outcome) : Prop :=
  ∃ σ : Profile, IsSPE P Qbar σ ∧ σ.outcome P = e

end ReactiveCapacity


