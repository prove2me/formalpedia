-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_Production
-- name    : SRAudit_TwoPhase_Supplement_Production
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:22:14.367722+00:00
-- url     : https://prove2.me/theorems/d643818b-017c-4b2a-b2f6-0f76e085effc
-- title:
--   §3.3 (6)–(13), p. 14, Table 1 variables, (C.21)–(C.25) — the three-stage Cournot production game, its equilibrium, the buyer's production profit and the closed-form functions
-- statement:
--   The production phase of §3.3 on a supply network $g$, with demand and cost data $\alpha,\beta,v_0,v_1,v_2$ ($v_T=v_0+v_1+v_2$; standing assumptions $\beta>0$, $\alpha\ge v_T$) and tier-2 capacity $M$.
--
--   1. **Buyer's problem $P_0$** (6)–(7): given the input price $p_{(1)}$, choose $q_c\in\mathbb R$ to maximize $\pi_c(q_c)=(\alpha-\beta q_c-v_0-p_{(1)})q_c$. The inverse demand $p^*_{(1)}(q_c)$ faced by tier 1 is the unique price at which $q_c$ is optimal.
--   2. **Tier-1 game $P_1$** (8)–(10): given input prices $p_{(2)i}$, the firms $i\in S(1)$ choose $q_i\in\mathbb R$ with payoffs $\pi_i=(p^*_{(1)}(\sum_{i'\in S(1)}q_{i'})-v_1-p_{(2)i})q_i$. The inverse demand $p^*_{(2)}(q_{(1)})$ faced by tier 2 is the unique price vector at which $q_{(1)}$ is an equilibrium of $P_1$.
--   3. **Tier-2 game $P_2$** (11)–(13): supplier $j$ chooses $s_{j,i}\in[0,M]$ for each tier-1 customer $i$ ($j\in S_i\cup S_{ab}$, $i\in S(1)$); with $q_i=\sum_{j'\in S_i\cup S_{ab}}s_{j',i}$ its payoff is $\pi_j=\sum_i(p^*_{(2)i}(q_{(1)})-v_2)s_{j,i}$.
--   4. **Production phase equilibrium** (p. 14): a tuple $(p^*_{(0)},p^*_{(1)},p^*_{(2)},q^*_c,q^*_{(1)},s^*_{(2)})$ in which $s^*_{(2)}$ is an equilibrium of $P_2$ and $p^*_{(2)}$ the resulting tier-2 prices, $q^*_{(1)}$ an equilibrium of $P_1$ given $p^*_{(2)}$ and $p^*_{(1)}=p^*_{(1)}(\sum_i q^*_i)$, $q^*_c$ optimal in $P_0$ given $p^*_{(1)}$, and $p^*_{(0)}=\alpha-\beta q^*_c$.
--   5. **Production profit** (p. 15, fn. 6): $\pi(g)=\pi^*_c$, the buyer's profit (7) in the equilibrium of $g$; $\pi(g_\emptyset)=0$.
--   6. **Table 1 variables** (p. 15): $q^*_c$, $m^*_c=p^*_{(0)}-p^*_{(1)}-v_0$, $\pi^*_c$, $p^*_{(1)}$, and for $i\in\{a,b\}$: $q^*_i$, $p^*_{(2)i}$, $m^*_i=p^*_{(1)}-p^*_{(2)i}-v_1$, $\pi^*_i=(p^*_{(1)}-v_1-p^*_{(2)i})q^*_i$, $\rho^*_i=q^*_i/q^*_c$.
--   7. **Closed forms** (C.21)–(C.25): $L(x_1,x_2,x_3)=4x_1+4x_2+8x_3+3x_1x_2+4x_1x_3+4x_2x_3+4x_3^2+4$ and
--   $$s_e=\tfrac12\tfrac{\alpha-v_T}{\beta}\tfrac{x_2+2x_3+2}{L},\quad s_s=\tfrac13\tfrac{\alpha-v_T}{\beta}\tfrac{-x_1+2x_2+2x_3+2}{L},$$
--   $$q_{(1)}=\tfrac16\tfrac{\alpha-v_T}{\beta}\tfrac{4x_3^2+4x_1x_3+4x_2x_3+4x_3+6x_1+3x_1x_2}{L},\quad q=\tfrac13\tfrac{\alpha-v_T}{\beta}\tfrac{3x_1+3x_2+4x_3+4x_1x_3+4x_2x_3+3x_1x_2+4x_3^2}{L}.$$
--
--   **Formalization Note** Strategy profiles are total functions normalised to $0$ off the supply links and at absent firms, so that uniqueness of an equilibrium is meaningful. The two inverse demands are defined from the optimum and the equilibrium (with a junk value $0$ when the price is not unique), not by pasting (C.1) or (C.5); those formulas are Propositions C.1 and C.2. The equilibrium used by $\pi$ and the Table 1 variables is the unique one (a junk default when there is not exactly one); the null network gets $q^*_c=m^*_c=\pi^*_c=0$.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), pp. 12–15, §3.3, (6)–(13), fn. 6; OA-7, (C.21)–(C.25)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

/-- Demand and cost data of the production phase (§3.3): inverse demand `p(0)(qc) = α − β qc` and
unit production costs `v0, v1, v2` of tiers 0, 1, 2. -/
structure Demand where
  α : ℝ
  β : ℝ
  v0 : ℝ
  v1 : ℝ
  v2 : ℝ

/-- `vT = v0 + v1 + v2`. -/
def Demand.vT (E : Demand) : ℝ := E.v0 + E.v1 + E.v2

/-- Standing assumptions of §3.3 (p. 12): `β > 0` and `α ≥ vT`. -/
def Demand.Standing (E : Demand) : Prop := 0 < E.β ∧ E.vT ≤ E.α

/-! ### Third stage: the buyer's problem `P0` -/

/-- The buyer's profit (7) with (6): `πc(qc) = (p(0)(qc) − v0 − p(1)) qc`. -/
def buyerProfit (E : Demand) (p1 qc : ℝ) : ℝ := (E.α - E.β * qc - E.v0 - p1) * qc

/-- `qc` solves `P0` at input price `p(1)` (decision space `Cc = ℝ`). -/
def IsBuyerOptimal (E : Demand) (p1 qc : ℝ) : Prop := ∀ q : ℝ, buyerProfit E p1 q ≤ buyerProfit E p1 qc

open Classical in
/-- The inverse demand `p*(1)(qc)` faced by the tier-1 firms: the unique input price at which `qc`
solves `P0` (junk value `0` if there is not exactly one such price). -/
noncomputable def invDemand1 (E : Demand) (qc : ℝ) : ℝ :=
  if h : ∃! p1 : ℝ, IsBuyerOptimal E p1 qc then h.exists.choose else 0

/-! ### Second stage: the tier-1 game `P1` -/

variable {ι : Type} [DecidableEq ι]

/-- Tier-1 firm `i`'s payoff (10) given input prices `p(2)` and the profile `q(1)` (indexed by `Firm`,
only the firms of `S(1)` play): `πi(q(1)) = (p*(1)(∑_{i'∈S(1)} q_{i'}) − v1 − p(2)i) qi`. -/
noncomputable def tier1Payoff (E : Demand) (g : Network ι) (p2 q : Firm → ℝ) (i : Firm) : ℝ :=
  (invDemand1 E (∑ i' ∈ g.T1, q i') - E.v1 - p2 i) * q i

/-- `q` is a pure-strategy equilibrium of `P1` (strategy spaces `Ci = ℝ`) given `p(2)`; the profile is
normalised to `0` at absent firms. -/
def IsTier1Eq (E : Demand) (g : Network ι) (p2 q : Firm → ℝ) : Prop :=
  (∀ x, x ∉ g.T1 → q x = 0) ∧
  ∀ i ∈ g.T1, ∀ y : ℝ, tier1Payoff E g p2 (Function.update q i y) i ≤ tier1Payoff E g p2 q i

open Classical in
/-- The inverse demand `p*(2)(q(1))` faced by the tier-2 suppliers: the unique input-price vector
(normalised to `0` at absent firms) at which `q(1)` is an equilibrium of `P1` (junk `0` otherwise). -/
noncomputable def invDemand2 (E : Demand) (g : Network ι) (q : Firm → ℝ) : Firm → ℝ :=
  if h : ∃! p2 : Firm → ℝ, (∀ x, x ∉ g.T1 → p2 x = 0) ∧ IsTier1Eq E g p2 q then h.exists.choose
  else 0

/-! ### First stage: the tier-2 game `P2` -/

/-- Market clearing (13): `qi = ∑_{j' ∈ Si ∪ Sab} s_{j',i}` for `i ∈ S(1)` (and `0` at absent firms).
A tier-2 profile `s j i` is the quantity supplier `j` sells to tier-1 firm `i`. -/
def tier1Qty (g : Network ι) (s : ι → Firm → ℝ) : Firm → ℝ :=
  fun i => if i ∈ g.T1 then ∑ j ∈ g.excl i ∪ g.Sab, s j i else 0

/-- Tier-2 supplier `j`'s payoff (11)–(12) after substituting (13):
`πj = ∑_{i ∈ S(1), j ∈ Si ∪ Sab} (p*(2)i(q(1)) − v2) s_{j,i}`. -/
noncomputable def tier2Payoff (E : Demand) (g : Network ι) (s : ι → Firm → ℝ) (j : ι) : ℝ :=
  ∑ i ∈ g.T1.filter (fun i => j ∈ g.excl i ∪ g.Sab),
    (invDemand2 E g (tier1Qty g s) i - E.v2) * s j i

/-- A tier-2 profile lies in `∏ Cj`: `0 ≤ s_{j,i} ≤ M` on every supply link `j → i` and `s_{j,i} = 0`
off the links (normalisation). -/
def Feasible2 (g : Network ι) (M : ℝ) (s : ι → Firm → ℝ) : Prop :=
  ∀ (j : ι) (i : Firm),
    (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab → 0 ≤ s j i ∧ s j i ≤ M) ∧
    (¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → s j i = 0)

/-- `s` is a pure-strategy equilibrium of `P2` with capacity `M`: no tier-2 supplier `j ∈ S(2)` gains by
a feasible unilateral deviation. -/
def IsTier2Eq (E : Demand) (g : Network ι) (M : ℝ) (s : ι → Firm → ℝ) : Prop :=
  Feasible2 g M s ∧
  ∀ j ∈ g.S2, ∀ s' : ι → Firm → ℝ, Feasible2 g M s' → (∀ j', j' ≠ j → s' j' = s j') →
    tier2Payoff E g s' j ≤ tier2Payoff E g s j

/-! ### Production phase equilibrium (p. 14) -/

/-- A tuple of prices and quantities `(p*(0), p*(1), p*(2), q*c, q*(1), s*(2))`. -/
structure ProdOutcome (ι : Type) where
  p0 : ℝ
  p1 : ℝ
  p2 : Firm → ℝ
  qc : ℝ
  q1 : Firm → ℝ
  s2 : ι → Firm → ℝ

instance : Inhabited (ProdOutcome ι) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- The production phase equilibrium of p. 14: `s*(2)` is an equilibrium of `P2` and `p*(2)` the
resulting tier-2 prices; given `p*(2)`, `q*(1)` is an equilibrium of `P1` and `p*(1)` the resulting
tier-1 price; given `p*(1)`, `q*c` solves `P0` and `p*(0)` is the resulting selling price. -/
def IsProdEq (E : Demand) (g : Network ι) (M : ℝ) (e : ProdOutcome ι) : Prop :=
  IsTier2Eq E g M e.s2 ∧
  e.p2 = invDemand2 E g (tier1Qty g e.s2) ∧
  IsTier1Eq E g e.p2 e.q1 ∧
  e.p1 = invDemand1 E (∑ i ∈ g.T1, e.q1 i) ∧
  IsBuyerOptimal E e.p1 e.qc ∧
  e.p0 = E.α - E.β * e.qc

open Classical in
/-- The production phase equilibrium of `g` with capacity `M` (junk `default` unless unique). -/
noncomputable def eqOf (E : Demand) (M : ℝ) (g : Network ι) : ProdOutcome ι :=
  if h : ∃! e : ProdOutcome ι, IsProdEq E g M e then h.exists.choose else default

/-- The Cournot production profit `π(γ) = π*c` (p. 15): the buyer's profit (7) in the equilibrium
of `g`, and `0` at the null network (fn. 6). -/
noncomputable def cournotProfit (E : Demand) (M : ℝ) (g : Network ι) : ℝ :=
  by classical exact
  if g.T1 = ∅ ∨ g.S2 = ∅ then 0 else buyerProfit E (eqOf E M g).p1 (eqOf E M g).qc

/-! ### Equilibrium variables of Table 1 (p. 15) -/

/-- `q*c` (`0` at the null network). -/
noncomputable def qcStar (E : Demand) (M : ℝ) (g : Network ι) : ℝ :=
  by classical exact if g.T1 = ∅ ∨ g.S2 = ∅ then 0 else (eqOf E M g).qc

/-- `m*c = p*(0) − p*(1) − v0` (`0` at the null network). -/
noncomputable def mcStar (E : Demand) (M : ℝ) (g : Network ι) : ℝ :=
  by classical exact
  if g.T1 = ∅ ∨ g.S2 = ∅ then 0 else (eqOf E M g).p0 - (eqOf E M g).p1 - E.v0

/-- `π*c`, the buyer's equilibrium profit. -/
noncomputable def picStar (E : Demand) (M : ℝ) (g : Network ι) : ℝ := cournotProfit E M g

/-- `p*(1)`. -/
noncomputable def p1Star (E : Demand) (M : ℝ) (g : Network ι) : ℝ := (eqOf E M g).p1

/-- `q*i` for tier-1 firm `i`. -/
noncomputable def qStar (E : Demand) (M : ℝ) (g : Network ι) (i : Firm) : ℝ := (eqOf E M g).q1 i

/-- `p*(2)i`. -/
noncomputable def p2Star (E : Demand) (M : ℝ) (g : Network ι) (i : Firm) : ℝ := (eqOf E M g).p2 i

/-- `m*i = p*(1) − p*(2)i − v1`. -/
noncomputable def mStar (E : Demand) (M : ℝ) (g : Network ι) (i : Firm) : ℝ :=
  (eqOf E M g).p1 - (eqOf E M g).p2 i - E.v1

/-- `π*i`, tier-1 firm `i`'s profit (8) in equilibrium: `(p*(1) − v1 − p*(2)i) q*i`. -/
noncomputable def piStar (E : Demand) (M : ℝ) (g : Network ι) (i : Firm) : ℝ :=
  ((eqOf E M g).p1 - E.v1 - (eqOf E M g).p2 i) * (eqOf E M g).q1 i

/-- The market share `ρ*i = q*i / q*c`. -/
noncomputable def rhoStar (E : Demand) (M : ℝ) (g : Network ι) (i : Firm) : ℝ :=
  qStar E M g i / qcStar E M g

/-! ### Closed-form functions (C.21)–(C.25) (OA-7) -/

/-- `L(x1,x2,x3) = 4x1 + 4x2 + 8x3 + 3x1x2 + 4x1x3 + 4x2x3 + 4x3² + 4` (C.21). -/
def Lf (x1 x2 x3 : ℝ) : ℝ :=
  4 * x1 + 4 * x2 + 8 * x3 + 3 * x1 * x2 + 4 * x1 * x3 + 4 * x2 * x3 + 4 * x3 ^ 2 + 4

/-- `se` (C.22). -/
noncomputable def se (E : Demand) (x1 x2 x3 : ℝ) : ℝ :=
  1 / 2 * ((E.α - E.vT) / E.β) * ((x2 + 2 * x3 + 2) / Lf x1 x2 x3)

/-- `ss` (C.23). -/
noncomputable def ss (E : Demand) (x1 x2 x3 : ℝ) : ℝ :=
  1 / 3 * ((E.α - E.vT) / E.β) * ((-x1 + 2 * x2 + 2 * x3 + 2) / Lf x1 x2 x3)

/-- `q(1)` (C.24). -/
noncomputable def q1f (E : Demand) (x1 x2 x3 : ℝ) : ℝ :=
  1 / 6 * ((E.α - E.vT) / E.β) *
    ((4 * x3 ^ 2 + 4 * x1 * x3 + 4 * x2 * x3 + 4 * x3 + 6 * x1 + 3 * x1 * x2) / Lf x1 x2 x3)

/-- `q` (C.25). -/
noncomputable def qf (E : Demand) (x1 x2 x3 : ℝ) : ℝ :=
  1 / 3 * ((E.α - E.vT) / E.β) *
    ((3 * x1 + 3 * x2 + 4 * x3 + 4 * x1 * x3 + 4 * x2 * x3 + 3 * x1 * x2 + 4 * x3 ^ 2) / Lf x1 x2 x3)

end SRAudit.TwoPhase.Supplement


