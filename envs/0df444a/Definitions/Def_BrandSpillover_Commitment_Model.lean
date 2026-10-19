-- Prove2me | Definitions.Def_BrandSpillover_Commitment_Model
-- name    : BrandSpillover_Commitment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:24.423386+00:00
-- url     : https://prove2.me/theorems/99cfe122-455e-4df6-bfcb-6b0dd70e0260
-- title:
--   §3–§4, pp. 7–13, 17, 31 — CM and two Cournot firms with brand power 1 and θ, sourcing structures, brand spillover, the CM's wholesale-price programs
-- statement:
--   A contract manufacturer (CM) supplies two competing firms: Firm S, with a strong brand, and Firm W, with a weak brand. Consumers' perceived brand power is $\theta_S = 1$ for Firm S and $\theta_W = \theta < 1$ for Firm W. Both firms can produce in-house at unit cost $c$; the CM's unit cost is normalized to $0$. The standing assumptions are
--
--   $$c > 0,\qquad \underline\theta = \max\Big\{\tfrac{2+7c}{7},\, \tfrac{1+c}{2}\Big\} \le \theta < 1,\qquad 0 \le \alpha \le 1 .$$
--
--   1. **Sourcing structures.** A structure is one of $(O,O)$, $(O,I)$, $(I,O)$, $(I,I)$; the first letter is Firm S's decision and the second Firm W's, with $O$ = outsource to the CM and $I$ = insource.
--   2. **Brand spillover.** With spillover level $a$ in effect, Firm W's brand power is $\theta + a(1-\theta)$ under $(O,O)$ and $\theta$ under every other structure. Without commitment $a = \alpha$; when Firm W commits to not using brand spillover, $a = 0$.
--   3. **Quantity stage.** Given unit costs $k_S, k_W$ (the wholesale price $w_i$ if Firm $i$ outsources, $c$ if it insources), the firms compete in quantities with prices $p_S = 1 - q_S - q_W$ and $p_W = \theta_W - q_S - q_W$. The quantities are the first-order-condition solutions
--   $$q_S = \tfrac13(2 - \theta_W - 2k_S + k_W),\qquad q_W = \tfrac13(2\theta_W - 1 + k_S - 2k_W),$$
--   and the profits are $\Pi_S = (1 - q_S - q_W - k_S)q_S$, $\Pi_W = (\theta_W - q_S - q_W - k_W)q_W$. The CM earns $w_i q_i$ from each firm that outsources.
--   4. **Price stage.** For each structure the CM chooses wholesale prices $w = (w_S, w_W) \in \mathbb R^2$ subject to the participation constraints of the paper. Under $(O,I)$: $\Pi^{oi}_S(w_S) \ge \Pi^{ii}_S$. Under $(I,O)$: $\Pi^{io}_W(w_W) \ge \Pi^{ii}_W$. Under $(O,O)$: $\Pi^{oi}_S(w_S) \ge \Pi^{ii}_S$, $\Pi^{oo}_S(w_S,w_W) \ge \Pi^{io}_S(w_W)$ and $\Pi^{oo}_W(w_S,w_W) \ge \Pi^{oi}_W(w_S)$. Under $(I,I)$ there is no constraint and the CM earns $0$. Optimal prices maximize the CM's profit over this feasible set.
--   5. **Equilibrium.** An equilibrium outcome is a structure $s$ with optimal prices $w$ whose CM profit is at least the optimal CM profit of every structure; ties between structures are allowed.
--
--   The module also names the thresholds $c^{oi} = \tfrac13(2-\theta)$, $c^{oo}_1 = \tfrac12(2\theta - 1 - 3a(1-\theta))$, $c^{oo}_2 = \tfrac12(1 + a(1-\theta))$ and the quantities $T_1, T_2, T_3$ of Proposition 3, together with the Nash-equilibrium predicate of the quantity game over $\mathbb R$.
--
--   These definitions are the common model for every statement of the mission.
--
--   **Formalization Note** The profit functions use the referenced general Cournot payoff $(A - q - \beta q' - k)q$ with $\beta = 1$. Quantities are the first-order-condition formulas on $\mathbb R$ and are not constrained to be nonnegative, as in the paper, which evaluates every on- and off-path profit with these formulas; at equilibrium prices they are nonnegative under the standing assumptions. Wholesale prices range over all of $\mathbb R$; the paper imposes no sign restriction. A price coordinate for a firm that insources is ignored. In $T_1$ the radicand contains $4a^2(1-\theta)^2$; the page prints $4\alpha^2(1+\theta)^2$, a misprint (setting the CM's profit difference to zero gives $(1-\theta)^2$). `Real.sqrt` returns $0$ on a negative radicand.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), pp. 7–13, 17, 31, §3, §4.1–4.2, §4.4, Appendix A (proof of Lemma 1)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_CournotDuopoly

namespace BrandSpillover.Commitment

noncomputable section

/-- Wu, Zhang & Zhou, *Brand Spillover as a Marketing Strategy*, SSRN preprint 3891915 (June 2021),
p. 8: the four sourcing structures `(O, O)`, `(O, I)`, `(I, O)`, `(I, I)`. The first letter is
Firm S's decision, the second Firm W's; `O` = outsource to the contract manufacturer (CM),
`I` = insource. -/
inductive Structure
  | OO
  | OI
  | IO
  | II
  deriving DecidableEq, Repr

/-- Parameters of the model (pp. 7–9): Firm W's original brand power `θ` (Firm S's is normalized
to `1`), the firms' insourcing unit cost `c` (the CM's unit cost is normalized to `0`), and the
level of brand spillover `α`. -/
structure Params where
  θ : ℝ
  c : ℝ
  α : ℝ

/-- The lower bound `θ̲ = max {(2 + 7c)/7, (1 + c)/2}` on Firm W's brand power (p. 10). -/
def thetaLow (c : ℝ) : ℝ := max ((2 + 7 * c) / 7) ((1 + c) / 2)

/-- Standing assumptions of §3 (pp. 8–10): `c > 0` (the CM, with cost `0`, is more efficient than
the firms), `θ ≥ θ̲` (p. 10), `θ < 1 = θ_S` (p. 8), and `α ∈ [0, 1]` (p. 9). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.c ∧ thetaLow P.c ≤ P.θ ∧ P.θ < 1 ∧ 0 ≤ P.α ∧ P.α ≤ 1

/-- Firm S outsources under `(O, O)` and `(O, I)`. -/
def Structure.sOut : Structure → Bool
  | .OO => true
  | .OI => true
  | .IO => false
  | .II => false

/-- Firm W outsources under `(O, O)` and `(I, O)`. -/
def Structure.wOut : Structure → Bool
  | .OO => true
  | .IO => true
  | .OI => false
  | .II => false

/-- Firm W's brand power when the spillover level in effect is `a` (pp. 8–9): `θ + a(1 − θ)` under
`(O, O)`, and `θ` under every other structure ("When at least one firm insources, brand spillover
cannot happen"). Without commitment `a = α`; with commitment `a = 0` (p. 11). -/
def brandW (θ a : ℝ) (s : Structure) : ℝ := if s = .OO then θ + a * (1 - θ) else θ

/-- Firm S's unit cost: the wholesale price `w.1 = w_S` if it outsources, `c` otherwise. -/
def costS (c : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ := if s.sOut then w.1 else c

/-- Firm W's unit cost: the wholesale price `w.2 = w_W` if it outsources, `c` otherwise. -/
def costW (c : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ := if s.wOut then w.2 else c

/-- Firm S's first-order-condition quantity in the Cournot game with prices `p_S = 1 − q_S − q_W`,
`p_W = θ_W − q_S − q_W` and unit costs `k_S`, `k_W` (pp. 11–12, App. A p. 31). -/
def focQS (θW kS kW : ℝ) : ℝ := (2 - θW - 2 * kS + kW) / 3

/-- Firm W's first-order-condition quantity in the same game. -/
def focQW (θW kS kW : ℝ) : ℝ := (2 * θW - 1 + kS - 2 * kW) / 3

/-- Pure Nash equilibrium `(x, y)` of the stage-4 quantity game on `ℝ`: Firm S (intercept `1`,
cost `kS`) and Firm W (intercept `θW`, cost `kW`) each maximize their profit
`(θ_i − q_S − q_W − k_i) q_i` over all real quantities, given the rival's quantity. -/
def IsQuantityNE (θW kS kW x y : ℝ) : Prop :=
  (∀ x' : ℝ, SupplierAudit.Competition.cournotPayoff 1 1 kS x' y ≤
      SupplierAudit.Competition.cournotPayoff 1 1 kS x y) ∧
  (∀ y' : ℝ, SupplierAudit.Competition.cournotPayoff 1 θW kW y' x ≤
      SupplierAudit.Competition.cournotPayoff 1 θW kW y x)

/-- Firm S's stage-4 quantity under structure `s`, prices `w`, spillover level `a`. -/
def quantS (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ :=
  focQS (brandW P.θ a s) (costS P.c s w) (costW P.c s w)

/-- Firm W's stage-4 quantity under structure `s`, prices `w`, spillover level `a`. -/
def quantW (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ :=
  focQW (brandW P.θ a s) (costS P.c s w) (costW P.c s w)

/-- Firm S's profit `Π_S = (1 − q_S − q_W − k_S) q_S` (p. 10). -/
def profitS (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ :=
  SupplierAudit.Competition.cournotPayoff 1 1 (costS P.c s w) (quantS P a s w) (quantW P a s w)

/-- Firm W's profit `Π_W = (θ_W − q_S − q_W − k_W) q_W` (p. 10). -/
def profitW (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ :=
  SupplierAudit.Competition.cournotPayoff 1 (brandW P.θ a s) (costW P.c s w)
    (quantW P a s w) (quantS P a s w)

/-- The CM's profit (p. 10): `w_i q_i` summed over the firms that outsource. -/
def cmProfit (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : ℝ :=
  (if s.sOut then w.1 * quantS P a s w else 0) + (if s.wOut then w.2 * quantW P a s w else 0)

/-- The participation constraints of the CM's programs: `(O, I)` p. 11, `(O, O)` p. 12,
`(I, O)` App. A p. 31; `(I, I)` has none. Each compares a firm's profit when outsourcing at the
offered prices with its profit when it deviates to insourcing. -/
def Feasible (P : Params) (a : ℝ) : Structure → ℝ × ℝ → Prop
  | .II, _ => True
  | .OI, w => profitS P a .II w ≤ profitS P a .OI w
  | .IO, w => profitW P a .II w ≤ profitW P a .IO w
  | .OO, w => profitS P a .II w ≤ profitS P a .OI w ∧
              profitS P a .IO w ≤ profitS P a .OO w ∧
              profitW P a .OI w ≤ profitW P a .OO w

/-- `w` is an optimal solution of the CM's program for structure `s`. -/
def IsOptPrices (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : Prop :=
  Feasible P a s w ∧ ∀ w' : ℝ × ℝ, Feasible P a s w' → cmProfit P a s w' ≤ cmProfit P a s w

/-- Equilibrium outcome of stages 2–4 (p. 11): `s` is a structure the CM prefers, i.e. its optimal
CM profit is at least the optimal CM profit of every structure, and `w` are optimal prices for
`s`. Ties between structures are allowed. -/
def IsEquilibrium (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) : Prop :=
  IsOptPrices P a s w ∧
    ∀ (s' : Structure) (w' : ℝ × ℝ), IsOptPrices P a s' w' → cmProfit P a s' w' ≤ cmProfit P a s w

/-- `c^oi = (2 − θ)/3` (Lemma 2, p. 12). -/
def cOI (P : Params) : ℝ := (2 - P.θ) / 3

/-- `c^oo_1 = (2θ − 1 − 3a(1 − θ))/2` (Lemma 3, p. 13). -/
def cOO1 (P : Params) (a : ℝ) : ℝ := (2 * P.θ - 1 - 3 * a * (1 - P.θ)) / 2

/-- `c^oo_2 = (1 + a(1 − θ))/2` (Lemma 3, p. 13). -/
def cOO2 (P : Params) (a : ℝ) : ℝ := (1 + a * (1 - P.θ)) / 2

/-- `T1` (p. 17), with the factor `(1 − θ)²` in the radicand where the page prints `(1 + θ)²`. -/
def T1 (P : Params) (a : ℝ) : ℝ :=
  P.θ - 1 / 2 - 1 / 2 * Real.sqrt ((2 * P.θ - 1) ^ 2 - 4 * a ^ 2 * (1 - P.θ) ^ 2 - 8 * a
    + 18 * a * P.θ - 10 * a * P.θ ^ 2)

/-- `T2` (p. 17). -/
def T2 (P : Params) (a : ℝ) : ℝ :=
  P.θ - 1 / 2 + 3 / 2 * a - 3 / 2 * a * P.θ - 1 / 2 * Real.sqrt (10 * a ^ 2 * (1 - P.θ) ^ 2 + 2
    - 8 * P.θ * (1 - P.θ) - 16 * a + 36 * a * P.θ - 20 * a * P.θ ^ 2)

/-- `T3` (p. 17). -/
def T3 (P : Params) (a : ℝ) : ℝ :=
  P.θ - 1 / 2 + 3 / 2 * a - 3 / 2 * a * P.θ + 1 / 2 * Real.sqrt (10 * a ^ 2 * (1 - P.θ) ^ 2 + 2
    - 8 * P.θ * (1 - P.θ) - 16 * a + 36 * a * P.θ - 20 * a * P.θ ^ 2)

end

end BrandSpillover.Commitment


