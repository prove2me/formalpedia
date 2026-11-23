-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_Simultaneous
-- name    : StrategicRFx_Benefit_Supplement_Simultaneous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:04:31.730739+00:00
-- url     : https://prove2.me/theorems/cd49a3cb-5150-44fa-8aab-cff7ad816fc6
-- title:
--   §2.3.1 — full simultaneous contract Nash programs and Pareto equilibrium
-- statement:
--   Fix the other supplier's believed contract equal to his equilibrium contract. If the buyer sources from both suppliers, supplier $i$'s contract maximizes
--
--   $$\pi_i^{\theta_i}(\pi_0-D_0)^{1-\theta_i},\qquad \pi_i\ge0,\quad\pi_0\ge D_0,$$
--
--   where $D_0$ is the buyer's optimal exclusive payoff with supplier $j$. Both payment functions may vary over the source contract class, subject to nonnegative exclusive supplier payoff. The exclusive-sourcing program is defined separately. If neither program is feasible, the other supplier serves the buyer; the excluded supplier's contract may be arbitrary. The buyer's actual sourcing must agree with the case used to derive the contracts, and both beliefs must be consistent.
--
--   A Pareto equilibrium is a simultaneous equilibrium not dominated by another simultaneous equilibrium in the same primitive technology. Dominance means all three payoffs weakly increase and at least one increases strictly. These predicates contain neither coordination nor cost-plus implementation as hypotheses.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §2.3.1, p. 9; Assumption 3, p. 10

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Primitives

namespace StrategicRFx.Benefit.Supplement

/-- A feasible contract/outcome of the dual branch of [Simu-i]. -/
def DualCandidate (M : Technology) (i : Fin 2) (fixed : Contract)
    (d : Contract) (q : ℝ × ℝ) (D : ℝ) : Prop :=
  Admissible M d i ∧
  IsDualOrder M (fun k => if k = i then d else fixed) q ∧
  0 ≤ (outcomePayoff M (fun k => if k = i then d else fixed) (.dual q)).supplier i ∧
  D ≤ (outcomePayoff M (fun k => if k = i then d else fixed) (.dual q)).buyer

/-- The exclusive branch [Simu-i′]. -/
def SingleCandidate (M : Technology) (i : Fin 2) (d : Contract)
    (s : Sourcing) (D : ℝ) : Prop :=
  Admissible M d i ∧ IsExclusiveOrder M d i s ∧
  0 ≤ (exclusivePayoff M d i s).supplier i ∧ D ≤ (exclusivePayoff M d i s).buyer

/-- Contract-level Nash-product maximization with fixed beliefs, p. 9. -/
def IsDualBargain (M : Technology) (i : Fin 2) (fixed d : Contract)
    (q : ℝ × ℝ) (D : ℝ) : Prop :=
  DualCandidate M i fixed d q D ∧
  ∀ d' q', DualCandidate M i fixed d' q' D →
    nashProduct (M.power i)
      ((outcomePayoff M (fun k => if k = i then d' else fixed) (.dual q')).supplier i)
      ((outcomePayoff M (fun k => if k = i then d' else fixed) (.dual q')).buyer - D) ≤
    nashProduct (M.power i)
      ((outcomePayoff M (fun k => if k = i then d else fixed) (.dual q)).supplier i)
      ((outcomePayoff M (fun k => if k = i then d else fixed) (.dual q)).buyer - D)

def IsSingleBargain (M : Technology) (i : Fin 2) (d : Contract)
    (s : Sourcing) (D : ℝ) : Prop :=
  SingleCandidate M i d s D ∧
  ∀ d' s', SingleCandidate M i d' s' D →
    nashProduct (M.power i) ((exclusivePayoff M d' i s').supplier i)
      ((exclusivePayoff M d' i s').buyer - D) ≤
    nashProduct (M.power i) ((exclusivePayoff M d i s).supplier i)
      ((exclusivePayoff M d i s).buyer - D)

structure ContractOutcome where
  contracts : Contracts
  order : Sourcing
  exclusiveOrder : Fin 2 → Sourcing

def ContractOutcome.payoff (M : Technology) (x : ContractOutcome) : Payoff :=
  outcomePayoff M x.contracts x.order

/-- Each original exclusive payoff is an actual attained optimum, with
nonnegative supplier payoff under Assumption 3. -/
def ValidOutcome (M : Technology) (x : ContractOutcome) : Prop :=
  IsBuyerOrder M x.contracts x.order ∧
  ∀ i, IsExclusiveOrder M (x.contracts i) i (x.exclusiveOrder i) ∧
    0 ≤ (exclusivePayoff M (x.contracts i) i (x.exclusiveOrder i)).supplier i

def NoBargainFeasible (M : Technology) (i : Fin 2) (fixed : Contract) (D : ℝ) : Prop :=
  (¬ ∃ d q, DualCandidate M i fixed d q D) ∧
  (¬ ∃ d s, SingleCandidate M i d s D)

/-- All three cases of §2.3.1, with beliefs equal to the other equilibrium
contract and the buyer's sourcing consistent with the selected case. No
coordination or cost-plus condition occurs in this definition. -/
def IsSimultaneous (M : Technology) (x : ContractOutcome) : Prop :=
  ValidOutcome M x ∧ ∀ i,
    let j := other i
    let D := (exclusivePayoff M (x.contracts j) j (x.exclusiveOrder j)).buyer
    match x.order with
    | .dual q => IsDualBargain M i (x.contracts j) (x.contracts i) q D
    | .single k q => if k = i then IsSingleBargain M i (x.contracts i) (.single i q) D
        else NoBargainFeasible M i (x.contracts j) D
    | .none => NoBargainFeasible M i (x.contracts j) D

/-- Pareto dominance compares equilibria in the same primitive model. -/
def IsParetoSimultaneous (M : Technology) (x : ContractOutcome) : Prop :=
  IsSimultaneous M x ∧ ¬ ∃ y, IsSimultaneous M y ∧ StrictlyImproves (y.payoff M) (x.payoff M)

end StrategicRFx.Benefit.Supplement


