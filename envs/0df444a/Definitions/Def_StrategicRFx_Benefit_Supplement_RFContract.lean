-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_RFContract
-- name    : StrategicRFx_Benefit_Supplement_RFContract
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:09:02.144172+00:00
-- url     : https://prove2.me/theorems/4fc9749f-a6c9-416e-9db6-8f2f88503360
-- title:
--   §§2.3, 3.2 — quantity-level RFx commitments and sequential contract bargaining
-- statement:
--   An accepted quotation commits the buyer to procure the solicited first-best quantity from that supplier even if renegotiation fails. If the quoted profit is $t_i$, its total payment is
--
--   $$C_i(q_i^o)+t_i.$$
--
--   An ordinary negotiated contract contains unrestricted normal and exclusive transfer functions. A spot commitment fixes both the quantity and total payment; it cannot be discarded by switching to exclusive sourcing from the other supplier or to no transaction. Rejection leaves the no-deal contract as fallback. Actual sourcing compares all permitted dual, exclusive and no-transaction alternatives.
--
--   Follower renegotiation maximizes the literal Nash product of gains above the actual fallback transaction, with the other supplier's procurement right fixed. The buyer chooses acceptance or rejection optimally, including acceptance at a tie. Leader renegotiation anticipates that entire follower correspondence and its no-agreement continuation. The buyer then chooses the sequence and first acceptance decision optimally. Both sourcing programs and the infeasible case are present. Neither coordination nor a cost-plus restriction is part of equilibrium.
--
--   This provides the contract-level RFx setting needed by Theorems 2 and 3, without identifying it with the already published coordinated scalar model. The deterministic cost-plus outcome uses all four exact transfer formulas and first-best order witnesses.
--
--   **Formalization Note** Maxima are relational, not default real suprema; no arbitrary transfer function is assumed to attain an optimum. Each equilibrium carries consistent selections from the possibly multivalued source response; the same policies evaluate every candidate and fallback. This is the negotiation stage only; quotation-game histories are separate.
--
--   **Continuation selection** Each equilibrium quantifies consistent follower policies for both possible leaders, covering every attained response domain without a universal-attainment assumption. Buyer order and acceptance comparisons use these same policies, as do the leader’s candidate contracts and no-deal/accepted-quote fallbacks.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §2.3, pp. 9–10; §3.2, pp. 15–18; proofs of Theorems 2–3, pp. ec2–ec5

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Sequential

namespace StrategicRFx.Benefit.Supplement

/-- A spot commitment survives failed renegotiation. It obliges the buyer to
procure exactly the solicited quantity at the quoted total payment (p. 15).
An ordinary contract still permits supplier exclusion. -/
inductive ProcurementRight where
  | contract (c : Contract)
  | spot (quantity payment : ℝ)

abbrev Rights := Fin 2 → ProcurementRight

def quantityFrom (s : Sourcing) (i : Fin 2) : ℝ :=
  if i = 0 then (sourcingQuantity s).1 else (sourcingQuantity s).2

def Sourcing.positive : Sourcing → Prop
  | .none => True
  | .dual q => 0 < q.1 ∧ 0 < q.2
  | .single _ q => 0 < q

/-- A spot commitment may not be discarded by choosing single sourcing or
no transaction. A no-deal contract permits only zero procurement. -/
def ProcurementRight.permits (s : Sourcing) (i : Fin 2) : ProcurementRight → Prop
  | .contract c => 0 < quantityFrom s i → c.isSome
  | .spot q _ => 0 < q ∧ quantityFrom s i = q

def tradeAvailable (c : Rights) (s : Sourcing) : Prop :=
  s.positive ∧ ∀ i, (c i).permits s i

def ProcurementRight.transfer (s : Sourcing) (i : Fin 2) : ProcurementRight → ℝ
  | .contract c => match s with
    | .none => 0
    | .dual _ => normalTransfer c (quantityFrom s i)
    | .single k q => if k = i then exclusiveTransfer c q else 0
  | .spot _ p => p

/-- Transfers are used only on available trades. Excluded suppliers have no
production or payment; a committed supplier cannot be excluded. -/
def tradePayoff (M : Technology) (c : Rights) (s : Sourcing) : Payoff :=
  { buyer := M.revenue (sourcingQuantity s) -
      (c 0).transfer s 0 - (c 1).transfer s 1
    supplier := fun i => (c i).transfer s i - M.cost i (quantityFrom s i) }

def IsTradeOrder (M : Technology) (c : Rights) (s : Sourcing) : Prop :=
  tradeAvailable c s ∧ ∀ r, tradeAvailable c r →
    (tradePayoff M c r).buyer ≤ (tradePayoff M c s).buyer

/-- Conditional sourcing programs (1)–(2); global sourcing consistency is
imposed on the selected continuation, rather than on every competitor. -/
def SameSourcingBranch : Sourcing → Sourcing → Prop
  | .none, .none => True
  | .dual _, .dual _ => True
  | .single i _, .single j _ => i = j
  | _, _ => False

def IsTradeBranchOrder (M : Technology) (c : Rights) (s : Sourcing) : Prop :=
  tradeAvailable c s ∧ ∀ r, SameSourcingBranch s r → tradeAvailable c r →
    (tradePayoff M c r).buyer ≤ (tradePayoff M c s).buyer

structure TradeOutcome where
  rights : Rights
  order : Sourcing

def TradeOutcome.payoff (M : Technology) (x : TradeOutcome) : Payoff :=
  tradePayoff M x.rights x.order

/-- Assumption 3 on negotiated exclusive clauses; quote profits are
nonnegative under the nonnegative-quote hypothesis. -/
def ValidTrade (M : Technology) (x : TradeOutcome) : Prop :=
  IsTradeOrder M x.rights x.order ∧
  ∀ i c, x.rights i = .contract c → Admissible M c i

def ordinaryRights (c : Contracts) : Rights := fun i => .contract (c i)

def ContractOutcome.trade (x : ContractOutcome) : TradeOutcome :=
  ⟨ordinaryRights x.contracts, x.order⟩

def solicitedQuantity (b : FirstBest) (i : Fin 2) : ℝ :=
  if i = 0 then b.dual.1 else b.dual.2

/-- Quote t_i denotes profit, so total price is C_i(q_i^o)+t_i. -/
def quoteRight (M : Technology) (b : FirstBest) (t : Fin 2 → ℝ)
    (i : Fin 2) (accept : Bool) : ProcurementRight :=
  if accept then .spot (solicitedQuantity b i) (M.cost i (solicitedQuantity b i) + t i)
  else .contract none

/-- Supplier i's renegotiation candidate, for one of the dual or own-exclusive
branches. The other right is fixed. The full unrestricted pair of contingent
payment functions is renegotiated. Reservation utilities come from an actual
fallback order; no scalar coordination premise occurs here. -/
def RFStageCandidate (M : Technology) (i : Fin 2) (fixed : ProcurementRight)
    (D : Payoff) (dual : Bool) (x : TradeOutcome) : Prop :=
  (∃ d : Payment, x.rights i = .contract (some d) ∧ Admissible M (some d) i) ∧
  x.rights (other i) = fixed ∧
  (if dual then ∃ q, x.order = .dual q else ∃ q, x.order = .single i q) ∧
  IsTradeBranchOrder M x.rights x.order ∧
  D.supplier i ≤ (x.payoff M).supplier i ∧ D.buyer ≤ (x.payoff M).buyer

/-- Literal Nash gains for a contract-level renegotiation. -/
noncomputable def rfStageProduct (M : Technology) (i : Fin 2) (D : Payoff)
    (x : TradeOutcome) : ℝ :=
  nashProduct (M.power i) ((x.payoff M).supplier i - D.supplier i)
    ((x.payoff M).buyer - D.buyer)

/-- Given the fixed other right and the accepted/rejected own quote, compare
all feasible contingent contracts in the selected sourcing branch. If both
programs are infeasible, retain the actual no-agreement sourcing outcome.
No assumption makes every arbitrary transfer function attain an optimum. -/
def IsRFStageSolution (M : Technology) (i : Fin 2) (fixed ownFallback : ProcurementRight)
    (x : TradeOutcome) : Prop :=
  ∃ s, IsTradeOrder M (fun k => if k = i then ownFallback else fixed) s ∧
    let z : TradeOutcome := ⟨fun k => if k = i then ownFallback else fixed, s⟩
    (ValidTrade M x ∧ ∃ dual, RFStageCandidate M i fixed (z.payoff M) dual x ∧
      ∀ y, RFStageCandidate M i fixed (z.payoff M) dual y →
        rfStageProduct M i (z.payoff M) y ≤ rfStageProduct M i (z.payoff M) x) ∨
    ((¬ ∃ dual y, RFStageCandidate M i fixed (z.payoff M) dual y) ∧ x = z)

/-- At the follower node the buyer may accept or reject the quote before
renegotiating. All optimal continuations are retained. Equality favors
acceptance; this is the follower accept-at-equality convention on pp. 17–18. -/
def RFxFollower (M : Technology) (b : FirstBest) (t : Fin 2 → ℝ)
    (leader : Fin 2) (fixed : ProcurementRight) (x : TradeOutcome) : Prop :=
  ∃ accept : Bool,
    IsRFStageSolution M (other leader) fixed (quoteRight M b t (other leader) accept) x ∧
    (∀ a y, IsRFStageSolution M (other leader) fixed
        (quoteRight M b t (other leader) a) y → (y.payoff M).buyer ≤ (x.payoff M).buyer) ∧
    (accept = false → ∀ y, IsRFStageSolution M (other leader) fixed
        (quoteRight M b t (other leader) true) y → (y.payoff M).buyer < (x.payoff M).buyer)

/-- A follower strategy selects from its continuation correspondence at
each fixed leader right, only where an attained optimum exists. All these
selections are admissible; no unique-argmax condition is imposed. -/
def RFContinuationPolicy (M : Technology) (b : FirstBest) (t : Fin 2 → ℝ)
    (leader : Fin 2) (F : ProcurementRight → TradeOutcome → Prop) : Prop :=
  (∀ d x, F d x → RFxFollower M b t leader d x) ∧
  (∀ d, (∃ x, RFxFollower M b t leader d x) → ∃ x, F d x) ∧
  (∀ d x y, F d x → F d y → x = y)

/-- The leader's candidate uses one consistent follower selection across
all candidate contracts, rather than choosing a new response at each
comparison. Accepted/rejected fallbacks use that same policy. -/
def RFLeaderCandidate (M : Technology) (leader : Fin 2)
    (F : ProcurementRight → TradeOutcome → Prop)
    (D : Payoff) (dual : Bool) (x : TradeOutcome) : Prop :=
  (∃ d : Payment, x.rights leader = .contract (some d) ∧ Admissible M (some d) leader) ∧
  F (x.rights leader) x ∧
  (if dual then ∃ q, x.order = .dual q else ∃ q, x.order = .single leader q) ∧
  D.supplier leader ≤ (x.payoff M).supplier leader ∧ D.buyer ≤ (x.payoff M).buyer

/-- [Sequ-i] with RFx reservation changes and a fixed follower policy.
Failure preserves the accepted spot commitment, or no deal after rejection. -/
def RFxLeader (M : Technology) (b : FirstBest) (t : Fin 2 → ℝ)
    (leader : Fin 2) (F : ProcurementRight → TradeOutcome → Prop)
    (accept : Bool) (x : TradeOutcome) : Prop :=
  ∃ z, F (quoteRight M b t leader accept) z ∧
    ((∃ dual, RFLeaderCandidate M leader F (z.payoff M) dual x ∧
        ∀ y, RFLeaderCandidate M leader F (z.payoff M) dual y →
          rfStageProduct M leader (z.payoff M) y ≤ rfStageProduct M leader (z.payoff M) x) ∨
      ((¬ ∃ dual y, RFLeaderCandidate M leader F (z.payoff M) dual y) ∧ x = z))

/-- An equilibrium contains consistent continuation policies for both possible
leader choices. The buyer compares acceptance and order alternatives within
these same policies; each policy is allowed to select any attained follower
response. This retains the source's full multivalued continuation domain. -/
def IsSequentialWithRFx (M : Technology) (b : FirstBest) (t : Fin 2 → ℝ)
    (leader : Fin 2) (x : TradeOutcome) : Prop :=
  (∀ i, 0 ≤ t i) ∧
  ∃ F : Fin 2 → ProcurementRight → TradeOutcome → Prop,
    (∀ i, RFContinuationPolicy M b t i (F i)) ∧
    ∃ a, RFxLeader M b t leader (F leader) a x ∧
      ∀ j a' y, RFxLeader M b t j (F j) a' y → (y.payoff M).buyer ≤ (x.payoff M).buyer

/-- Theorem 3's settings, including both orders and every quote pair. -/
inductive ContractSetting where
  | simultaneous
  | sequential (leader : Fin 2)
  | rfx (quotes : Fin 2 → ℝ) (leader : Fin 2)

def IsContractEquilibrium (M : Technology) (b : FirstBest)
    (setting : ContractSetting) (x : ContractOutcome) : Prop :=
  match setting with
  | .simultaneous => IsSimultaneous M x
  | .sequential i => IsSequentialWithoutRFx M i x
  | .rfx t i => ValidOutcome M x ∧ IsSequentialWithRFx M b t i x.trade

/-- Theorem 3's exact four transfers, with first-best normal and exclusive
orders as attained witnesses. No equilibrium property is built into this
constructor. -/
def costPlusOutcome (M : Technology) (b : FirstBest) (x : ContractOutcome) : ContractOutcome :=
  { contracts := replacement M b x.contracts (x.payoff M) x.exclusiveOrder
    order := .dual b.dual
    exclusiveOrder := fun i => .single i (b.exclusive i) }

end StrategicRFx.Benefit.Supplement


