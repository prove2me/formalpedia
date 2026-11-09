-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms
-- name    : SecondBestTrade_HalfEfficiency_Mechanisms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:52.931676+00:00
-- url     : https://prove2.me/theorems/3df9937c-ddbe-4a36-9944-b0d2f786ca87
-- title:
--   §3 and Program (P) — Mechanisms, utilities and benchmarks
-- statement:
--   A direct mechanism assigns feasible trade marginals and nonnegative buyer payments and seller receipts to every report profile. In the signed relaxation, an agent's signed transfer $t_a$ is its payment to the mechanism, so a seller's receipt is $-t_a$. The generic direct-mechanism carrier is reused from the finite-type mechanism library.
--
--   For true type $s$ and report $r$, $U_a(s;r)$ averages over the other agents' product prior, values the allocation at $s$, and evaluates the allocation and transfer at $r$. Buyer utility is value minus payment; seller utility is receipt minus cost. The requirements are
--   $$U_a(s;s)\ge U_a(s;r),\quad U_a(s;s)\ge0,\quad \sum_i p_i(v,c)=\sum_j p_j(v,c)\text{ for every report profile}.$$
--   The signed relaxed class keeps feasibility, BIC and interim IR, and requires only nonnegative expected net revenue. Program (P) uses signed transfers and includes each support report and a null report yielding zero allocation and transfer. Its objective is GFT. The second-best benchmark SB and OPT(P) are suprema over these concrete feasible classes, not assumed optima.
--
--   This layer separates the original mechanism class from its LP relaxation. `finiteLPPresentation` asks for finitely many linear inequalities in all allocation and signed-transfer coordinates and a linear objective equal to GFT. Neither this presentation nor any attainment or budget-conversion theorem is assumed as data.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), §3, (3.1)–(3.5), §5.1 and Program (P), (A.1)–(A.4), printed pp. 3–4, 7, 18–19 (PDF pp. 4–5, 8, 19–20)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Market
import Definitions.Def_MechanismDesign_Correlated_FiniteModel

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Generic direct mechanisms are reused; positive t means a payment by an agent.
A seller's receipt is therefore -t. -/
abbrev SignedMechanism (N : Market) :=
  MechanismDesign.Correlated.FiniteTypes.DirectMechanism (Agent N) (Ty N) (Trade N → ℝ)

def buyerPay (N : Market) (m : SignedMechanism N) (i : Fin N.nb) (v : Profile N) : ℝ :=
  m.t (.inl i) v
def sellerReceipt (N : Market) (m : SignedMechanism N) (j : Fin N.ns) (v : Profile N) : ℝ :=
  -m.t (.inr j) v

/-- The paper's direct mechanism: buyer payments and seller receipts are nonnegative. -/
structure Mechanism (N : Market) where
  x : Allocation N
  pay : Fin N.nb → Profile N → ℝ≥0
  receipt : Fin N.ns → Profile N → ℝ≥0

def toSigned (N : Market) (m : Mechanism N) : SignedMechanism N where
  q := m.x
  t := Sum.elim (fun i v => (m.pay i v : ℝ)) (fun j v => -(m.receipt j v : ℝ))

def valueUtility (N : Market) (a : Agent N) (t : Ty N a) (q : Trade N → ℝ) : ℝ :=
  Sum.elim (fun _ => ∑ e, coord N a t e * q e)
    (fun _ => -(∑ e, coord N a t e * q e)) a

def U (N : Market) (m : SignedMechanism N) (a : Agent N) (t r : Ty N a) : ℝ :=
  expect N (fun v => valueUtility N a t (m.q (overwrite N v a r)) -
    m.t a (overwrite N v a r))

/-- Null report: no incident allocation and no own transfer, so its utility is zero. -/
def nullAllocation (N : Market) : Trade N → ℝ := fun _ => 0
def nullTransfer : ℝ := 0
def reportUtility (N : Market) (m : SignedMechanism N) (a : Agent N) (t : Ty N a) :
    Option (Ty N a) → ℝ
  | none => valueUtility N a t (nullAllocation N) - nullTransfer
  | some r => U N m a t r

def BIC (N : Market) (m : SignedMechanism N) : Prop :=
  ∀ a t r, U N m a t r ≤ U N m a t t
def IR (N : Market) (m : SignedMechanism N) : Prop := ∀ a t, 0 ≤ U N m a t t
def SBB (N : Market) (m : SignedMechanism N) : Prop := ∀ v, ∑ a, m.t a v = 0
def WBB (N : Market) (m : SignedMechanism N) : Prop :=
  0 ≤ expect N (fun v => ∑ a, m.t a v)
def nonnegativeTransfers (N : Market) (m : SignedMechanism N) : Prop :=
  (∀ i v, 0 ≤ buyerPay N m i v) ∧ (∀ j v, 0 ≤ sellerReceipt N m j v)
def relaxed (N : Market) (m : SignedMechanism N) : Prop :=
  feasible N m.q ∧ BIC N m ∧ IR N m ∧ WBB N m
def admissible (N : Market) (m : Mechanism N) : Prop :=
  feasible N m.x ∧ BIC N (toSigned N m) ∧ IR N (toSigned N m) ∧ SBB N (toSigned N m)

noncomputable def SB (N : Market) : ℝ :=
  sSup {z | ∃ m : Mechanism N, admissible N m ∧ z = GFT N m.x}
noncomputable def relaxedSB (N : Market) : ℝ :=
  sSup {z | ∃ m : SignedMechanism N, relaxed N m ∧ z = GFT N m.q}

/-- Program (P), including every support and null-report incentive constraint. -/
def programFeasible (N : Market) (m : SignedMechanism N) : Prop :=
  feasible N m.q ∧ WBB N m ∧
    ∀ a t (r : Option (Ty N a)), reportUtility N m a t r ≤ U N m a t t
noncomputable def OPT (N : Market) : ℝ :=
  sSup {z | ∃ m : SignedMechanism N, programFeasible N m ∧ z = GFT N m.q}

def zeroSigned (N : Market) : SignedMechanism N where
  q := fun _ _ => 0
  t := fun _ _ => 0

/-- Coordinate vector of all allocation and signed transfer variables of (P). -/
abbrev Variable (N : Market) := Profile N × (Trade N ⊕ Agent N)
abbrev LPVector (N : Market) := Variable N → ℝ

def decode (N : Market) (u : LPVector N) : SignedMechanism N where
  q := fun v e => u (v, .inl e)
  t := fun a v => u (v, .inr a)

/-- A finite inequality presentation and a linear objective, in exactly (P)'s variables. -/
def finiteLPPresentation (N : Market) : Prop :=
  ∃ (k : ℕ) (A : Fin k → LPVector N →ₗ[ℝ] ℝ) (b : Fin k → ℝ)
    (l : LPVector N →ₗ[ℝ] ℝ),
    (∀ u, programFeasible N (decode N u) ↔ ∀ r, A r u ≤ b r) ∧
    (∀ u, l u = GFT N (decode N u).q)

end SecondBestTrade.HalfEfficiency


