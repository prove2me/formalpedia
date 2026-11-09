-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_HDFPA
-- name    : CorrelatedAuctionComplexity_Main_HDFPA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:18.679094+00:00
-- url     : https://prove2.me/theorems/035b6090-43a9-49f7-8753-ce651b10b66a
-- title:
--   Hypergraph auctions, incident-weight equilibrium, and normalization
-- statement:
--   A hypergraph discrete first-price auction has finitely many bidders, a public rational value for each, a finite rational bid set containing zero, and a list of positive weighted nonempty participant sets. The list retains repeated auctions. Every bidder participates somewhere. In a model with range bound $R$, values and bids lie in $[0,R]$.
--
--   A legal mixed profile assigns each bidder an arbitrary real lottery on the bids, with zero probability on bids above her value. Write $U_i(\sigma)$ for the sum of weighted auction utilities and $W_i>0$ for the sum of incident weights. The approximation convention is
--
--   $$U_i(\sigma)\ge U_i(b_i,\sigma_{-i})-\eta W_i\qquad(b_i\le v_i).$$
--
--   The bundle also provides rational-profile evaluation, conditional-edge utilities, the scaling map $(B,v)\mapsto(B/c,v/c)$, and Nash's map from equation (6), using payoffs divided by $W_i$. Weights are never required to sum to one.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Definitions 4–5, Section 3.2, pp. 10–11; Eq. (6), pp. 20–21 (PDF same pages)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_FiniteAuction

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


/-- Numerical data, without embedding any equilibrium or complexity conclusion. -/
structure HDFPA (N : Type) where
  bids : Finset ℚ
  value : N → ℚ
  edges : List (AuctionEdge N)

namespace HDFPA
variable {N : Type} [Fintype N] [DecidableEq N]

def WellFormed (H : HDFPA N) (bound : ℚ) : Prop :=
  Nonempty N ∧ 0 ∈ H.bids ∧
  (∀ b ∈ H.bids, 0 ≤ b ∧ b ≤ bound) ∧
  (∀ i, 0 ≤ H.value i ∧ H.value i ≤ bound) ∧
  (∀ e ∈ H.edges, e.WellFormed) ∧
  ∀ i, ∃ e ∈ H.edges, i ∈ e.participants

abbrev Bid (H : HDFPA N) := {b // b ∈ H.bids}
abbrev Profile (H : HDFPA N) := N → H.Bid → ℝ
abbrev RatProfile (H : HDFPA N) := N → H.Bid → ℚ

def Legal (H : HDFPA N) (p : H.Profile) : Prop :=
  ∀ i, IsLottery (p i) ∧ ∀ b, H.value i < b.val → p i b = 0

def Pure (H : HDFPA N) (p : H.Profile) : Prop :=
  ∀ i, ∃ b, p i b = 1 ∧ ∀ a, a ≠ b → p i a = 0

def edge (H : HDFPA N) (e : Fin H.edges.length) : AuctionEdge N := H.edges[e]

noncomputable def incidentWeight (H : HDFPA N) (i : N) : ℝ :=
  ∑ e : Fin H.edges.length, if i ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0

noncomputable def edgeUtility (H : HDFPA N) (e : Fin H.edges.length)
    (p : H.Profile) (i : N) : ℝ :=
  ((H.edge e).weight : ℝ) * expectation p
    (fun b => (singlePayoff (H.edge e).participants H.value (fun j => (b j).val) i : ℝ))

noncomputable def utility (H : HDFPA N) (p : H.Profile) (i : N) : ℝ :=
  ∑ e : Fin H.edges.length, H.edgeUtility e p i

noncomputable def pureUtility (H : HDFPA N) (p : H.Profile) (i : N) (b : H.Bid) : ℝ :=
  H.utility (deviation p i b) i

def IsNE (H : HDFPA N) (η : ℝ) (p : H.Profile) : Prop :=
  H.Legal p ∧ ∀ i b, b.val ≤ H.value i →
    H.pureUtility p i b - η * H.incidentWeight i ≤ H.utility p i

/-- This is the conditional edge distribution of Observation 5, including multiplicities. -/
noncomputable def conditionalUtility (H : HDFPA N) (p : H.Profile) (i : N) : ℝ :=
  ∑ e : Fin H.edges.length,
    if i ∈ (H.edge e).participants then H.edgeUtility e p i / H.incidentWeight i else 0

/-- Rational evaluation is used only for finite computational outputs. -/
def utilityQ (H : HDFPA N) (p : H.RatProfile) (i : N) : ℚ :=
  ∑ e : Fin H.edges.length, (H.edge e).weight *
    ∑ b : N → H.Bid, (∏ j, p j (b j)) *
      singlePayoff (H.edge e).participants H.value (fun j => (b j).val) i

noncomputable def realProfile (H : HDFPA N) (p : H.RatProfile) : H.Profile :=
  fun i b => (p i b : ℝ)

/-- Scaling changes bids and values, and leaves edge occurrences and weights intact. -/
def scale (H : HDFPA N) (c : ℚ) : HDFPA N where
  bids := H.bids.image (fun b => b / c)
  value := fun i => H.value i / c
  edges := H.edges

noncomputable def normalizedPayoff (H : HDFPA N) (p : H.Profile) (i : N) : ℝ :=
  H.utility p i / H.incidentWeight i

noncomputable def gain (H : HDFPA N) (p : H.Profile) (i : N) (a : H.Bid) : ℝ :=
  if a.val ≤ H.value i then
    max 0 ((H.pureUtility p i a - H.utility p i) / H.incidentWeight i) else 0

/-- Section 4.7, equation (6), on all legal actions. -/
noncomputable def nashMap (H : HDFPA N) (p : H.Profile) : H.Profile :=
  fun i b => (p i b + H.gain p i b) / (1 + ∑ a, H.gain p i a)

end HDFPA

end CorrelatedAuctionComplexity.Main


