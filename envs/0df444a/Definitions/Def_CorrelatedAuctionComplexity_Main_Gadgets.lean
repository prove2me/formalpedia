-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_Gadgets
-- name    : CorrelatedAuctionComplexity_Main_Gadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:20.329029+00:00
-- url     : https://prove2.me/theorems/ebb67bd7-a44a-425b-9db4-6500b70ed357
-- title:
--   COPY, SUM, and NOT auction occurrences with ambient-edge conditions
-- statement:
--   In the binary-bid model, $p(x)$ is the probability of bidding one and $\Delta_x^R(p)$ is the weighted utility difference between pure bids one and zero over the selected edge occurrences:
--
--   $$\Delta_x^R(p)=U_x^R(1,p_{-x})-U_x^R(0,p_{-x}).$$
--
--   COPY, SUM and NOT are the exact edge and weight tables in Sections 4.3–4.5. Input bidders have value 2, outputs 4, helpers 3, and anchors $1/2$. An occurrence injectively selects edge occurrences in the ambient multiset; its helpers and anchors occur in no other edge. Role predicates specify the values and freshness. SUM permits repeated inputs, while its two corresponding edge occurrences remain distinct. COPY uses the common positive multiplier $\Lambda$; the other tables have multiplier one. These definitions impose no equilibrium response.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Sections 4.1–4.5, pp. 12–18 (PDF pp. 12–18)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_HDFPA

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


namespace HDFPA
variable {N : Type} [Fintype N] [DecidableEq N]

def binaryProfile (H : HDFPA N) (p : N → ℝ) : H.Profile :=
  fun i b => if b.val = 1 then p i else 1 - p i

def LegalBinary (H : HDFPA N) (p : N → ℝ) : Prop :=
  (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∀ i, H.value i < 1 → p i = 0

noncomputable def binaryEdgePure (H : HDFPA N) (p : N → ℝ)
    (e : Fin H.edges.length) (i : N) (t : Bool) : ℝ :=
  ((H.edge e).weight : ℝ) * expectation
    (deviation (fun (j : N) (a : Bool) => if a then p j else 1 - p j) i t)
    (fun b => (singlePayoff (H.edge e).participants H.value
      (fun j => if b j then 1 else 0) i : ℝ))

noncomputable def delta (H : HDFPA N) (p : N → ℝ)
    (R : Finset (Fin H.edges.length)) (i : N) : ℝ :=
  ∑ e ∈ R, (H.binaryEdgePure p e i true - H.binaryEdgePure p e i false)

noncomputable def totalDelta (H : HDFPA N) (p : N → ℝ) (i : N) : ℝ :=
  H.delta p Finset.univ i

end HDFPA

/-- Coefficients are rational; COPY's common multiplier is supplied separately. -/
structure Gadget (N : Type) where
  auctions : List (AuctionEdge N)
  auxiliaries : List N

/-- An occurrence is an injective selection of EDGE OCCURRENCES in the ambient multiset. -/
def Occurs {N : Type} [Fintype N] [DecidableEq N] (H : HDFPA N)
    (G : Gadget N) (ids : Fin G.auctions.length → Fin H.edges.length) (scale : ℝ) : Prop :=
  Function.Injective ids ∧
  (∀ j, (H.edge (ids j)).participants = G.auctions[j].participants ∧
    ((H.edge (ids j)).weight : ℝ) = (G.auctions[j].weight : ℝ) * scale) ∧
  ∀ e, e ∉ Set.range ids → ∀ a ∈ G.auxiliaries, a ∉ (H.edge e).participants

def gadgetEdges {N : Type} (H : HDFPA N) (G : Gadget N)
    (ids : Fin G.auctions.length → Fin H.edges.length) : Finset (Fin H.edges.length) :=
  Finset.univ.image ids

def copyGadget {N : Type} [DecidableEq N] (y x h : N) (z : Fin 3 → N) : Gadget N where
  auxiliaries := h :: List.ofFn z
  auctions := [⟨{y,h},4⟩, ⟨{y,h,z 0},12⟩, ⟨{y},24⟩, ⟨{x,h},4⟩,
    ⟨{x,h,z 1,z 2},16⟩, ⟨{h},36⟩, ⟨{x},9⟩]

def sumGadget {N : Type} [DecidableEq N] (x₁ x₂ y h : N) (z : Fin 6 → N) : Gadget N where
  auxiliaries := h :: List.ofFn z
  auctions := [⟨{x₁,h,z 0,z 1},4⟩, ⟨{x₂,h,z 2,z 3},4⟩, ⟨{y,h},8⟩,
    ⟨{y,h,z 4,z 5},12⟩, ⟨{h},29⟩, ⟨{y},31⟩]

def notGadget {N : Type} [DecidableEq N] (x y h : N) (z : Fin 2 → N) : Gadget N where
  auxiliaries := h :: List.ofFn z
  auctions := [⟨{x,h},2⟩, ⟨{y,h},8⟩, ⟨{y,h,z 0,z 1},12⟩, ⟨{h},21⟩, ⟨{y},31⟩]

def CopyRoles {N : Type} [DecidableEq N] (H : HDFPA N) (y x h : N) (z : Fin 3 → N) : Prop :=
  (y :: x :: h :: List.ofFn z).Nodup ∧ H.value y = 4 ∧ H.value x = 2 ∧
  H.value h = 3 ∧ ∀ j, H.value (z j) = 1/2

def SumRoles {N : Type} [DecidableEq N] (H : HDFPA N)
    (x₁ x₂ y h : N) (z : Fin 6 → N) : Prop :=
  (y :: h :: List.ofFn z).Nodup ∧
  (∀ a ∈ y :: h :: List.ofFn z, a ≠ x₁ ∧ a ≠ x₂) ∧
  H.value x₁ = 2 ∧ H.value x₂ = 2 ∧ H.value y = 4 ∧ H.value h = 3 ∧
  ∀ j, H.value (z j) = 1/2

def NotRoles {N : Type} [DecidableEq N] (H : HDFPA N) (x y h : N) (z : Fin 2 → N) : Prop :=
  (x :: y :: h :: List.ofFn z).Nodup ∧ H.value x = 2 ∧ H.value y = 4 ∧
  H.value h = 3 ∧ ∀ j, H.value (z j) = 1/2

end CorrelatedAuctionComplexity.Main


