-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_GeneralizedCircuit
-- name    : CorrelatedAuctionComplexity_Main_GeneralizedCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:30.9083+00:00
-- url     : https://prove2.me/theorems/929cf218-4d8e-4f3d-be6e-4ffe57cb18d1
-- title:
--   SUM/NOT generalized circuits and the concrete hard HDFPA
-- statement:
--   A generalized circuit has a finite node set and at most one output gate per node. A gate is saturated SUM or NOT, with its output distinct from its inputs; a SUM may repeat its input. Cycles are allowed. A solution obeys
--
--   $$a\in[0,1+\varepsilon]^V,\qquad |a_w-\min(a_u+a_v,1)|\le\varepsilon,\qquad |a_w-(1-a_u)|\le\varepsilon$$
--
--   for the respective gates. Bounded input use counts a gate once even if it repeats an input.
--
--   The hard auction is constructed from two main bidders per node, one COPY per node with $\Lambda=40$, and one fresh SUM or NOT gadget per gate. Auxiliary bidder types contain exactly the helpers and anchors used. Thus the construction defines auctions and values from circuit data, rather than assuming gadget correctness or a reduction.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Definition 6, pp. 11–12; Sections 4.2–4.6, pp. 13–19 (PDF same pages)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_Gadgets

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


/-- No acyclicity is imposed. A repeated SUM input is permitted. -/
inductive Gate (n : ℕ) where
  | sum (u v w : Fin n)
  | neg (u w : Fin n)
  deriving DecidableEq

namespace Gate
variable {n : ℕ}
def output : Gate n → Fin n
  | .sum _ _ w => w
  | .neg _ w => w

def inputs : Gate n → Finset (Fin n)
  | .sum u v _ => {u,v}
  | .neg u _ => {u}

def auxCount : Gate n → ℕ
  | .sum _ _ _ => 7
  | .neg _ _ => 3
end Gate

structure GeneralizedCircuit where
  n : ℕ
  gates : List (Gate n)

namespace GeneralizedCircuit

def WellFormed (C : GeneralizedCircuit) : Prop :=
  C.gates.length ≤ C.n ∧ (C.gates.map Gate.output).Nodup ∧
  (∀ g ∈ C.gates, g.output ∉ g.inputs)

def BoundedInput (C : GeneralizedCircuit) : Prop :=
  ∀ u : Fin C.n, (C.gates.filter fun g => u ∈ g.inputs).length ≤ 2

def Solution (C : GeneralizedCircuit) (ε : ℝ) (a : Fin C.n → ℝ) : Prop :=
  (∀ u, 0 ≤ a u ∧ a u ≤ 1 + ε) ∧ ∀ g ∈ C.gates, match g with
    | .sum u v w => |a w - min (a u + a v) 1| ≤ ε
    | .neg u w => |a w - (1 - a u)| ≤ ε

/-- Main output/input bidders, four COPY auxiliaries per node, and the exact number
of auxiliaries needed by each gate. Thus there are no unused, unincident bidders. -/
abbrev HardBidder (C : GeneralizedCircuit) :=
  (Fin C.n × Bool) ⊕ ((Fin C.n × Fin 4) ⊕
    (Σ g : Fin C.gates.length, Fin (C.gates[g].auxCount)))

def outputBidder (C : GeneralizedCircuit) (u : Fin C.n) : C.HardBidder := .inl (u,true)
def inputBidder (C : GeneralizedCircuit) (u : Fin C.n) : C.HardBidder := .inl (u,false)
def copyHelper (C : GeneralizedCircuit) (u : Fin C.n) : C.HardBidder := .inr (.inl (u,0))
def copyAnchor (C : GeneralizedCircuit) (u : Fin C.n) (j : Fin 3) : C.HardBidder :=
  .inr (.inl (u,⟨j.val+1, by omega⟩))

noncomputable def gateAuctions (C : GeneralizedCircuit) (g : Fin C.gates.length) :
    List (AuctionEdge C.HardBidder) := by
  classical
  let h : C.HardBidder := .inr (.inr ⟨g, ⟨0, by cases C.gates[g] <;> simp [Gate.auxCount]⟩⟩)
  match hg : C.gates[g] with
  | .sum u v w =>
    let z : Fin 6 → C.HardBidder := fun j =>
      .inr (.inr ⟨g,⟨j.val+1, by simp [hg, Gate.auxCount]; omega⟩⟩)
    exact (sumGadget (C.inputBidder u) (C.inputBidder v) (C.outputBidder w) h z).auctions
  | .neg u w =>
    let z : Fin 2 → C.HardBidder := fun j =>
      .inr (.inr ⟨g,⟨j.val+1, by simp [hg, Gate.auxCount]; omega⟩⟩)
    exact (notGadget (C.inputBidder u) (C.outputBidder w) h z).auctions

/-- Section 4.2/4.6 with Λ=40, using the tables of Sections 4.3–4.5. -/
noncomputable def hardHDFPA (C : GeneralizedCircuit) : HDFPA C.HardBidder where
  bids := {0,1}
  value := fun i => match i with
    | .inl (_,b) => if b then 4 else 2
    | .inr (.inl (_,j)) => if j.val = 0 then 3 else 1/2
    | .inr (.inr ⟨_,j⟩) => if j.val = 0 then 3 else 1/2
  edges := ((List.finRange C.n).flatMap fun u =>
    ((copyGadget (C.outputBidder u) (C.inputBidder u) (C.copyHelper u) (C.copyAnchor u)).auctions.map
      fun e => ⟨e.participants,40 * e.weight⟩)) ++
    ((List.finRange C.gates.length).flatMap C.gateAuctions)

end GeneralizedCircuit

end CorrelatedAuctionComplexity.Main


