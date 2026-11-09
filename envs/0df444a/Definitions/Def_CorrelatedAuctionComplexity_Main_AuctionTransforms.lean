-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_AuctionTransforms
-- name    : CorrelatedAuctionComplexity_Main_AuctionTransforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:59.334238+00:00
-- url     : https://prove2.me/theorems/9573eaf2-b2b6-4139-9918-fddb09d64b69
-- title:
--   Shifted DFPA with dummy bidders and type-clone decomposition
-- statement:
--   For an unnormalized binary-bid HDFPA with values in $\{1/2,2,3,4\}$ and at most four participants per edge, construct $A_H$ on the original bidders and fifty value-zero dummy bidders. Its bids are $\{0,1,2\}$. An edge $S$ gives its participants shifted values $v_i+1$ and everyone else zero, with mass proportional to its weight. Every anchor receives an additional singleton value vector of mass $W_i$. Identical edges are merged, masses normalized, and coinciding vectors merged. The strategy extraction uses
--
--   $$\sigma_i(1)=\beta_{x_i}(v_i+1)(2),\qquad\sigma_i(0)=1-\sigma_i(1).$$
--
--   For a general DFPA $A$, the decomposition $H_A$ has a clone $(i,v)$ for every supported bidder type. Each prior atom gives an edge on its corresponding clones with its prior mass as weight. Forward and inverse profile maps simply reindex the same distributions. Both constructions are defined from the input data, without equilibrium hypotheses.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Section 5.1, pp. 21–24; Definition 18 and Lemma 19 proof, pp. 24–26 (PDF same pages)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_DFPA
import Definitions.Def_CorrelatedAuctionComplexity_Main_Gadgets

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


variable {N : Type} [Fintype N] [DecidableEq N]

/-- The hard family in Section 5.1, before either normalization. -/
def HardFamily (H : HDFPA N) : Prop :=
  H.WellFormed 4 ∧ H.bids = {0,1} ∧
  (∀ i, H.value i ∈ ({1/2,2,3,4} : Finset ℚ)) ∧
  ∀ e ∈ H.edges, e.participants.card ≤ 4

/-- Merging hyperedges with identical participant sets, as in footnote 7. -/
def mergedEdges (H : HDFPA N) : List (AuctionEdge N) :=
  ((H.edges.map AuctionEdge.participants).eraseDups).map fun S =>
    ⟨S, ((H.edges.filter fun e => e.participants = S).map AuctionEdge.weight).sum⟩

/-- The 50 extra bidders participate even when their value is zero. -/
noncomputable def shiftedAtoms (H : HDFPA N) : List (PriorAtom (N ⊕ Fin 50)) :=
  ((mergedEdges H).map fun e =>
    ⟨(fun j => match j with
      | .inl i => if i ∈ e.participants then H.value i + 1 else 0
      | .inr _ => 0), e.weight⟩) ++
  ((Finset.univ.filter fun i => H.value i = 1/2).toList.map fun i =>
    ⟨(fun j => if j = Sum.inl i then 3/2 else 0),
      ((H.edges.filter fun e => i ∈ e.participants).map AuctionEdge.weight).sum⟩)

/-- A_H is constructed from H, including the anchor mass and global mass normalization. -/
noncomputable def shiftedDFPA (H : HDFPA N) : DFPA (N ⊕ Fin 50) where
  bids := {0,1,2}
  prior := DFPA.coalesce ((shiftedAtoms H).map fun d =>
    ⟨d.value, d.mass / ((shiftedAtoms H).map PriorAtom.mass).sum⟩)

/-- On well-formed hard instances every requested positive type is in the support. -/
noncomputable def shiftedProbability (H : HDFPA N) (β : (shiftedDFPA H).Profile)
    (i : N) (b : ℚ) : ℝ :=
  if hv : H.value i + 1 ∈ (shiftedDFPA H).types (.inl i) then
    if hb : b ∈ (shiftedDFPA H).bids then β (.inl i) ⟨_,hv⟩ ⟨b,hb⟩ else 0
  else 0

noncomputable def pullBackShifted (H : HDFPA N) (β : (shiftedDFPA H).Profile) : H.Profile :=
  H.binaryProfile (fun i => shiftedProbability H β i 2)

namespace DFPA
abbrev Clone (A : DFPA N) := Σ i : N, A.TypeAt i

/-- Definition 18. Every support occurrence becomes an edge on its exact type clones. -/
def decomposition (A : DFPA N) : HDFPA A.Clone where
  bids := A.bids
  value := fun c => c.2.val
  edges := (List.finRange A.prior.length).map fun d =>
    ⟨Finset.univ.image (fun i => (⟨i,A.atomType d i⟩ : A.Clone)), A.prior[d].mass⟩

noncomputable def profileForward (A : DFPA N) (σ : A.decomposition.Profile) : A.Profile :=
  fun i v b => σ ⟨i,v⟩ b

noncomputable def profileInverse (A : DFPA N) (β : A.Profile) : A.decomposition.Profile :=
  fun c b => β c.1 c.2 b

end DFPA

end CorrelatedAuctionComplexity.Main


