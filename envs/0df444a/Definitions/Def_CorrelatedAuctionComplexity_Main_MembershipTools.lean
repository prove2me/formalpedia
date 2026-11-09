-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools
-- name    : CorrelatedAuctionComplexity_Main_MembershipTools
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:39.849593+00:00
-- url     : https://prove2.me/theorems/081b10b9-0f2d-44ec-88d3-02a75ab01cee
-- title:
--   Tie-count dynamic program, profile codecs, and exact accuracy conversions
-- statement:
--   The tie-count row begins at $D_{0,0}=1$ and is updated by
--
--   $$D_{r,k}=\ell_rD_{r-1,k}+t_rD_{r-1,k-1},$$
--
--   with zero out-of-range coefficients. The pure-bid edge utility is $(v_i-b)\sum_kD_{m,k}/(k+1)$. Clone and DFPA profile encodings use the same coordinate order. A utility request includes the auction, rational profile and bidder index.
--
--   The source's numerical interfaces are recorded exactly: circuit error $6000\eta$; HDFPA scaling accuracy $\eta/4$; DFPA transfer error $121\varepsilon'$; final normalized DFPA accuracy $\eta/605$; Nash-map tolerance $\eta^2/(16|B|^3)$ and Lipschitz bound $4n|B|^2$. These quantities define conventions, not hypotheses assuming an efficient algorithm or its correctness.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Sections 4.6–4.7 and 5.1–5.2, pp. 19–26 (PDF pp. 19–26)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_SearchProblems
import Definitions.Def_CorrelatedAuctionComplexity_Main_AuctionTransforms

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


/-- Coefficient recurrence D_{r,k}=ℓ_r D_{r-1,k}+t_r D_{r-1,k-1}; out-of-range is zero. -/
def tieStep (row : List ℚ) (q : ℚ × ℚ) : List ℚ :=
  (List.range (row.length+1)).map fun k =>
    q.1 * row.getD k 0 + q.2 * (if k = 0 then 0 else row.getD (k-1) 0)

def tieTable (lt : List (ℚ × ℚ)) : List ℚ := lt.foldl tieStep [1]

noncomputable def edgeUtilityDP {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : H.RatProfile) (e : Fin H.edges.length) (i : N) (b : H.Bid) : ℚ :=
  let others := ((H.edge e).participants.erase i).toList
  let row := tieTable (others.map fun j =>
    (∑ a : H.Bid, if a.val < b.val then p j a else 0,
     ∑ a : H.Bid, if a.val = b.val then p j a else 0))
  (H.value i - b.val) *
    ((List.range row.length).map fun k => row.getD k 0 / (k+1 : ℕ)).sum

def utilityRequest {n : ℕ} (H : HDFPA (Fin n)) (p : H.RatProfile) (i : Fin n) : Bits :=
  encodeNat (encodeH H).length ++ encodeH H ++ encodeNat i.val ++ encodeHProfile H p

/-- Clone profiles use the same lexicographic (bidder,type,bid) ordering as DFPA profiles. -/
def encodeCloneProfile {n : ℕ} (A : DFPA (Fin n)) (p : A.decomposition.RatProfile) : Bits :=
  pack ((List.finRange n).flatMap fun i => (ordered (A.types i)).flatMap fun v =>
    (ordered A.bids).flatMap fun b => ratCode (p ⟨i,v⟩ b))

def forwardRat {n : ℕ} (A : DFPA (Fin n)) (p : A.decomposition.RatProfile) : A.RatProfile :=
  fun i v b => p ⟨i,v⟩ b

def inverseRat {n : ℕ} (A : DFPA (Fin n)) (p : A.RatProfile) : A.decomposition.RatProfile :=
  fun c b => p c.1 c.2 b

/-- The exact accuracy conversions in Sections 4.6 and 5.1. -/
def circuitError (η : ℝ) : ℝ := 6000*η
def normalizedHAccuracy (η : ℚ) : ℚ := η/4
def transferError (ε : ℝ) : ℝ := 121*ε
def normalizedDAccuracy (η : ℚ) : ℚ := η/605

noncomputable def nashMapTolerance (η : ℝ) (bids : ℕ) : ℝ := η^2/(16*(bids:ℝ)^3)
def nashMapLipschitz (n bids : ℕ) : ℝ := 4*(n:ℝ)*(bids:ℝ)^2

end CorrelatedAuctionComplexity.Main


