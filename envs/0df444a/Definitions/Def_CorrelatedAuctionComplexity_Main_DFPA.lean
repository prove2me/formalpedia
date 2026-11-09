-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_DFPA
-- name    : CorrelatedAuctionComplexity_Main_DFPA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:19.60204+00:00
-- url     : https://prove2.me/theorems/eee1c821-c7e7-4e65-9dd6-b19e837c900e
-- title:
--   Correlated discrete priors and conditional Bayes–Nash utilities
-- statement:
--   A discrete first-price auction has finitely many bidders, a finite rational bid set $B$ containing zero, and an explicitly listed common prior with distinct rational value vectors and positive rational masses summing to one. Values and bids lie in $[0,R]$. Bidder $i$ observes only her own value, which ranges over the actual marginal support $V_i$.
--
--   Strategies $\beta_i(v_i)$ are real lotteries with no overbidding. Conditional on the full value vector, bidders randomize independently. The conditional utility averages first over the other bidders' independent bids, then over the prior conditioned on $v_i$:
--
--   $$U_i(\beta_i,\beta_{-i};v_i)\ge U_i(b,\beta_{-i};v_i)-\varepsilon\quad(i,\ v_i\in V_i,\ b\in B).$$
--
--   Pure deviations test every bid, including overbids; all bidders remain in the auction and uniform ties. Positive marginal mass justifies conditioning. The bundle includes scaling and merging coinciding prior atoms, together with rational computational profiles distinct from real mathematical profiles.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Definition 3 and Section 3.1, pp. 8–9 (PDF pp. 8–9)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_FiniteAuction

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


structure PriorAtom (N : Type) where
  value : N → ℚ
  mass : ℚ

structure DFPA (N : Type) where
  bids : Finset ℚ
  prior : List (PriorAtom N)

namespace DFPA
variable {N : Type} [Fintype N] [DecidableEq N]

def WellFormed (A : DFPA N) (bound : ℚ) : Prop :=
  Nonempty N ∧ 0 ∈ A.bids ∧
  (∀ b ∈ A.bids, 0 ≤ b ∧ b ≤ bound) ∧
  (A.prior.map PriorAtom.value).Nodup ∧
  (∀ d ∈ A.prior, 0 < d.mass ∧ ∀ i, 0 ≤ d.value i ∧ d.value i ≤ bound) ∧
  (A.prior.map PriorAtom.mass).sum = 1

/-- Types are exactly the supported marginal values, rather than arbitrary declared lists. -/
def types (A : DFPA N) (i : N) : Finset ℚ := (A.prior.map fun d => d.value i).toFinset
abbrev Bid (A : DFPA N) := {b // b ∈ A.bids}
abbrev TypeAt (A : DFPA N) (i : N) := {v // v ∈ A.types i}
abbrev Profile (A : DFPA N) := ∀ i, A.TypeAt i → A.Bid → ℝ
abbrev RatProfile (A : DFPA N) := ∀ i, A.TypeAt i → A.Bid → ℚ

def Legal (A : DFPA N) (β : A.Profile) : Prop :=
  ∀ i v, IsLottery (β i v) ∧ ∀ b, v.val < b.val → β i v b = 0

def Pure (A : DFPA N) (β : A.Profile) : Prop :=
  ∀ i v, ∃ b, β i v b = 1 ∧ ∀ a, a ≠ b → β i v a = 0

def atomType (A : DFPA N) (d : Fin A.prior.length) (i : N) : A.TypeAt i :=
  ⟨A.prior[d].value i, by
    simp only [types, List.mem_toFinset, List.mem_map]
    exact ⟨A.prior[d], List.getElem_mem d.isLt, rfl⟩⟩

noncomputable def marginal (A : DFPA N) (i : N) (v : A.TypeAt i) : ℝ :=
  ∑ d : Fin A.prior.length, if A.prior[d].value i = v.val then (A.prior[d].mass : ℝ) else 0

noncomputable def pureUtility (A : DFPA N) (β : A.Profile) (i : N)
    (v : A.TypeAt i) (b : A.Bid) : ℝ :=
  (∑ d : Fin A.prior.length,
    if A.prior[d].value i = v.val then
      (A.prior[d].mass : ℝ) * expectation
        (deviation (fun j => β j (A.atomType d j)) i b)
        (fun a => (singlePayoff Finset.univ A.prior[d].value (fun j => (a j).val) i : ℝ))
    else 0) / A.marginal i v

noncomputable def utility (A : DFPA N) (β : A.Profile) (i : N) (v : A.TypeAt i) : ℝ :=
  ∑ b, β i v b * A.pureUtility β i v b

/-- Pure deviations range over ALL bids, including overbids, exactly as Definition 3. -/
def IsMBNE (A : DFPA N) (ε : ℝ) (β : A.Profile) : Prop :=
  A.Legal β ∧ ∀ i v b, A.pureUtility β i v b - ε ≤ A.utility β i v

noncomputable def realProfile (A : DFPA N) (p : A.RatProfile) : A.Profile :=
  fun i v b => (p i v b : ℝ)

def scale (A : DFPA N) (c : ℚ) : DFPA N where
  bids := A.bids.image (fun b => b / c)
  prior := A.prior.map fun d => ⟨(fun i => d.value i / c), d.mass⟩

/-- Coalesce coinciding value vectors, preserving total mass and all conditional laws. -/
def coalesce (ds : List (PriorAtom N)) : List (PriorAtom N) :=
  ((ds.map PriorAtom.value).eraseDups).map fun v =>
    ⟨v, ((ds.filter fun d => d.value = v).map PriorAtom.mass).sum⟩

end DFPA

end CorrelatedAuctionComplexity.Main


