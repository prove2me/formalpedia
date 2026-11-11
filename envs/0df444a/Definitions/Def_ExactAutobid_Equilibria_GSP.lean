-- Prove2me | Definitions.Def_ExactAutobid_Equilibria_GSP
-- name    : ExactAutobid_Equilibria_GSP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:05.874575+00:00
-- url     : https://prove2.me/theorems/ad0b633e-4578-4c68-9cb7-a041abee829e
-- title:
--   Budget- and ROI-constrained GSP equilibria (Definitions 2.2, 2.3) with canonical and prescribed caps, and their search problems
-- statement:
--   The GSP sponsored-shopping model is the published `AutobiddingGSP.Approximation.Auction`: bidder $i$ owns a catalog of goods with values $v_{ij} > 0$ and bids $\alpha_i v_{ij}$; goods are ranked by nonincreasing bid (every such order is valid); a good's per-click price is the bid of the first later good owned by a different bidder (**no self-pricing**), or $0$; position $k$ has click-through rate $c_k$. For a distribution $\pi$ over orders valid at $\alpha$, $V_i$ and $P_i$ are the expected value and payment.
--
--   A **budget-constrained GSP equilibrium** (Definition 2.2) is $(\alpha, \pi)$ with $0 \le \alpha_i \le 1$, $P_i \le B_i$, $P_i < B_i \Rightarrow \alpha_i = 1$ (the published `IsApproxABEB` at $\gamma = 0$). An **ROI-constrained GSP equilibrium with cap $A$** (Definition 2.3) is $(\alpha, \pi)$ with
--   $$1 \le \alpha_i \le A,\qquad P_i \le V_i,\qquad P_i < V_i \Longrightarrow \alpha_i = A;$$
--   with the canonical instance-defined cap $A_0 = 1 + \sum_{i,j} v_{ij} / \min v_{ij}$ this is the published `IsApproxABER` at $\gamma = 0$, and `IsROIGSPEqCap` states it for any cap, used for prescribed caps $A > 1$ fixed independently of the auction.
--
--   The real search problems `budgetGSPProblemOn`, `roiGSPCanonicalProblemOn`, `roiGSPCapProblemOn A` have the auctions satisfying the published standing assumptions (`Auction.ValidFor`; positive budgets, or no budgets) and a predicate $R$ as instances; a **solution is a multiplier vector $\alpha$ for which some distribution $\pi$ over valid orders makes $(\alpha,\pi)$ an equilibrium**. The **restricted class** `UnitFullBounded c`: full display ($K$ equals the number of goods), unit click-through rates, every bidder owns at most $c$ goods. The polynomial-support variants require $\pi$ supported on at most $p(|\langle I\rangle|)$ orders; the input-cap variant takes the pair (auction, rational $A > 1$) as instance. A **witness** for polynomial-time computation is a list of rational multipliers and a finite weighted list of rankings.
--
--   **Formalization Note.** Auctions are binary encoded over `Sym`; a distribution over all $M!$ orders cannot be a coordinate block of fixed dimension, which is why the solution vector is $\alpha$ (as in [HLN26] and the published `ABERealSearch`).
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), §2.1, p. 4, Definitions 2.2, 2.3; Theorem 1.1(ii)–(iii), p. 2; Lemma A.1, p. 57

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_Search

namespace ExactAutobid.Equilibria

open OnlineCRS.Combine FixpReciprocal AutobiddingGSP.Approximation

/-- Binary encoding over `Sym` of a GSP sponsored-shopping auction: each bidder's catalog values,
the number `K` of slots, the click-through rates and the budgets. -/
def encGSP (A : Auction) : List Sym :=
  fList (fList fRat) A.vals ++ fNat A.K ++ fList fRat A.ctr ++ fList fRat A.budgets

theorem encGSP_prefixFree : PrefixFree encGSP := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ s t h
  simp only [encGSP, List.append_assoc] at h
  obtain ⟨h1, k1⟩ := fRat_prefixFree.fList.fList h
  obtain ⟨h2, k2⟩ := fNat_prefixFree k1
  obtain ⟨h3, k3⟩ := fRat_prefixFree.fList k2
  obtain ⟨h4, k4⟩ := fRat_prefixFree.fList k3
  subst h1 h2 h3 h4
  exact ⟨rfl, k4⟩

theorem encGSP_injective : Function.Injective encGSP := encGSP_prefixFree.injective

/-- **ROI-constrained GSP equilibrium with ROI target one and a cap `A`** (Definition 2.3, (2.3)):
`α ∈ [1, A]^n`, `π` a probability distribution over orders valid at `α`, and for every bidder
`P_i ≤ V_i` and `P_i < V_i ⟹ α_i = A`, with the no-self-pricing GSP expected payment and value
of the published model.

Huang, Liu, Yan, *On the Complexity of Exact Autobidding Equilibria*, arXiv:2611.04475
(sha256 270d1b74…), §2.1, p. 4, Definition 2.3 (with any cap; the prescribed caps `A > 1` are fixed
independently of the auction). -/
def IsROIGSPEqCap (Au : Auction) (A : ℝ) (α : Fin Au.n → ℝ) (π : Au.Alloc → ℝ) : Prop :=
  (∀ i, 1 ≤ α i ∧ α i ≤ A) ∧ Au.IsDist π ∧ (∀ a, 0 < π a → Au.IsValidAlloc α a) ∧
    (∀ i, Au.expPayment α π i ≤ Au.expValue π i) ∧
    ∀ i, Au.expPayment α π i < Au.expValue π i → α i = A

/-- The budget-model instances: the standing assumptions `Auction.WellFormed` of the published
model and one positive budget per bidder. -/
def BudgetInstance (Au : Auction) : Prop := Au.ValidFor Model.budget false

/-- The ROI-model instances: `Auction.WellFormed` and no budgets. -/
def ROIInstance (Au : Auction) : Prop := Au.ValidFor Model.roi false

/-- **The restricted GSP class of Theorem 1.1(ii)–(iii)** with bound `c`: full display (`K = M`),
unit click-through rates, and every bidder owns at most `c` goods. -/
def UnitFullBounded (c : ℕ) (Au : Auction) : Prop :=
  Au.K = Au.vals.flatten.length ∧ (∀ q ∈ Au.ctr, q = 1) ∧ ∀ l ∈ Au.vals, l.length ≤ c

/-- The size of the support of a distribution over orders. -/
noncomputable def supportSize (Au : Auction) (π : Au.Alloc → ℝ) : ℕ :=
  (Finset.univ.filter (fun a => π a ≠ 0)).card

/-- **A GSP equilibrium search problem**: the instances are the auctions satisfying `P`; a solution
of an auction is a multiplier vector `α` for which **some** distribution `π` over orders makes
`(α, π)` an equilibrium in the sense of `E` (Definitions 2.2, 2.3). -/
def gspProblemOn (P : Auction → Prop)
    (E : (Au : Auction) → (Fin Au.n → ℝ) → (Au.Alloc → ℝ) → Prop) : RealSearch where
  Inst := {Au : Auction // P Au}
  enc := fun I => encGSP I.1
  enc_injective := fun _ _ h => Subtype.ext (encGSP_injective h)
  dim := fun I => I.1.n
  Sol := fun I => {α | ∃ π, E I.1 α π}

/-- **A GSP equilibrium search problem with polynomial support**: as `gspProblemOn P E`, but a
solution `α` must come with an equilibrium distribution `π` supported on at most `p(|enc I|)`
orders. -/
def gspSuppProblemOn (P : Auction → Prop)
    (E : (Au : Auction) → (Fin Au.n → ℝ) → (Au.Alloc → ℝ) → Prop) (p : Polynomial ℕ) :
    RealSearch where
  Inst := {Au : Auction // P Au}
  enc := fun I => encGSP I.1
  enc_injective := fun _ _ h => Subtype.ext (encGSP_injective h)
  dim := fun I => I.1.n
  Sol := fun I => {α | ∃ π, E I.1 α π ∧ supportSize I.1 π ≤ p.eval (encGSP I.1).length}

/-- The exact budget-constrained GSP equilibrium (Definition 2.2): `IsApproxABEB` at `γ = 0`. -/
def budgetEq (Au : Auction) (α : Fin Au.n → ℝ) (π : Au.Alloc → ℝ) : Prop := Au.IsApproxABEB 0 α π

/-- The exact ROI-constrained GSP equilibrium with the canonical cap `A₀ = 1 + Σ v / min v`
(Definition 2.3 with the cap of [HLN26]): `IsApproxABER` at `γ = 0`. -/
def roiCanonicalEq (Au : Auction) (α : Fin Au.n → ℝ) (π : Au.Alloc → ℝ) : Prop :=
  Au.IsApproxABER 0 α π

/-- **Exact budget-constrained no-self-pricing GSP equilibrium** on the budget instances
satisfying `R`. -/
def budgetGSPProblemOn (R : Auction → Prop) : RealSearch :=
  gspProblemOn (fun Au => BudgetInstance Au ∧ R Au) budgetEq

/-- **Exact ROI-constrained GSP equilibrium with the canonical instance-defined cap** on the ROI
instances satisfying `R`. -/
def roiGSPCanonicalProblemOn (R : Auction → Prop) : RealSearch :=
  gspProblemOn (fun Au => ROIInstance Au ∧ R Au) roiCanonicalEq

/-- **Exact ROI-constrained GSP equilibrium with a prescribed cap `A`** (a parameter of the problem,
fixed independently of the auction) on the ROI instances satisfying `R`. -/
def roiGSPCapProblemOn (A : ℚ) (R : Auction → Prop) : RealSearch :=
  gspProblemOn (fun Au => ROIInstance Au ∧ R Au) (fun Au α π => IsROIGSPEqCap Au (A : ℝ) α π)

/-- **Prescribed-cap ROI-GSP with polynomial support** (Lemma A.1), on all ROI instances. -/
def roiGSPCapSuppProblem (A : ℚ) (p : Polynomial ℕ) : RealSearch :=
  gspSuppProblemOn ROIInstance (fun Au α π => IsROIGSPEqCap Au (A : ℝ) α π) p

/-- **Prescribed-cap ROI-GSP with the cap as an input** (Lemma A.1, "including when `A` is an
input"): instances are pairs of a ROI auction and a rational cap `A > 1`, encoded as the auction
followed by `A` in binary; a solution `α` comes with an equilibrium `π` of cap `A` supported on at
most `p(|enc I|)` orders. -/
def roiGSPInputCapSuppProblem (p : Polynomial ℕ) : RealSearch where
  Inst := {I : Auction × ℚ // ROIInstance I.1 ∧ 1 < I.2}
  enc := fun I => encGSP I.1.1 ++ fRat I.1.2
  enc_injective := by
    rintro ⟨⟨a, q⟩, ha⟩ ⟨⟨b, r⟩, hb⟩ h
    have h' : encGSP a ++ fRat q = encGSP b ++ fRat r := h
    obtain ⟨h1, h2⟩ := encGSP_prefixFree h'
    have h3 := fRat_prefixFree.injective h2
    subst h1 h3
    rfl
  dim := fun I => I.1.1.n
  Sol := fun I => {α | ∃ π, IsROIGSPEqCap I.1.1 (I.1.2 : ℝ) α π ∧
    supportSize I.1.1 π ≤ p.eval (encGSP I.1.1 ++ fRat I.1.2).length}

/-- Binary encoding over `Sym` of a rational equilibrium representation: rational multipliers and a
weighted list of rankings (each ranking a list of (bidder, item index) pairs, as in the published
`Auction.rankList`). -/
def encGSPWitness (w : List ℚ × List (ℚ × List (ℕ × ℕ))) : List Sym :=
  fList fRat w.1 ++ fList (fun e => fRat e.1 ++ fList (fun p => fNat p.1 ++ fNat p.2) e.2) w.2

/-- The witness `(α, ws)` represents a ROI-GSP equilibrium with cap `A` of `Au`: one multiplier per
bidder, every listed ranking is the ranking list of an order, and the induced pair
`(alphaOf α, mixtureOf ws)` satisfies Definition 2.3 with cap `A`. -/
def IsROIGSPCapWitness (Au : Auction) (A : ℝ) (w : List ℚ × List (ℚ × List (ℕ × ℕ))) : Prop :=
  w.1.length = Au.n ∧ (∀ e ∈ w.2, ∃ a : Au.Alloc, e.2 = Au.rankList a) ∧
    IsROIGSPEqCap Au A (Au.alphaOf w.1) (Au.mixtureOf w.2)

end ExactAutobid.Equilibria


