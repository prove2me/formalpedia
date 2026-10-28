-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualPrefixCaps
-- name    : BS2_b3ba934b_ActualPrefixCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:28:01.428986+00:00
-- url     : https://prove2.me/theorems/9da9d726-f2b1-4997-82d7-a8239fbd1aa2
-- title:
--   Sensitivity separation: ActualPrefixCaps (complete source module)
-- statement:
--   Complete Lean source module `ActualPrefixCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualPrefixCaps.lean; original SHA-256 15e2833fdff4d4215491198840a2619655a555ecbfb70e9c46e73a4055444e85; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- All prefix-cap ingredients are consequences of actual failed-guard sets
and the separately proved labeling exclusions. -/
import Definitions.Def_BS2_b3ba934b_ResidualSelection
import Definitions.Def_BS2_b3ba934b_MarkedCandidateCaps

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundPrefixCaps
open scoped Classical BigOperators
open TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
open MarkedCandidateCaps ThreeBoundMarkers
noncomputable section
variable {V X : Type} [Fintype V] [DecidableEq V]

def outsideHigh (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H T : Finset V) (q : ℕ) : Finset V :=
  (H \ T).filter fun v => (guardFailures R ell P children v).card ≤ q

def eligibleHigh (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V) (q : ℕ) : Finset V :=
  H.filter fun v => (guardFailures R ell P children v).card ≤ q+1

theorem ordinary_prefix_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (color : V → Bool) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q) :
    T.card ≤ min (a-1-(outsideHigh R ell P children H T q).card)
      (a-(outsideHigh R ell P children H T (q+1)).card) := by
  have hsub (b : ℕ) : outsideHigh R ell P children H T b ⊆ H := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hdis (b : ℕ) : Disjoint T (outsideHigh R ell P children H T b) := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvH
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvH).1).2 hvT
  have hbudget (b : ℕ) : ∀ v ∈ outsideHigh R ell P children H T b,
      (guardFailures R ell P children v).card ≤ b :=
    fun _ hv => (Finset.mem_filter.mp hv).2
  have h₀ := target_plus_high_cap R ell P children T
    (outsideHigh R ell P children H T q) (hdis q) q a hexcl color hpartner
    (fun w hw => hhigh w (hsub q hw)) hT (hbudget q)
  have h₁ := target_plus_extra_high_cap R hR ell P children T
    (outsideHigh R ell P children H T (q+1)) (hdis (q+1)) q a hexcl color hpartner
    (fun w hw => hhigh w (hsub (q+1) hw)) hT (hbudget (q+1))
  omega

theorem marked_prefix_cap (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (T H : Finset V)
    (color : V → Bool) (q m a : ℕ)
    (hm : m ≤ (eligibleHigh R ell P children H q).card)
    (hcap : MarkedCardBound R ell q m (m*(q+1)) a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q) :
    T.card ≤ a-1 + (m-(outsideHigh R ell P children H T (q+1)).card) := by
  have he : eligibleHigh R ell P children H q \ T =
      outsideHigh R ell P children H T (q+1) := by
    ext v
    simp only [eligibleHigh,outsideHigh,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have h := actual_marked_outside_first_cap R ell P children T
    (eligibleHigh R ell P children H q) q m a hm hcap color hpartner
    (fun w hw => hhigh w (Finset.mem_filter.mp hw).1) hT
    (fun _ hv => (Finset.mem_filter.mp hv).2)
  simpa only [he] using h

theorem dominator_prefix_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (color : V → Bool) (vs : List V)
    (hvs : vs.Nodup) (hH : vs.toFinset = H)
    (m a : ℕ) (hm : m ≤ vs.length) (hcap : DominatorCardBound R ell m a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card = 0) :
    T.card ≤ (T ∩ H).card+(a-1)+
      (((vs.map (residual R ell P children H)).mergeSort (· ≤ ·)).take m).sum := by
  have hN := bound_by_sorted_prefix vs hvs (residual R ell P children H)
    m (T \ H).card (a-1) hm (by
      intro M hM hc
      rw [hH] at hM
      exact actual_dominator_residual_cap R hR ell P children (T \ H) H M
        Finset.sdiff_disjoint hM color m a hc hcap
        (fun w hw => hpartner w (Finset.mem_sdiff.mp hw).1) hhigh
        (fun v hv => hT v (Finset.mem_sdiff.mp hv).1))
  have hsplit := Finset.card_sdiff_add_card_inter T H
  omega

theorem zero_marked_prefix_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (color : V → Bool) (vs : List V)
    (hvs : vs.Nodup) (hH : vs.toFinset = H)
    (q m a : ℕ) (hm : m ≤ vs.length) (hmq : m ≤ q+2)
    (hcap : MarkedCardBound R ell q m 0 a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q) :
    T.card ≤ (T ∩ H).card+(a-1)+
      (((vs.map (residual R ell P children H)).mergeSort (· ≤ ·)).take m).sum := by
  have hN := bound_by_sorted_prefix vs hvs (residual R ell P children H)
    m (T \ H).card (a-1) hm (by
      intro M hM hc
      rw [hH] at hM
      exact actual_zero_marked_residual_cap R hR ell P children (T \ H) H M
        Finset.sdiff_disjoint hM color q m a hc hmq hcap
        (fun w hw => hpartner w (Finset.mem_sdiff.mp hw).1) hhigh
        (fun v hv => hT v (Finset.mem_sdiff.mp hv).1))
  have hsplit := Finset.card_sdiff_add_card_inter T H
  omega

end
end ThreeBoundPrefixCaps

#print axioms ThreeBoundPrefixCaps.ordinary_prefix_cap
#print axioms ThreeBoundPrefixCaps.marked_prefix_cap
#print axioms ThreeBoundPrefixCaps.dominator_prefix_cap
#print axioms ThreeBoundPrefixCaps.zero_marked_prefix_cap


