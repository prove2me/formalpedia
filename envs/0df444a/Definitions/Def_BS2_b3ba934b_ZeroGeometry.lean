-- Prove2me | Definitions.Def_BS2_b3ba934b_ZeroGeometry
-- name    : BS2_b3ba934b_ZeroGeometry
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:25:45.358771+00:00
-- url     : https://prove2.me/theorems/e4237d13-d698-4532-b4bb-36e8c9c16cf6
-- title:
--   Sensitivity separation: ZeroGeometry (complete source module)
-- statement:
--   Complete Lean source module `ZeroGeometry` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. Original declarations and proof bodies are retained, with local import paths rewritten and residual references explicitly qualified as ResidualCaps.residual to avoid the Mathlib topology name collision. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ZeroGeometry.lean; original SHA-256 4ddca2d9fdb0fdbc9fd95d9a5472ae93fca7af1ab241987d9595270d3fde30de; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact zero-tolerance geometry: all internal high arcs are charged, and
   deleting only genuinely hit negative heads gives the sharp marker caps. -/
import Definitions.Def_BS2_b3ba934b_ResidualCaps
import Definitions.Def_BS2_b3ba934b_GlobalAccounting

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundZeroGeometry
open TournamentHighRows CandidateCoherence ResidualCaps
open scoped Classical BigOperators
noncomputable section
variable {V X : Type} [Fintype V]

theorem arcs_card_eq_sum_out (R : V → V → Prop) (H : Finset V) :
    (arcs R H).card = ∑ v∈H, (outNeighbors R H v).card := by
  have hd : (H : Set V).PairwiseDisjoint
      (fun v => ({v} : Finset V).product (outNeighbors R H v)) := by
    intro v hv w hw hn
    apply Finset.disjoint_left.mpr
    rintro ⟨z,a⟩ hzv hzw
    have hvz : z=v := Finset.mem_singleton.mp (Finset.mem_product.mp hzv).1
    have hwz : z=w := Finset.mem_singleton.mp (Finset.mem_product.mp hzw).1
    exact hn (hvz.symm.trans hwz)
  rw [arcs_eq_union_rows]
  calc
    (H.biUnion (fun v => ({v} : Finset V).product (outNeighbors R H v))).card
        = ∑ v∈H, (({v} : Finset V).product (outNeighbors R H v)).card :=
      Finset.card_biUnion hd
    _ = ∑ v∈H, (outNeighbors R H v).card := by simp

theorem cleaned_zero_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H) (color : V → Bool)
    (m a : ℕ) (hm : m≤H.card) (hcap : DominatorCardBound R ell m a)
    (hpartner : ∀ w∈A, ∀ c : Bool, c≠color w → guard (children w c))
    (hhigh : ∀ w∈H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v∈A, (guardFailures R ell guard children v).card=0) :
    A.card≤a-1+(deletedHeads R ell A H color).card := by
  obtain ⟨M,hMH,hM⟩ := Finset.exists_subset_card_eq hm
  let C := cleanedHeads R ell A H color
  have hCA : C⊆A := cleanedHeads_subset R ell A H color
  have hdom := high_dominates_zero_candidates R hR ell guard children A H hdis hhigh hzero
  have hgA : OrdinaryGood R ell A 0 color := by
    apply ordinaryGood_of_actual_guards R ell guard children A 0 color hpartner
    intro v hv
    exact le_of_eq (hzero v hv)
  have hgC := ordinaryGood_mono R ell C A hCA 0 color hgA
  have hcoherent : ∀ v∈C∪M, (mismatch R ell C color v).card=0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Nat.eq_zero_of_le_zero (hgC v hv)
    · rw [marker_clean_mismatch_empty R ell A H color v (hMH hv)]
      rfl
  have hb := hcap C M color (hdis.mono hCA hMH) hM
    (fun v hv w hw => hdom v (hMH hv) w (hCA hw)) hcoherent
  have he := cleaned_plus_deleted R ell A H color
  change C.card+(deletedHeads R ell A H color).card=A.card at he
  omega

theorem residual_sum_identity (R : V → V → Prop)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (H G : Finset V) (hGH : G⊆H)
    (hhigh : ∀ w∈H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v∈H, (guardFailures R ell guard children v).card = if v∈G then 1 else 0) :
    (∑ v∈H, _root_.ResidualCaps.residual R ell guard children H v)+(arcs R H).card=G.card := by
  rw [arcs_card_eq_sum_out,← Finset.sum_add_distrib]
  have he : (∑ v∈H, (_root_.ResidualCaps.residual R ell guard children H v+(outNeighbors R H v).card)) =
      ∑ v∈H, (if v∈G then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hle := Finset.card_le_card (out_high_subset_failures R ell guard children H hhigh v)
    simpa only [_root_.ResidualCaps.residual,Nat.sub_add_cancel hle] using hbudget v hv
  rw [he]
  have hfilter : H.filter (fun v => v∈G)=G := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hv => ⟨hGH hv,hv⟩⟩
  rw [← Finset.card_filter,hfilter]

theorem residual_budget_identity (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (H G : Finset V) (hGH : G⊆H)
    (hhigh : ∀ w∈H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v∈H, (guardFailures R ell guard children v).card = if v∈G then 1 else 0) :
    2*(∑ v∈H, _root_.ResidualCaps.residual R ell guard children H v)+H.card*(H.card-1)=2*G.card := by
  have he := residual_sum_identity R ell guard children H G hGH hhigh hbudget
  have ha := twice_arcs_card R hR H
  have ha' : 2*(arcs R H).card=H.card*(H.card-1) := by
    simpa only [Nat.mul_sub_left_distrib,Nat.mul_one] using ha
  omega

end
end ThreeBoundZeroGeometry

#print axioms ThreeBoundZeroGeometry.cleaned_zero_cap
#print axioms ThreeBoundZeroGeometry.residual_budget_identity


