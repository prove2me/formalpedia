-- Prove2me | Definitions.Def_BS2_b3ba934b_ResidualCaps
-- name    : BS2_b3ba934b_ResidualCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:03:34.770793+00:00
-- url     : https://prove2.me/theorems/fe2cfec5-26aa-4dcb-a60e-20aad4ea229b
-- title:
--   Sensitivity separation: ResidualCaps (complete source module)
-- statement:
--   Complete Lean source module `ResidualCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ResidualCaps.lean; original SHA-256 ec03db09ea4a2f3cbd1fc6c44684bdf2e0853b238640ccde652c9ebbdb8a911c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Source, double-dominator, and zero-mismatch residual caps for actual graded
target candidates. The residuals are actual failed guards left after all arcs
inside the full high-row tournament have been charged.
-/
import Definitions.Def_BS2_b3ba934b_Q2CandidateTypes

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]

/-- The number of failed guards not forced by outgoing arcs to the high set. -/
def residual (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (H : Finset V) (v : V) : ℕ :=
  (guardFailures R ell guard children v).card - (outNeighbors R H v).card

def deletedHeads (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : Finset V :=
  M.biUnion (mismatch R ell A color)

def cleanedHeads (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : Finset V :=
  A \ deletedHeads R ell A M color

/-- This is the common exact-cardinality consequence of the source and
    double-dominator exclusions: m=1 is a source, m=2 is a double dominator. -/
def DominatorCardBound (R : V → V → Prop) (ell : V → V → Bool) (m a : ℕ) : Prop :=
  ∀ (A M : Finset V) (color : V → Bool), Disjoint A M → M.card = m →
    (∀ v ∈ M, ∀ w ∈ A, R v w) →
    (∀ v ∈ A ∪ M, (mismatch R ell A color v).card = 0) → A.card < a

/-- The marked exclusions used by the q2 generator all use an empty positive
    marker set; every marker therefore has the extra unit of budget. -/
def MarkedGood (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (q B : ℕ) (color : V → Bool) : Prop :=
  (∀ v ∈ A, (mismatch R ell A color v).card + (outNeighbors R M v).card ≤ q) ∧
  (∀ v ∈ M, (outNeighbors R M v).card + (mismatch R ell A color v).card ≤ q+1) ∧
  (∑ v ∈ M, (mismatch R ell A color v).card) ≤ B

def MarkedCardBound (R : V → V → Prop) (ell : V → V → Bool)
    (q m B a : ℕ) : Prop :=
  ∀ (A M : Finset V) (color : V → Bool), Disjoint A M → M.card = m →
    MarkedGood R ell A M q B color → A.card < a

theorem mismatch_card_le_residual (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H) (color : V → Bool)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c)) (v : V) :
    (mismatch R ell A color v).card ≤ residual R ell guard children H v := by
  have h := charges_card_le_actual_failures R ell guard children A H hdis color hpartner hhigh v
  unfold residual
  omega

theorem deletedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : deletedHeads R ell A M color ⊆ A := by
  intro w hw
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hw
  exact (Finset.mem_filter.mp hv).1

theorem cleanedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : cleanedHeads R ell A M color ⊆ A :=
  Finset.sdiff_subset

theorem cleaned_plus_deleted (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) :
    (cleanedHeads R ell A M color).card + (deletedHeads R ell A M color).card = A.card :=
  Finset.card_sdiff_add_card_eq_card (deletedHeads_subset R ell A M color)

theorem marker_clean_mismatch_empty (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) (v : V) (hv : v ∈ M) :
    mismatch R ell (cleanedHeads R ell A M color) color v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwC,hvw,hcolor⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwA,hwD⟩ := Finset.mem_sdiff.mp hwC
  exact hwD (Finset.mem_biUnion.mpr
    ⟨v,hv,Finset.mem_filter.mpr ⟨hwA,hvw,hcolor⟩⟩)

theorem deleted_card_le_sum_residual (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H) (color : V → Bool)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c)) :
    (deletedHeads R ell A M color).card ≤ ∑ v ∈ M, residual R ell guard children H v := by
  calc
    _ ≤ ∑ v ∈ M, (mismatch R ell A color v).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun v _ =>
      mismatch_card_le_residual R ell guard children A H hdis color hpartner hhigh v

/-- A zero-budget target row cannot point to any high row. Thus every high
    row dominates the zero-budget negative target set. -/
theorem high_dominates_zero_candidates (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v ∈ A, (guardFailures R ell guard children v).card = 0) :
    ∀ v ∈ H, ∀ w ∈ A, R v w := by
  intro v hv w hw
  have hne : v ≠ w := by
    intro he
    subst w
    exact Finset.disjoint_left.mp hdis hw hv
  apply (hR.orient v w hne).mpr
  intro hwv
  have hmem : v ∈ guardFailures R ell guard children w :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwv,hhigh v hv (ell w v)⟩
  have hpos := Finset.card_pos.mpr ⟨v,hmem⟩
  rw [hzero w hw] at hpos
  omega

/-- Deleting the mismatching heads of any selected high markers costs at most
    their total residual and leaves a valid dominated coherent set. This gives
    the source and double residual caps by taking one or two markers. -/
theorem actual_dominator_residual_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (m a : ℕ) (hM : M.card = m)
    (hcap : DominatorCardBound R ell m a)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v ∈ A, (guardFailures R ell guard children v).card = 0) :
    A.card ≤ a-1 + ∑ v ∈ M, residual R ell guard children H v := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hdisCM : Disjoint C M := hdis.mono hCA hMH
  have hdom := high_dominates_zero_candidates R hR ell guard children A H hdis hhigh hzero
  have hgoodA : OrdinaryGood R ell A 0 color := by
    apply ordinaryGood_of_actual_guards R ell guard children A 0 color hpartner
    intro v hv
    exact le_of_eq (hzero v hv)
  have hgoodC : OrdinaryGood R ell C 0 color := ordinaryGood_mono R ell C A hCA 0 color hgoodA
  have hcoherent : ∀ v ∈ C ∪ M, (mismatch R ell C color v).card = 0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvC | hvM
    · exact Nat.eq_zero_of_le_zero (hgoodC v hvC)
    · rw [marker_clean_mismatch_empty R ell A M color v hvM]
      rfl
  have hC := hcap C M color hdisCM hM
    (fun v hv w hw => hdom v (hMH hv) w (hCA hw)) hcoherent
  have hsum := deleted_card_le_sum_residual R ell guard children A H M hdis hMH color hpartner hhigh
  have htotal := cleaned_plus_deleted R ell A M color
  change C.card + (deletedHeads R ell A M color).card = A.card at htotal
  omega

theorem outNeighbors_card_le_pred (R : V → V → Prop) (hR : IsTournament R)
    (M : Finset V) (v : V) (hv : v ∈ M) : (outNeighbors R M v).card ≤ M.card-1 := by
  have hsub : outNeighbors R M v ⊆ M.erase v := by
    intro w hw
    obtain ⟨hwM,hvw⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_erase.mpr
    refine ⟨?_,hwM⟩
    intro he
    subst w
    exact hR.loopless v hvw
  have h := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem hv] at h

/-- Zeroing all selected-marker mismatches gives a marked configuration even
    when the original markers have larger global guard budgets. Only the
    number of selected markers matters for their internal outdegrees. -/
theorem cleaned_marked_zero (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (q : ℕ) (hsize : M.card ≤ q+2)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤ q) :
    MarkedGood R ell (cleanedHeads R ell A M color) M q 0 color := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hzero : ∀ v ∈ M, (mismatch R ell C color v).card = 0 := by
    intro v hv
    rw [marker_clean_mismatch_empty R ell A M color v hv]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (charges_card_le_actual_failures R ell guard children C M (hdis.mono hCA hMH)
      color (fun w hw => hpartner w (hCA hw)) (fun w hw => hhigh w (hMH hw)) v).trans
      (hbudget v (hCA hv))
  · intro v hv
    rw [hzero v hv, Nat.add_zero]
    have h := outNeighbors_card_le_pred R hR M v hv
    omega
  · have hz : (∑ v ∈ M, (mismatch R ell C color v).card) = 0 :=
      Finset.sum_eq_zero (fun v hv => hzero v hv)
    exact hz.le

/-- This yields the q1/three-marker and q2/four-marker zero-mismatch caps
    after adding the separately counted positive prefix. -/
theorem actual_zero_marked_residual_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (q m a : ℕ) (hM : M.card = m) (hm : m ≤ q+2)
    (hcap : MarkedCardBound R ell q m 0 a)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤ q) :
    A.card ≤ a-1 + ∑ v ∈ M, residual R ell guard children H v := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hg := cleaned_marked_zero R hR ell guard children A H M hdis hMH color q
    (by omega) hpartner hhigh hbudget
  have hC := hcap C M color (hdis.mono hCA hMH) hM hg
  have hsum := deleted_card_le_sum_residual R ell guard children A H M hdis hMH color hpartner hhigh
  have htotal := cleaned_plus_deleted R ell A M color
  change C.card + (deletedHeads R ell A M color).card = A.card at htotal
  omega

end
end ResidualCaps

#print axioms ResidualCaps.mismatch_card_le_residual
#print axioms ResidualCaps.high_dominates_zero_candidates
#print axioms ResidualCaps.actual_dominator_residual_cap
#print axioms ResidualCaps.cleaned_marked_zero
#print axioms ResidualCaps.actual_zero_marked_residual_cap


