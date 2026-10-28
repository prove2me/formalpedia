-- Prove2me | Definitions.Def_BS2_b3ba934b_CandidateCoherence
-- name    : BS2_b3ba934b_CandidateCoherence
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:00:21.212978+00:00
-- url     : https://prove2.me/theorems/7354ef14-9787-44ca-a911-6991a906cbfb
-- title:
--   Sensitivity separation: CandidateCoherence (complete source module)
-- statement:
--   Complete Lean source module `CandidateCoherence` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/CandidateCoherence.lean; original SHA-256 c389062dc583cd307e3b5ebc46a8b3f3386215560a89a02cd6a0b7f6300c678f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/
import Definitions.Def_BS2_b3ba934b_TournamentHighRows

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}

/-- A successful repair of either actual private child implies geometric
    one-child repairability of the initial target pair. -/
theorem geometric_of_one_child_repair (F : Fin N → X → Prop)
    (t u : Fin N) (x y : X)
    (hrepair : (∃ x', ¬ Target F t u x y ∧ Target F t u x' y) ∨
      (∃ y', ¬ Target F t u x y ∧ Target F t u x y')) : F t x ∨ F t y := by
  rcases hrepair with ⟨x',_,hx'⟩ | ⟨y',_,hy'⟩
  · exact Or.inr hx'.2.1
  · exact Or.inl hy'.1

/-- Choose the position opposite an accepted lower-target child. -/
noncomputable def targetColor (F : Fin N → X → Prop) (t : V → Fin N)
    (children : V → Bool → X) (v : V) : Bool := by
  classical
  exact if F (t v) (children v false) then true else false

theorem nonchosen_target_true (F : Fin N → X → Prop) (t : V → Fin N)
    (children : V → Bool → X) (v : V)
    (hgeom : F (t v) (children v false) ∨ F (t v) (children v true))
    (b : Bool) (hb : b ≠ targetColor F t children v) : F (t v) (children v b) := by
  classical
  by_cases hleft : F (t v) (children v false)
  · simp only [targetColor, if_pos hleft] at hb
    cases b
    · exact hleft
    · exact False.elim (hb rfl)
  · have hright := hgeom.resolve_left hleft
    simp only [targetColor, if_neg hleft] at hb
    cases b
    · exact False.elim (hb rfl)
    · exact hright

theorem nonchosen_guard_true (F : Fin N → X → Prop) (hF : Nested F)
    (g : Fin N) (t : V → Fin N) (children : V → Bool → X) (v : V)
    (hgt : g ≤ t v)
    (hgeom : F (t v) (children v false) ∨ F (t v) (children v true))
    (b : Bool) (hb : b ≠ targetColor F t children v) : F g (children v b) :=
  hF g (t v) hgt _ (nonchosen_target_true F t children v hgeom b hb)

/-- In a negative target candidate, any guard-false child is the chosen color. -/
theorem guard_false_forces_color (F : Fin N → X → Prop) (hF : Nested F)
    (g : Fin N) (t : V → Fin N) (children : V → Bool → X) (v : V)
    (hgt : g ≤ t v)
    (hgeom : F (t v) (children v false) ∨ F (t v) (children v true))
    (b : Bool) (hb : ¬ F g (children v b)) : b = targetColor F t children v := by
  classical
  by_contra hne
  exact hb (nonchosen_guard_true F hF g t children v hgt hgeom b hne)

noncomputable def mismatch (R : V → V → Prop) (ell : V → V → Bool)
    (T : Finset V) (color : V → Bool) (v : V) : Finset V := by
  classical
  exact T.filter fun w => R v w ∧ ell v w ≠ color w

def OrdinaryGood (R : V → V → Prop) (ell : V → V → Bool)
    (T : Finset V) (q : ℕ) (color : V → Bool) : Prop :=
  ∀ v ∈ T, (mismatch R ell T color v).card ≤ q

/-- An exact-size ordinary exclusion, in the same coloring semantics as the
    accepted labeling construction. -/
def NoOrdinary (R : V → V → Prop) (ell : V → V → Bool) (q a : ℕ) : Prop :=
  ∀ T : Finset V, T.card = a → ∀ color : V → Bool, ¬ OrdinaryGood R ell T q color

theorem mismatch_mono (R : V → V → Prop) (ell : V → V → Bool)
    (T U : Finset V) (hTU : T ⊆ U) (color : V → Bool) (v : V) :
    mismatch R ell T color v ⊆ mismatch R ell U color v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hw⟩
  exact Finset.mem_filter.mpr ⟨hTU hwT,hw⟩

theorem ordinaryGood_mono (R : V → V → Prop) (ell : V → V → Bool)
    (T U : Finset V) (hTU : T ⊆ U) (q : ℕ) (color : V → Bool)
    (hU : OrdinaryGood R ell U q color) : OrdinaryGood R ell T q color := by
  intro v hv
  exact (Finset.card_le_card (mismatch_mono R ell T U hTU color v)).trans (hU v (hTU hv))

theorem ordinary_card_lt (R : V → V → Prop) (ell : V → V → Bool)
    (q a : ℕ) (hexcl : NoOrdinary R ell q a)
    (T : Finset V) (color : V → Bool) (hT : OrdinaryGood R ell T q color) : T.card < a := by
  classical
  by_contra hn
  have ha : a ≤ T.card := Nat.le_of_not_gt hn
  obtain ⟨U,hUT,hUa⟩ := Finset.exists_subset_card_eq ha
  exact hexcl U hUa color (ordinaryGood_mono R ell U T hUT q color hT)

section ActualGuards
variable [Fintype V]

/-- Each label mismatch enters the actual selected-child failure set. -/
theorem mismatch_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b)) (v : V) :
    mismatch R ell T color v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hvw,hlabel⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,hvw,hpartner w hwT (ell v w) hlabel⟩

/-- Actual guard budgets imply ordinary coherence for any partner-valid coloring. -/
theorem ordinaryGood_of_actual_guards (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (q : ℕ) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b))
    (hbudget : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q) :
    OrdinaryGood R ell T q color := by
  intro v hv
  exact (Finset.card_le_card (mismatch_subset_failures R ell P children T color hpartner v)).trans
    (hbudget v hv)

/-- The ordinary target-prefix cap holds with different graded thresholds at
    different rows; no fixed-target assumption is used. -/
theorem geometric_candidates_coherent (F : Fin N → X → Prop) (hF : Nested F)
    (R : V → V → Prop) (ell : V → V → Bool) (g : Fin N)
    (t : V → Fin N) (children : V → Bool → X) (T : Finset V) (q : ℕ)
    (hgt : ∀ v ∈ T, g ≤ t v)
    (hgeom : ∀ v ∈ T, F (t v) (children v false) ∨ F (t v) (children v true))
    (hbudget : ∀ v ∈ T, (guardFailures R ell (F g) children v).card ≤ q) :
    OrdinaryGood R ell T q (targetColor F t children) := by
  apply ordinaryGood_of_actual_guards R ell (F g) children T q (targetColor F t children)
  · intro w hw b hb
    exact nonchosen_guard_true F hF g t children w (hgt w hw) (hgeom w hw) b hb
  · exact hbudget

theorem geometric_candidates_card_lt (F : Fin N → X → Prop) (hF : Nested F)
    (R : V → V → Prop) (ell : V → V → Bool) (g : Fin N)
    (t : V → Fin N) (children : V → Bool → X) (T : Finset V) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a)
    (hgt : ∀ v ∈ T, g ≤ t v)
    (hgeom : ∀ v ∈ T, F (t v) (children v false) ∨ F (t v) (children v true))
    (hbudget : ∀ v ∈ T, (guardFailures R ell (F g) children v).card ≤ q) :
    T.card < a := by
  apply ordinary_card_lt R ell q a hexcl T (targetColor F t children)
  exact geometric_candidates_coherent F hF R ell g t children T q hgt hgeom hbudget

/-- Adjoin disjoint high rows of the same failure budget using arbitrary
    colors on those rows. This is the first strengthened prefix cap. -/
theorem target_plus_high_cap (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (hdisjoint : Disjoint T H) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b))
    (hhigh : ∀ w ∈ H, ∀ b : Bool, P (children w b))
    (hbudgetT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q)
    (hbudgetH : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ q) :
    T.card + H.card < a := by
  classical
  let extended : V → Bool := fun w => if w ∈ T then color w else false
  have hp : ∀ w ∈ T ∪ H, ∀ b : Bool, b ≠ extended w → P (children w b) := by
    intro w hw b hb
    by_cases hwT : w ∈ T
    · have hn : b ≠ color w := by simpa only [extended, if_pos hwT] using hb
      exact hpartner w hwT b hn
    · exact hhigh w ((Finset.mem_union.mp hw).resolve_left hwT) b
  have hb : ∀ v ∈ T ∪ H, (guardFailures R ell P children v).card ≤ q := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (hbudgetT v) (hbudgetH v)
  have hgood := ordinaryGood_of_actual_guards R ell P children (T ∪ H) q extended hp hb
  have hcard := ordinary_card_lt R ell q a hexcl (T ∪ H) extended hgood
  rwa [Finset.card_union_of_disjoint hdisjoint] at hcard

end ActualGuards
end CandidateCoherence

#print axioms CandidateCoherence.geometric_of_one_child_repair
#print axioms CandidateCoherence.guard_false_forces_color
#print axioms CandidateCoherence.mismatch_subset_failures
#print axioms CandidateCoherence.geometric_candidates_card_lt
#print axioms CandidateCoherence.target_plus_high_cap


