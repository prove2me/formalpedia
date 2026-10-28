-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxLocal
-- name    : BS2_b3ba934b_MinmaxLocal
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:58:28.714971+00:00
-- url     : https://prove2.me/theorems/7e214517-ec6f-4d8f-a0f7-4daf72a23497
-- title:
--   Sensitivity separation: MinmaxLocal (complete source module)
-- statement:
--   Complete Lean source module `MinmaxLocal` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All theorem statements and proof steps are retained. Local import paths and the recorded campaign flip references are fully qualified for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions. Five references to the campaign coordinate-flip operation are explicitly qualified as OAI.Paper320.flip, avoiding an ambiguity under the platform's full Mathlib imports; the referenced operation and theorem statements are unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxLocal.lean; original SHA-256 d6ef1ef454889b213ab6af1d585ba6694aa7af2c1d7c826454bbbbb1c08bb9b7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Unconditional local lemmas for the graded min/max sensitivity transfer.

This file proves actual predicates and actual one-coordinate-flip identities.
It does not assume a sensitivity-transfer theorem or a recursive seed theorem.
The exact rank is defined from the finite nested family, rather than supplied
as an unproved rank oracle.
-/
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MinmaxLocal
open scoped Classical

variable {N : ℕ} {X J I : Type}

/-- A family indexed by `Fin N` is nested from weak to strong. -/
def Nested (F : Fin N → X → Prop) : Prop :=
  ∀ i j : Fin N, i ≤ j → ∀ x : X, F j x → F i x

/-- The number one larger than the largest accepted predicate index;
    zero denotes the all-false state. -/
noncomputable def height (F : Fin N → X → Prop) (x : X) : ℕ := by
  classical
  exact Finset.univ.sup fun i : Fin N => if F i x then i.val + 1 else 0

/-- The exact rank, with `-1` for the all-false state. -/
noncomputable def rank (F : Fin N → X → Prop) (x : X) : ℤ :=
  (height F x : ℤ) - 1

theorem height_le (F : Fin N → X → Prop) (x : X) : height F x ≤ N := by
  classical
  unfold height
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega

/-- Nesting makes the true predicate indices an initial segment. -/
theorem holds_iff_lt_height (F : Fin N → X → Prop) (hF : Nested F)
    (x : X) (i : Fin N) : F i x ↔ i.val < height F x := by
  classical
  constructor
  · intro hi
    have hh := Finset.le_sup (s := (Finset.univ : Finset (Fin N)))
      (f := fun j => if F j x then j.val + 1 else 0) (Finset.mem_univ i)
    simp only [if_pos hi] at hh
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i.val) hh
  · intro hi
    change i.val < Finset.univ.sup (fun j : Fin N => if F j x then j.val + 1 else 0) at hi
    obtain ⟨j, _, hj⟩ := Finset.lt_sup_iff.mp hi
    by_cases htrue : F j x
    · simp only [if_pos htrue] at hj
      exact hF i j (by change i.val ≤ j.val; omega) x htrue
    · simp only [if_neg htrue] at hj
      omega

/-- Exact rank reconstructs every Boolean predicate in the family. -/
theorem holds_iff_le_rank (F : Fin N → X → Prop) (hF : Nested F)
    (x : X) (i : Fin N) : F i x ↔ (i.val : ℤ) ≤ rank F x := by
  rw [holds_iff_lt_height F hF x i]
  unfold rank
  omega

theorem rank_bounds (F : Fin N → X → Prop) (x : X) :
    -1 ≤ rank F x ∧ rank F x < (N : ℤ) := by
  have hh := height_le F x
  unfold rank
  omega

/-- The symmetric target: both weak predicates and at least one strong one. -/
def Target (F : Fin N → X → Prop) (t u : Fin N) (x y : X) : Prop :=
  F t x ∧ F t y ∧ (F u x ∨ F u y)

theorem target_comm (F : Fin N → X → Prop) (t u : Fin N) (x y : X) :
    Target F t u x y ↔ Target F t u y x := by
  unfold Target
  constructor
  · rintro ⟨hx, hy, hu⟩
    exact ⟨hy, hx, hu.symm⟩
  · rintro ⟨hy, hx, hu⟩
    exact ⟨hx, hy, hu.symm⟩

theorem target_mono (F : Fin N → X → Prop) (hF : Nested F)
    (tw uw ts us : Fin N) (ht : tw ≤ ts) (hu : uw ≤ us)
    (x y : X) (hs : Target F ts us x y) : Target F tw uw x y := by
  rcases hs with ⟨hx, hy, hupper⟩
  refine ⟨hF _ _ ht x hx, hF _ _ ht y hy, ?_⟩
  exact hupper.elim (fun hx => Or.inl (hF _ _ hu x hx))
    (fun hy => Or.inr (hF _ _ hu y hy))

theorem target_iff_rank (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (x y : X) :
    Target F t u x y ↔
      (t.val : ℤ) ≤ rank F x ∧ (t.val : ℤ) ≤ rank F y ∧
        ((u.val : ℤ) ≤ rank F x ∨ (u.val : ℤ) ≤ rank F y) := by
  simp only [Target, holds_iff_le_rank F hF]

/-- Exact one-fixed-child target cases, for arbitrary actual child inputs. -/
theorem target_fixed_child_cases (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (htu : t ≤ u) (x y : X) :
    Target F t u x y ↔
      (F u y ∧ F t x) ∨ (F t y ∧ ¬ F u y ∧ F u x) := by
  classical
  constructor
  · rintro ⟨hx, hy, hu⟩
    by_cases hyu : F u y
    · exact Or.inl ⟨hyu, hx⟩
    · exact Or.inr ⟨hy, hyu, hu.resolve_right hyu⟩
  · rintro (⟨hyu, hx⟩ | ⟨hy, _, hxu⟩)
    · exact ⟨hx, hF _ _ htu y hyu, Or.inr hyu⟩
    · exact ⟨hF _ _ htu x hxu, hy, Or.inl hxu⟩

/-- If the fixed child reaches the upper threshold, the other needs only t. -/
theorem target_iff_lower_of_upper_partner (F : Fin N → X → Prop)
    (hF : Nested F) (t u : Fin N) (htu : t ≤ u) (x y : X)
    (hy : F u y) : Target F t u x y ↔ F t x := by
  constructor
  · exact fun h => h.1
  · exact fun hx => ⟨hx, hF _ _ htu y hy, Or.inr hy⟩

/-- If the fixed child is in [t,u), the other must reach u. -/
theorem target_iff_upper_of_gap_partner (F : Fin N → X → Prop)
    (hF : Nested F) (t u : Fin N) (htu : t ≤ u) (x y : X)
    (hyt : F t y) (hyu : ¬ F u y) : Target F t u x y ↔ F u x := by
  constructor
  · exact fun h => h.2.2.resolve_right hyu
  · exact fun hx => ⟨hF _ _ htu x hx, hyt, Or.inl hx⟩

/-- A partner below the lower target prevents every one-child repair. -/
theorem target_false_of_partner_below (F : Fin N → X → Prop)
    (t u : Fin N) (x y : X) (hy : ¬ F t y) : ¬ Target F t u x y :=
  fun h => hy h.2.1

noncomputable def needed (F : Fin N → X → Prop) (t u : Fin N) (y : X) : Fin N := by
  classical
  exact if F u y then t else u

/-- This identity is the source of the inverse-target threshold in the checker. -/
theorem target_iff_needed (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (htu : t ≤ u) (x y : X) :
    Target F t u x y ↔ F t y ∧ F (needed F t u y) x := by
  classical
  by_cases hyu : F u y
  · simp only [needed, if_pos hyu]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, Or.inr hyu⟩
  · simp only [needed, if_neg hyu]
    constructor
    · exact fun h => ⟨h.2.1, h.2.2.resolve_right hyu⟩
    · exact fun h => ⟨hF _ _ htu x h.2, h.1, Or.inl h.2⟩

theorem needed_eq_of_rank_upper (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (y : X) (hy : (u.val : ℤ) ≤ rank F y) :
    needed F t u y = t := by
  classical
  simp only [needed, if_pos ((holds_iff_le_rank F hF y u).2 hy)]

theorem needed_eq_of_rank_below_upper (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (y : X) (hy : rank F y < (u.val : ℤ)) :
    needed F t u y = u := by
  classical
  have hn : ¬ F u y := fun h => (not_le_of_gt hy) ((holds_iff_le_rank F hF y u).1 h)
  simp only [needed, if_neg hn]

/-- Exact repair identity for changing the first child to any other actual input. -/
theorem left_repair_iff (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (htu : t ≤ u) (x x' y : X) :
    (¬ Target F t u x y ∧ Target F t u x' y) ↔
      F t y ∧ ¬ F (needed F t u y) x ∧ F (needed F t u y) x' := by
  rw [target_iff_needed F hF t u htu x y,
    target_iff_needed F hF t u htu x' y]
  constructor
  · rintro ⟨hnot, hy, hx'⟩
    exact ⟨hy, fun hx => hnot ⟨hy, hx⟩, hx'⟩
  · rintro ⟨hy, hx, hx'⟩
    exact ⟨fun h => hx h.2, hy, hx'⟩

theorem left_destruction_iff (F : Fin N → X → Prop) (hF : Nested F)
    (t u : Fin N) (htu : t ≤ u) (x x' y : X) :
    (Target F t u x y ∧ ¬ Target F t u x' y) ↔
      F t y ∧ F (needed F t u y) x ∧ ¬ F (needed F t u y) x' := by
  rw [target_iff_needed F hF t u htu x y,
    target_iff_needed F hF t u htu x' y]
  constructor
  · rintro ⟨⟨hy, hx⟩, hn⟩
    exact ⟨hy, hx, fun hx' => hn ⟨hy, hx'⟩⟩
  · rintro ⟨hy, hx, hx'⟩
    exact ⟨⟨hy, hx⟩, fun h => hx' h.2⟩

section ActualFlips
open OAI.Paper320
variable [Fintype I]

noncomputable def upBits (P : (I → Bool) → Prop) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => ¬ P x ∧ P (_root_.OAI.Paper320.flip x {a})

noncomputable def downBits (P : (I → Bool) → Prop) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => P x ∧ ¬ P (_root_.OAI.Paper320.flip x {a})

noncomputable def leftRepairBits (F : Fin N → (I → Bool) → Prop)
    (t u : Fin N) (x y : I → Bool) : Finset I :=
  upBits (fun z => Target F t u z y) x

noncomputable def leftDestructionBits (F : Fin N → (I → Bool) → Prop)
    (t u : Fin N) (x y : I → Bool) : Finset I :=
  downBits (fun z => Target F t u z y) x

/-- Equality of actual sensitive-coordinate sets, not just a numerical bound. -/
theorem leftRepairBits_eq (F : Fin N → (I → Bool) → Prop) (hF : Nested F)
    (t u : Fin N) (htu : t ≤ u) (x y : I → Bool) :
    leftRepairBits F t u x y =
      if F t y then upBits (F (needed F t u y)) x else ∅ := by
  classical
  ext a
  simp only [leftRepairBits, upBits, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [left_repair_iff F hF t u htu x (_root_.OAI.Paper320.flip x {a}) y]
  by_cases hy : F t y <;> simp [hy]

theorem leftDestructionBits_eq (F : Fin N → (I → Bool) → Prop) (hF : Nested F)
    (t u : Fin N) (htu : t ≤ u) (x y : I → Bool) :
    leftDestructionBits F t u x y =
      if F t y then downBits (F (needed F t u y)) x else ∅ := by
  classical
  ext a
  simp only [leftDestructionBits, downBits, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [left_destruction_iff F hF t u htu x (_root_.OAI.Paper320.flip x {a}) y]
  by_cases hy : F t y <;> simp [hy]

/-- Actual flips cannot simultaneously destroy a weaker predicate and create
    a stronger predicate in the same nested child. -/
theorem down_up_disjoint (F : Fin N → (I → Bool) → Prop) (hF : Nested F)
    (g t : Fin N) (hgt : g ≤ t) (x : I → Bool) :
    Disjoint (downBits (F g) x) (upBits (F t) x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hdown := (Finset.mem_filter.mp ha).2
  have hup := (Finset.mem_filter.mp hb).2
  exact hdown.2 (hF g t hgt (_root_.OAI.Paper320.flip x {a}) hup.2)

/-- The pointwise joint set is bounded both by its own profile allowance
    and by the sum of the separate allowances. -/
theorem joint_card_le_min (A B : Finset I) (p d u : ℕ)
    (hA : A.card ≤ p) (hB : B.card ≤ d) (hU : (A ∪ B).card ≤ u) :
    (A ∪ B).card ≤ min u (p+d) := by
  classical
  apply Nat.le_min.mpr
  exact ⟨hU, (Finset.card_union_le A B).trans (Nat.add_le_add hA hB)⟩

/-- A joint allowance also bounds its upward component. -/
theorem component_card_le_min_joint (A B : Finset I) (p u : ℕ)
    (hA : A.card ≤ p) (hU : (A ∪ B).card ≤ u) : A.card ≤ min p u := by
  classical
  exact Nat.le_min.mpr ⟨hA, (Finset.card_le_card Finset.subset_union_left).trans hU⟩

end ActualFlips

noncomputable def failures (F : Fin N → X → Prop) (g : Fin N)
    (S : Finset J) (z : J → X) : Finset J := by
  classical
  exact S.filter fun a => F g (z a)

theorem failures_subset (F : Fin N → X → Prop) (hF : Nested F)
    (gs gw : Fin N) (hguard : gs ≤ gw) (S : Finset J) (z : J → X) :
    failures F gw S z ⊆ failures F gs S z := by
  classical
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haS, hFa⟩
  exact Finset.mem_filter.mpr ⟨haS, hF gs gw hguard (z a) hFa⟩

def Row (F : Fin N → X → Prop) (t u : ℕ → Fin N)
    (Q d : ℕ) (x y : X) : Prop :=
  d ≤ Q ∧ Target F (t d) (u d) x y

/-- Strong target acceptance and a lower weak guard count imply weak acceptance. -/
theorem row_of_target_and_lower_count (F : Fin N → X → Prop) (hF : Nested F)
    (tw uw : ℕ → Fin N) (htw : Monotone tw) (huw : Monotone uw)
    (ts us : Fin N) (b Q d : ℕ) (hb : b ≤ Q) (hd : d ≤ b)
    (ht : tw b ≤ ts) (hu : uw b ≤ us) (x y : X)
    (hs : Target F ts us x y) : Row F tw uw Q d x y := by
  refine ⟨hd.trans hb, ?_⟩
  exact target_mono F hF _ _ ts us ((htw hd).trans ht) ((huw hd).trans hu) x y hs

/-- For a strong guard candidate, weak-parent rejection forces every strong
    failed guard to be a weak failed guard as well. No transfer is assumed. -/
theorem guard_candidate_failures_eq (F : Fin N → X → Prop) (hF : Nested F)
    (gs gw : Fin N) (hguard : gs ≤ gw) (S : Finset J) (z : J → X)
    (tw uw : ℕ → Fin N) (htw : Monotone tw) (huw : Monotone uw)
    (ts us : Fin N) (b Q : ℕ) (hb : b ≤ Q)
    (ht : tw b ≤ ts) (hu : uw b ≤ us) (x y : X)
    (htarget : Target F ts us x y)
    (hcount : (failures F gs S z).card = b+1)
    (hreject : ¬ Row F tw uw Q (failures F gw S z).card x y) :
    failures F gw S z = failures F gs S z := by
  classical
  have hsub := failures_subset F hF gs gw hguard S z
  have hle := Finset.card_le_card hsub
  have hn : ¬ (failures F gw S z).card ≤ b := by
    intro hd
    exact hreject (row_of_target_and_lower_count F hF tw uw htw huw ts us
      b Q _ hb hd ht hu x y htarget)
  apply Finset.eq_of_subset_of_card_le hsub
  omega

/-- Every incoming guard-repair hit selects a child satisfying the weak guard. -/
theorem guard_hit_eligible (F : Fin N → X → Prop) (hF : Nested F)
    (gs gw : Fin N) (hguard : gs ≤ gw) (S : Finset J) (z : J → X)
    (tw uw : ℕ → Fin N) (htw : Monotone tw) (huw : Monotone uw)
    (ts us : Fin N) (b Q : ℕ) (hb : b ≤ Q)
    (ht : tw b ≤ ts) (hu : uw b ≤ us) (x y : X)
    (htarget : Target F ts us x y)
    (hcount : (failures F gs S z).card = b+1)
    (hreject : ¬ Row F tw uw Q (failures F gw S z).card x y)
    (a : J) (ha : a ∈ S) (hstrong : F gs (z a)) : F gw (z a) := by
  classical
  have heq := guard_candidate_failures_eq F hF gs gw hguard S z tw uw htw huw
    ts us b Q hb ht hu x y htarget hcount hreject
  have hmem : a ∈ failures F gw S z := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨ha, hstrong⟩
  exact (Finset.mem_filter.mp hmem).2

/-- This is precisely the rank eligibility test used in the min/max head oracle. -/
theorem guard_hit_rank_eligible (F : Fin N → X → Prop) (hF : Nested F)
    (gs gw : Fin N) (hguard : gs ≤ gw) (S : Finset J) (z : J → X)
    (tw uw : ℕ → Fin N) (htw : Monotone tw) (huw : Monotone uw)
    (ts us : Fin N) (b Q : ℕ) (hb : b ≤ Q)
    (ht : tw b ≤ ts) (hu : uw b ≤ us) (x y : X)
    (htarget : Target F ts us x y)
    (hcount : (failures F gs S z).card = b+1)
    (hreject : ¬ Row F tw uw Q (failures F gw S z).card x y)
    (a : J) (ha : a ∈ S) (hstrong : F gs (z a)) :
    (gw.val : ℤ) ≤ rank F (z a) := by
  apply (holds_iff_le_rank F hF (z a) gw).1
  exact guard_hit_eligible F hF gs gw hguard S z tw uw htw huw ts us b Q hb
    ht hu x y htarget hcount hreject a ha hstrong

end MinmaxLocal

#print axioms MinmaxLocal.holds_iff_le_rank
#print axioms MinmaxLocal.target_iff_needed
#print axioms MinmaxLocal.leftRepairBits_eq
#print axioms MinmaxLocal.leftDestructionBits_eq
#print axioms MinmaxLocal.down_up_disjoint
#print axioms MinmaxLocal.joint_card_le_min
#print axioms MinmaxLocal.guard_candidate_failures_eq
#print axioms MinmaxLocal.guard_hit_rank_eligible


