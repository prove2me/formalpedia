-- Prove2me | Definitions.Def_BS2_b3ba934b_ConditionalOrdinary
-- name    : BS2_b3ba934b_ConditionalOrdinary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:59:46.890002+00:00
-- url     : https://prove2.me/theorems/b75b08a3-5d2c-4ccb-9cc0-bc48e9e885d7
-- title:
--   Sensitivity separation: ConditionalOrdinary (complete source module)
-- statement:
--   Complete Lean source module `ConditionalOrdinary` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ConditionalOrdinary.lean; original SHA-256 f3399d34ca31ad9b4ad9de5a4ab294181bbd230bb91c7ec217c0414e4e592080; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/
import Definitions.Def_BS2_b3ba934b_GradedPositiveBoundary
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def ordinaryStage (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) : Stage L I V where
  Adj := S.Adj
  loopless := S.loopless
  label := S.label
  guard := fun _ => g
  tolerance := fun _ => q
  target := fun _ _ u z => F t u && F t z

def ordinaryParent (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) := parent (ordinaryStage S F t g q) F t

def guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset V :=
  Finset.univ.filter fun w => S.Adj v w ∧ F g (child x w (S.label v w)) = true

def ordinaryRow (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  (∀ c : Bool, F t (child x v c) = true) ∧ (guardFailures S F g x v).card ≤ q

@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩

@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]

theorem guardFailures_mono (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (g g' : L) (h : g' ≤ g)
    (x : ((V × Bool) × I) → Bool) (v : V) :
    guardFailures S F g x v ⊆ guardFailures S F g' x v := by
  intro w hw
  exact (mem_guardFailures S F g' x v w).2
    ⟨(mem_guardFailures S F g x v w).1 hw |>.1,
      hF _ _ h _ ((mem_guardFailures S F g x v w).1 hw).2⟩

theorem ordinary_parent_nested (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti tj gi gj : L) (qi qj : ℕ)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (hq : qj ≤ qi)
    (x : ((V × Bool) × I) → Bool) (hx : ordinaryParent S F tj gj qj x = true) :
    ordinaryParent S F ti gi qi x = true := by
  obtain ⟨v,hts,hcs⟩ := (ordinary_parent_true S F tj gj qj x).1 hx
  apply (ordinary_parent_true S F ti gi qi x).2
  refine ⟨v,fun c => hF _ _ ht _ (hts c), ?_⟩
  exact (Finset.card_le_card (guardFailures_mono S F hF gi gj hg x v)).trans (hcs.trans hq)

/-- A fixed constant-target branch is a subfunction of a graded parent whenever
    that parent admits its guard budget and has no stronger target up to it. -/
theorem ordinary_component_accepts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (l ti gi : L) (q : ℕ)
    (hg : gi ≤ S.guard l) (hq : q ≤ S.tolerance l)
    (ht : ∀ d, d ≤ q → t l d ≤ ti)
    (hgraded : ∀ d u z, S.target l d u z = (F (t l d) u && F (t l d) z))
    (x : ((V × Bool) × I) → Bool) (hx : ordinaryParent S F ti gi q x = true) :
    parent S F l x = true := by
  obtain ⟨v,hts,hcs⟩ := (ordinary_parent_true S F ti gi q x).1 hx
  have hsub : failed S F l x v ⊆ guardFailures S F gi x v := by
    intro w hw
    obtain ⟨_,hr,hf⟩ := Finset.mem_filter.mp hw
    exact (mem_guardFailures S F gi x v w).2 ⟨hr,hF _ _ hg _ hf⟩
  have hc : (failed S F l x v).card ≤ q := (Finset.card_le_card hsub).trans hcs
  apply (parent_true_iff S F l x).2
  refine ⟨v,hc.trans hq,?_⟩
  rw [hgraded]
  simp only [hF _ _ (ht _ hc) _ (hts false),hF _ _ (ht _ hc) _ (hts true),Bool.and_self]

theorem ordinary_component_down_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (l ti gi : L) (q : ℕ)
    (hg : gi ≤ S.guard l) (hq : q ≤ S.tolerance l)
    (ht : ∀ d, d ≤ q → t l d ≤ ti)
    (hgraded : ∀ d u z, S.target l d u z = (F (t l d) u && F (t l d) z))
    (x : ((V × Bool) × I) → Bool) :
    flipsTo (parent S F l) false x ⊆ flipsTo (ordinaryParent S F ti gi q) false x := by
  intro a ha
  have hf := (Finset.mem_filter.mp ha).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  cases hh : ordinaryParent S F ti gi q (flip x {a}) with
  | false => rfl
  | true =>
    have hc := ordinary_component_accepts S F hF t l ti gi q hg hq ht hgraded _ hh
    rw [hf] at hc
    contradiction

/-- The two actual target children contribute the refined conditional cost. -/
theorem targetBits_conditional_card (F : L → (I → Bool) → Bool)
    (ti tj tk : L) (x : ((V × Bool) × I) → Bool) (v : V) (m b : ℕ)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ht : ∀ c : Bool, F tj (child x v c) = true)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false) :
    (targetBits F ti x v).card ≤ max (2*m) (m+b) := by
  have hc : (targetBits F ti x v).card ≤
      (flipsTo (F ti) false (child x v false)).card +
      (flipsTo (F ti) false (child x v true)).card := by
    simpa only [targetBits,card_liftBits] using Finset.card_union_le
      (liftBits v false (flipsTo (F ti) false (child x v false)))
      (liftBits v true (flipsTo (F ti) false (child x v true)))
  cases hf : F tk (child x v false) <;> cases htr : F tk (child x v true)
  · exact hc.trans ((Nat.add_le_add (hm _ (ht false) hf) (hm _ (ht true) htr)).trans
      (by omega))
  · exact hc.trans ((Nat.add_le_add (hm _ (ht false) hf) (hb _ htr)).trans
      (le_max_right _ _))
  · exact hc.trans ((Nat.add_le_add (hb _ hf) (hm _ (ht true) htr)).trans (by omega))
  · obtain ⟨c,hc⟩ := hmiss
    cases c <;> simp_all


def passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset V :=
  outgoing S v \ guardFailures S F g x v

@[simp] theorem mem_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passingGuards S F g x v ↔
      S.Adj v w ∧ F g (child x w (S.label v w)) = false := by
  simp only [passingGuards, outgoing, guardFailures, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases F g (child x w (S.label v w)) <;> simp

theorem card_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (passingGuards S F g x v).card =
      (outgoing S v).card - (guardFailures S F g x v).card := by
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_guardFailures S F g x v w).1 hw |>.1⟩

def ordinaryGuardBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  (passingGuards S F gj x v).biUnion fun w =>
    liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))

theorem ordinaryGuardBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj : L) (x : ((V × Bool) × I) → Bool) (v : V) (a : ℕ)
    (ha : ABound F gj gi a) :
    (ordinaryGuardBits S F gi gj x v).card ≤
      ((outgoing S v).card - (guardFailures S F gj x v).card)*a := by
  unfold ordinaryGuardBits
  calc
    _ ≤ ∑ w ∈ passingGuards S F gj x v,
        (liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ passingGuards S F gj x v, a := by
      apply Finset.sum_le_sum
      intro w hw
      rw [card_liftBits]
      exact ha _ ((mem_passingGuards S F gj x v w).1 hw).2
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, card_passingGuards]

theorem ordinaryGuardBits_card_special (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj gk : L) (x : ((V × Bool) × I) → Bool) (v w : V) (a p : ℕ)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p)
    (hw : w ∈ passingGuards S F gj x v)
    (hk : F gk (child x w (S.label v w)) = true) :
    (ordinaryGuardBits S F gi gj x v).card ≤
      ((outgoing S v).card - (guardFailures S F gj x v).card - 1)*a+p := by
  have hsplit : passingGuards S F gj x v =
      insert w ((passingGuards S F gj x v).erase w) := (Finset.insert_erase hw).symm
  unfold ordinaryGuardBits
  rw [hsplit,Finset.biUnion_insert]
  calc
    _ ≤ (liftBits w (S.label v w)
      (flipsTo (F gi) true (child x w (S.label v w)))).card +
      (((passingGuards S F gj x v).erase w).biUnion fun z =>
        liftBits z (S.label v z) (flipsTo (F gi) true (child x z (S.label v z)))).card :=
      Finset.card_union_le _ _
    _ ≤ p + (((passingGuards S F gj x v).erase w).card*a) := by
      apply Nat.add_le_add
      · rw [card_liftBits]
        exact hp _ hk ((mem_passingGuards S F gj x v w).1 hw).2
      · apply Finset.card_biUnion_le.trans
        calc
          _ ≤ ∑ _z ∈ (passingGuards S F gj x v).erase w, a := by
            apply Finset.sum_le_sum
            intro z hz
            rw [card_liftBits]
            exact ha _ ((mem_passingGuards S F gj x v z).1 (Finset.mem_of_mem_erase hz)).2
          _ = _ := by simp
    _ = _ := by rw [Finset.card_erase_of_mem hw,card_passingGuards]; omega

theorem guardFailures_after_subset_insert (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (gi gj : L) (hg : gj ≤ gi)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    guardFailures S F gi (flip x {((w,c),a)}) v ⊆ insert w (guardFailures S F gj x v) := by
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · have hp : (z,S.label v z) ≠ (w,c) := fun h => hzw (congrArg Prod.fst h)
    obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
    rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact Finset.mem_insert.mpr (Or.inr ((mem_guardFailures S F gj x v z).2
      ⟨hR,hF _ _ hg _ hf⟩))

theorem ordinary_destroying_cover (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (w : V) (c : Bool) (a : I)
    (hoff : ordinaryParent S F ti gi qi (flip x {((w,c),a)}) = false) :
    (w = v ∧ F ti (flip (child x v c) {a}) = false) ∨
      (S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true) := by
  by_cases he : S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true
  · exact Or.inr he
  · have hsub : guardFailures S F gi (flip x {((w,c),a)}) v ⊆ guardFailures S F gj x v := by
      intro z hz
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
      apply (mem_guardFailures S F gj x v z).2
      refine ⟨hR,?_⟩
      by_cases hp : (z,S.label v z) = (w,c)
      · have hzw : z = w := congrArg Prod.fst hp
        have hl : S.label v z = c := congrArg Prod.snd hp
        subst z
        rw [hl,child_flip_same] at hf
        cases hb : F gj (child x w c) with
        | true => simpa only [hl] using hb
        | false => exact False.elim (he ⟨hR,hl,hb,hf⟩)
      · rw [child_flip_other x w z c (S.label v z) a hp] at hf
        exact hF _ _ hg _ hf
    have hc : (guardFailures S F gi (flip x {((w,c),a)}) v).card ≤ qi :=
      (Finset.card_le_card hsub).trans (hv.2.trans hq)
    left
    by_cases hw : w = v
    · subst w
      refine ⟨rfl,?_⟩
      cases hf : F ti (flip (child x v c) {a}) with
      | false => rfl
      | true =>
        have hon : ordinaryParent S F ti gi qi (flip x {((v,c),a)}) = true := by
          apply (ordinary_parent_true S F ti gi qi _).2
          refine ⟨v,?_,hc⟩
          intro e
          by_cases hec : e = c
          · subst e; simpa only [child_flip_same] using hf
          · rw [child_flip_other x v v c e a (fun h => hec (congrArg Prod.snd h))]
            exact hF _ _ ht _ (hv.1 e)
        rw [hoff] at hon
        contradiction
    · have hon : ordinaryParent S F ti gi qi (flip x {((w,c),a)}) = true := by
        apply (ordinary_parent_true S F ti gi qi _).2
        refine ⟨v,?_,hc⟩
        intro e
        rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)]
        exact hF _ _ ht _ (hv.1 e)
      rw [hoff] at hon
      contradiction

theorem ordinary_destroying_subset (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v) :
    flipsTo (ordinaryParent S F ti gi qi) false x ⊆
      targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  rcases ordinary_destroying_cover S F hF ti tj gi gj ht hg qi q hq x v hv w c a hoff with hh | he
  · obtain ⟨hw,hf⟩ := hh
    subst w
    apply Finset.mem_union.mpr
    left
    have hm : a ∈ flipsTo (F ti) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
  · obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passingGuards S F gj x v w).2 ⟨hR,?_⟩,?_⟩
    · simpa only [hl] using hbefore
    · apply (mem_liftBits _ _ _ _ _ _).2
      refine ⟨rfl,hl.symm,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩

/-- Actual guard slack removes all guard-only destruction coordinates. -/
theorem ordinary_destroying_subset_of_slack (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (hslack : (guardFailures S F gj x v).card < qi) :
    flipsTo (ordinaryParent S F ti gi qi) false x ⊆ targetBits F ti x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  have hc : (guardFailures S F gi (flip x {((w,c),a)}) v).card ≤ qi :=
    (Finset.card_le_card (guardFailures_after_subset_insert S F hF gi gj hg x v w c a)).trans
      ((Finset.card_insert_le _ _).trans (by omega))
  by_cases hw : w = v
  · subst w
    have hf : F ti (flip (child x v c) {a}) = false := by
      cases h : F ti (flip (child x v c) {a}) with
      | false => rfl
      | true =>
        have hon : ordinaryParent S F ti gi qi (flip x {((v,c),a)}) = true := by
          apply (ordinary_parent_true S F ti gi qi _).2
          refine ⟨v,?_,hc⟩
          intro e
          by_cases hec : e = c
          · subst e; simpa only [child_flip_same] using h
          · rw [child_flip_other x v v c e a (fun h => hec (congrArg Prod.snd h))]
            exact hF _ _ ht _ (hv.1 e)
        rw [hoff] at hon
        contradiction
    have hm : a ∈ flipsTo (F ti) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
  · have hon : ordinaryParent S F ti gi qi (flip x {((w,c),a)}) = true := by
      apply (ordinary_parent_true S F ti gi qi _).2
      refine ⟨v,?_,hc⟩
      intro e
      rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)]
      exact hF _ _ ht _ (hv.1 e)
    rw [hoff] at hon
    contradiction


/-- An ordinary winner's target-defect boundary uses both child states. -/
theorem ordinary_target_defect_down (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj tk gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false)
    (degree m b a : ℕ) (hdegree : (outgoing S v).card = degree)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b) (ha : ABound F gj gi a) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤
      max (2*m) (m+b) + if qi=q then (degree-q)*a else 0 := by
  have htarget := targetBits_conditional_card F ti tj tk x v m b hm hb hv.1 hmiss
  by_cases hslack : (guardFailures S F gj x v).card < qi
  · have h := (Finset.card_le_card (ordinary_destroying_subset_of_slack
      S F hF ti tj gi gj ht hg qi q hq x v hv hslack)).trans htarget
    exact h.trans (Nat.le_add_right _ _)
  · have he : qi=q := by have hh := hv.2; omega
    have hc : (guardFailures S F gj x v).card = q := by have hh := hv.2; omega
    rw [if_pos he]
    calc
      _ ≤ (targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v).card :=
        Finset.card_le_card (ordinary_destroying_subset S F hF ti tj gi gj ht hg qi q hq x v hv)
      _ ≤ (targetBits F ti x v).card+(ordinaryGuardBits S F gi gj x v).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add htarget (by
        simpa only [hdegree,hc] using ordinaryGuardBits_card_le S F gi gj x v a ha)

/-- In the guard-defect branch one actual guard lies in the conditional gap. -/
theorem ordinary_guard_defect_down (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj tk gi gj gk : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (htk : ∀ c : Bool, F tk (child x v c) = true)
    (hguard : q < (guardFailures S F gk x v).card)
    (degree b a p : ℕ) (hdegree : (outgoing S v).card = degree)
    (hb : BBound F ti tk b) (ha : ABound F gj gi a) (hp : PBound F gk gj gi p) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤
      2*b + if qi=q then (degree-q-1)*a+p else 0 := by
  have htarget := targetBits_card_le F ti tk x v b hb htk
  by_cases hslack : (guardFailures S F gj x v).card < qi
  · have h := (Finset.card_le_card (ordinary_destroying_subset_of_slack
      S F hF ti tj gi gj ht hg qi q hq x v hv hslack)).trans htarget
    exact h.trans (Nat.le_add_right _ _)
  · have he : qi=q := by have hh := hv.2; omega
    have hc : (guardFailures S F gj x v).card = q := by have hh := hv.2; omega
    have hex : ∃ w ∈ guardFailures S F gk x v, w ∉ guardFailures S F gj x v := by
      by_contra hn
      have hsub : guardFailures S F gk x v ⊆ guardFailures S F gj x v := by
        intro w hw
        by_contra hj
        exact hn ⟨w,hw,hj⟩
      have hh := Finset.card_le_card hsub
      omega
    obtain ⟨w,hwk,hwj⟩ := hex
    obtain ⟨hR,hk⟩ := (mem_guardFailures S F gk x v w).1 hwk
    have hj : F gj (child x w (S.label v w)) = false := by
      cases h : F gj (child x w (S.label v w)) with
      | false => rfl
      | true => exact False.elim (hwj ((mem_guardFailures S F gj x v w).2 ⟨hR,h⟩))
    have hw : w ∈ passingGuards S F gj x v := (mem_passingGuards S F gj x v w).2 ⟨hR,hj⟩
    rw [if_pos he]
    calc
      _ ≤ (targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v).card :=
        Finset.card_le_card (ordinary_destroying_subset S F hF ti tj gi gj ht hg qi q hq x v hv)
      _ ≤ (targetBits F ti x v).card+(ordinaryGuardBits S F gi gj x v).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add htarget (by
        simpa only [hdegree,hc] using ordinaryGuardBits_card_special S F gi gj gk x v w a p ha hp hw hk)

/-- Complete improved primitive-M transfer for actual ordinary parent functions. -/
theorem primitiveM (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk gi gj gk : L) (htij : ti ≤ tj) (htjk : tj ≤ tk)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (qi q : ℕ) (hq : q ≤ qi)
    (degree m b a p : ℕ) (hdegree : ∀ v, (outgoing S v).card = degree)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj q x = true)
    (hxk : ordinaryParent S F tk gk q x = false) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤
      max (if tj<tk then max (2*m) (m+b)+(if qi=q then (degree-q)*a else 0) else 0)
        (if gk<gj then 2*b+(if qi=q then (degree-q-1)*a+p else 0) else 0) := by
  obtain ⟨v,hv⟩ := (ordinary_parent_true S F tj gj q x).1 hxj
  by_cases hmiss : ∃ c : Bool, F tk (child x v c) = false
  · have hlt : tj<tk := by
      apply lt_of_le_of_ne htjk
      intro he
      obtain ⟨c,hc⟩ := hmiss
      have hh := hv.1 c
      rw [he,hc] at hh
      contradiction
    exact (ordinary_target_defect_down S F hF ti tj tk gi gj htij hgjgi qi q hq x v hv hmiss
      degree m b a (hdegree v) hm hb ha).trans (by rw [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c : Bool, F tk (child x v c) = true := by
      intro c
      cases h : F tk (child x v c) with
      | false => exact False.elim (hmiss ⟨c,h⟩)
      | true => rfl
    have hg : q < (guardFailures S F gk x v).card := by
      by_contra hn
      have hon := (ordinary_parent_true S F tk gk q x).2 ⟨v,htk,by omega⟩
      rw [hxk] at hon
      contradiction
    have hlt : gk<gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      rw [he] at hg
      have hc := hv.2
      omega
    exact (ordinary_guard_defect_down S F hF ti tj tk gi gj gk htij hgjgi qi q hq x v hv htk hg
      degree b a p (hdegree v) hb ha hp).trans (by rw [if_pos hlt]; exact le_max_right _ _)


def ordinaryRowBool (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (v : V) (x : ((V × Bool) × I) → Bool) : Bool :=
  decide (ordinaryRow S F t g q x v)

@[simp] theorem ordinary_row_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    ordinaryRowBool S F t g q v x = true ↔ ordinaryRow S F t g q x v := by
  simp [ordinaryRowBool]

@[simp] theorem ordinary_row_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    ordinaryRowBool S F t g q v x = false ↔ ¬ordinaryRow S F t g q x v := by
  simp [ordinaryRowBool]

theorem row_destroying_cover (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (w : V) (c : Bool) (a : I)
    (hoff : ordinaryRowBool S F ti gi qi v (flip x {((w,c),a)}) = false) :
    (w = v ∧ F ti (flip (child x v c) {a}) = false) ∨
      (S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true) := by
  by_cases he : S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true
  · exact Or.inr he
  · have hsub : guardFailures S F gi (flip x {((w,c),a)}) v ⊆ guardFailures S F gj x v := by
      intro z hz
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
      apply (mem_guardFailures S F gj x v z).2
      refine ⟨hR,?_⟩
      by_cases hp : (z,S.label v z) = (w,c)
      · have hzw : z = w := congrArg Prod.fst hp
        have hl : S.label v z = c := congrArg Prod.snd hp
        subst z
        rw [hl,child_flip_same] at hf
        cases hb : F gj (child x w c) with
        | true => simpa only [hl] using hb
        | false => exact False.elim (he ⟨hR,hl,hb,hf⟩)
      · rw [child_flip_other x w z c (S.label v z) a hp] at hf
        exact hF _ _ hg _ hf
    have hc : (guardFailures S F gi (flip x {((w,c),a)}) v).card ≤ qi :=
      (Finset.card_le_card hsub).trans (hv.2.trans hq)
    left
    by_cases hw : w = v
    · subst w
      refine ⟨rfl,?_⟩
      cases hf : F ti (flip (child x v c) {a}) with
      | false => rfl
      | true =>
        have hon : ordinaryRowBool S F ti gi qi v (flip x {((v,c),a)}) = true := by
          apply (ordinary_row_true S F ti gi qi _ v).2
          refine ⟨?_,hc⟩
          intro e
          by_cases hec : e = c
          · subst e; simpa only [child_flip_same] using hf
          · rw [child_flip_other x v v c e a (fun h => hec (congrArg Prod.snd h))]
            exact hF _ _ ht _ (hv.1 e)
        rw [hoff] at hon
        contradiction
    · have hon : ordinaryRowBool S F ti gi qi v (flip x {((w,c),a)}) = true := by
        apply (ordinary_row_true S F ti gi qi _ v).2
        refine ⟨?_,hc⟩
        intro e
        rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)]
        exact hF _ _ ht _ (hv.1 e)
      rw [hoff] at hon
      contradiction

theorem row_destroying_subset (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v) :
    flipsTo (ordinaryRowBool S F ti gi qi v) false x ⊆
      targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  rcases row_destroying_cover S F hF ti tj gi gj ht hg qi q hq x v hv w c a hoff with hh | he
  · obtain ⟨hw,hf⟩ := hh
    subst w
    apply Finset.mem_union.mpr
    left
    have hm : a ∈ flipsTo (F ti) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
  · obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passingGuards S F gj x v w).2 ⟨hR,?_⟩,?_⟩
    · simpa only [hl] using hbefore
    · apply (mem_liftBits _ _ _ _ _ _).2
      refine ⟨rfl,hl.symm,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩

/-- Actual guard slack removes all guard-only destruction coordinates. -/
theorem row_destroying_subset_of_slack (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (hslack : (guardFailures S F gj x v).card < qi) :
    flipsTo (ordinaryRowBool S F ti gi qi v) false x ⊆ targetBits F ti x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  have hc : (guardFailures S F gi (flip x {((w,c),a)}) v).card ≤ qi :=
    (Finset.card_le_card (guardFailures_after_subset_insert S F hF gi gj hg x v w c a)).trans
      ((Finset.card_insert_le _ _).trans (by omega))
  by_cases hw : w = v
  · subst w
    have hf : F ti (flip (child x v c) {a}) = false := by
      cases h : F ti (flip (child x v c) {a}) with
      | false => rfl
      | true =>
        have hon : ordinaryRowBool S F ti gi qi v (flip x {((v,c),a)}) = true := by
          apply (ordinary_row_true S F ti gi qi _ v).2
          refine ⟨?_,hc⟩
          intro e
          by_cases hec : e = c
          · subst e; simpa only [child_flip_same] using h
          · rw [child_flip_other x v v c e a (fun h => hec (congrArg Prod.snd h))]
            exact hF _ _ ht _ (hv.1 e)
        rw [hoff] at hon
        contradiction
    have hm : a ∈ flipsTo (F ti) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
  · have hon : ordinaryRowBool S F ti gi qi v (flip x {((w,c),a)}) = true := by
      apply (ordinary_row_true S F ti gi qi _ v).2
      refine ⟨?_,hc⟩
      intro e
      rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)]
      exact hF _ _ ht _ (hv.1 e)
    rw [hoff] at hon
    contradiction


/-- An ordinary winner's target-defect boundary uses both child states. -/
theorem row_target_defect_down (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj tk gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false)
    (degree m b a : ℕ) (hdegree : (outgoing S v).card = degree)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b) (ha : ABound F gj gi a) :
    (flipsTo (ordinaryRowBool S F ti gi qi v) false x).card ≤
      max (2*m) (m+b) + if qi=q then (degree-q)*a else 0 := by
  have htarget := targetBits_conditional_card F ti tj tk x v m b hm hb hv.1 hmiss
  by_cases hslack : (guardFailures S F gj x v).card < qi
  · have h := (Finset.card_le_card (row_destroying_subset_of_slack
      S F hF ti tj gi gj ht hg qi q hq x v hv hslack)).trans htarget
    exact h.trans (Nat.le_add_right _ _)
  · have he : qi=q := by have hh := hv.2; omega
    have hc : (guardFailures S F gj x v).card = q := by have hh := hv.2; omega
    rw [if_pos he]
    calc
      _ ≤ (targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v).card :=
        Finset.card_le_card (row_destroying_subset S F hF ti tj gi gj ht hg qi q hq x v hv)
      _ ≤ (targetBits F ti x v).card+(ordinaryGuardBits S F gi gj x v).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add htarget (by
        simpa only [hdegree,hc] using ordinaryGuardBits_card_le S F gi gj x v a ha)

/-- In the guard-defect branch one actual guard lies in the conditional gap. -/
theorem row_guard_defect_down (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj tk gi gj gk : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (htk : ∀ c : Bool, F tk (child x v c) = true)
    (hguard : q < (guardFailures S F gk x v).card)
    (degree b a p : ℕ) (hdegree : (outgoing S v).card = degree)
    (hb : BBound F ti tk b) (ha : ABound F gj gi a) (hp : PBound F gk gj gi p) :
    (flipsTo (ordinaryRowBool S F ti gi qi v) false x).card ≤
      2*b + if qi=q then (degree-q-1)*a+p else 0 := by
  have htarget := targetBits_card_le F ti tk x v b hb htk
  by_cases hslack : (guardFailures S F gj x v).card < qi
  · have h := (Finset.card_le_card (row_destroying_subset_of_slack
      S F hF ti tj gi gj ht hg qi q hq x v hv hslack)).trans htarget
    exact h.trans (Nat.le_add_right _ _)
  · have he : qi=q := by have hh := hv.2; omega
    have hc : (guardFailures S F gj x v).card = q := by have hh := hv.2; omega
    have hex : ∃ w ∈ guardFailures S F gk x v, w ∉ guardFailures S F gj x v := by
      by_contra hn
      have hsub : guardFailures S F gk x v ⊆ guardFailures S F gj x v := by
        intro w hw
        by_contra hj
        exact hn ⟨w,hw,hj⟩
      have hh := Finset.card_le_card hsub
      omega
    obtain ⟨w,hwk,hwj⟩ := hex
    obtain ⟨hR,hk⟩ := (mem_guardFailures S F gk x v w).1 hwk
    have hj : F gj (child x w (S.label v w)) = false := by
      cases h : F gj (child x w (S.label v w)) with
      | false => rfl
      | true => exact False.elim (hwj ((mem_guardFailures S F gj x v w).2 ⟨hR,h⟩))
    have hw : w ∈ passingGuards S F gj x v := (mem_passingGuards S F gj x v w).2 ⟨hR,hj⟩
    rw [if_pos he]
    calc
      _ ≤ (targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v).card :=
        Finset.card_le_card (row_destroying_subset S F hF ti tj gi gj ht hg qi q hq x v hv)
      _ ≤ (targetBits F ti x v).card+(ordinaryGuardBits S F gi gj x v).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add htarget (by
        simpa only [hdegree,hc] using ordinaryGuardBits_card_special S F gi gj gk x v w a p ha hp hw hk)



/-- Rowwise version needed by the joint strict union transfer. -/
theorem row_primitiveM (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk gi gj gk : L) (htij : ti ≤ tj) (htjk : tj ≤ tk)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (qi q : ℕ) (hq : q ≤ qi)
    (degree m b a p : ℕ) (hdegree : ∀ v, (outgoing S v).card = degree)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (hxj : ordinaryRow S F tj gj q x v)
    (hxk : ¬ordinaryRow S F tk gk q x v) :
    (flipsTo (ordinaryRowBool S F ti gi qi v) false x).card ≤
      max (if tj<tk then max (2*m) (m+b)+(if qi=q then (degree-q)*a else 0) else 0)
        (if gk<gj then 2*b+(if qi=q then (degree-q-1)*a+p else 0) else 0) := by
  by_cases hmiss : ∃ c : Bool, F tk (child x v c) = false
  · have hlt : tj<tk := by
      apply lt_of_le_of_ne htjk
      intro he
      obtain ⟨c,hc⟩ := hmiss
      have hh := hxj.1 c
      rw [he,hc] at hh
      contradiction
    exact (row_target_defect_down S F hF ti tj tk gi gj htij hgjgi qi q hq x v hxj hmiss
      degree m b a (hdegree v) hm hb ha).trans (by rw [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c : Bool, F tk (child x v c) = true := by
      intro c
      cases h : F tk (child x v c) with
      | false => exact False.elim (hmiss ⟨c,h⟩)
      | true => rfl
    have hg : q < (guardFailures S F gk x v).card := by
      by_contra hn
      exact hxk ⟨htk,by omega⟩
    have hlt : gk<gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      rw [he] at hg
      have hc := hxj.2
      omega
    exact (row_guard_defect_down S F hF ti tj tk gi gj gk htij hgjgi qi q hq x v hxj htk hg
      degree b a p (hdegree v) hb ha hp).trans (by rw [if_pos hlt]; exact le_max_right _ _)

end
end ThreeBoundConditional

#print axioms ThreeBoundConditional.primitiveM
#print axioms ThreeBoundConditional.ordinary_component_down_subset


