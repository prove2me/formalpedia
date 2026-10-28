-- Prove2me | Definitions.Def_BS2_b3ba934b_GradedPositiveBoundary
-- name    : BS2_b3ba934b_GradedPositiveBoundary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:58:45.511136+00:00
-- url     : https://prove2.me/theorems/b4031979-b220-45aa-b975-33bf516ef49c
-- title:
--   Sensitivity separation: GradedPositiveBoundary (complete source module)
-- statement:
--   Complete Lean source module `GradedPositiveBoundary` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GradedPositiveBoundary.lean; original SHA-256 6d85f6c7ba65c7b083899b73aafdf9256265e82b0d8bcdb147fb371d8519a028; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/
import Definitions.Def_BS2_b3ba934b_RecursiveLowerBounds
import Definitions.Def_BS2_b3ba934b_ProfileClosures
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def ExtraFailure (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) : Prop :=
  S.Adj v w ∧ S.label v w = c ∧
    F (S.guard j) (child x w c) = false ∧
    F (S.guard i) (flip (child x w c) {a}) = true

/-- Outside the changed child, every new weak failure was an old strong failure. -/
theorem failed_after_subset_insert (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤ S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    failed S F i (flip x {((w,c),a)}) v ⊆ insert w (failed S F j x v) := by
  classical
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · apply Finset.mem_insert.mpr
    right
    rcases Finset.mem_filter.mp hz with ⟨_, hR, hf⟩
    have hp : (z, S.label v z) ≠ (w,c) := fun h => hzw (congrArg Prod.fst h)
    rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR, hF _ _ hg _ hf⟩

/-- If no previously passing guard is activated, the old strong count suffices. -/
theorem failed_after_subset_of_no_extra (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤ S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (he : ¬ ExtraFailure S F i j x v w c a) :
    failed S F i (flip x {((w,c),a)}) v ⊆ failed S F j x v := by
  classical
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨_, hR, hf⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hR, ?_⟩
  by_cases hp : (z, S.label v z) = (w,c)
  · have hzw : z = w := congrArg Prod.fst hp
    have hl : S.label v z = c := congrArg Prod.snd hp
    subst z
    rw [hl, child_flip_same] at hf
    cases hb : F (S.guard j) (child x w c) with
    | true => simpa only [hl] using hb
    | false => exact False.elim (he ⟨hR, hl, hb, hf⟩)
  · rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact hF _ _ hg _ hf

theorem failed_after_card_le_add_one (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤ S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    (failed S F i (flip x {((w,c),a)}) v).card ≤ (failed S F j x v).card + 1 := by
  classical
  exact (Finset.card_le_card (failed_after_subset_insert S F hF i j hg x v w c a)).trans
    (Finset.card_insert_le _ _)

/-- A row survives whenever both children reach a safe target at an upper guard count. -/
theorem parent_true_of_count_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (l : L)
    (ht : Monotone (t l))
    (hgraded : ∀ d u z, S.target l d u z = (F (t l d) u && F (t l d) z))
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hdQ : d ≤ S.tolerance l) (hcount : (failed S F l x v).card ≤ d)
    (hx : F (t l d) (child x v false) = true)
    (hy : F (t l d) (child x v true) = true) : parent S F l x = true := by
  apply (parent_true_iff S F l x).2
  refine ⟨v, hcount.trans hdQ, ?_⟩
  rw [hgraded]
  simp only [hF _ _ (ht hcount) _ hx, hF _ _ (ht hcount) _ hy, Bool.and_self]

/-- A bit that destroys the weak parent either destroys its own private target
    or activates one selected guard that was passing for the strong row. -/
theorem destroying_flip_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (i j : L)
    (ht : Monotone (t i)) (hg : S.guard j ≤ S.guard i)
    (hgraded : ∀ d u z, S.target i d u z = (F (t i d) u && F (t i d) z))
    (x : ((V × Bool) × I) → Bool) (v : V)
    (d : ℕ) (hd : (failed S F j x v).card = d)
    (hdQ : d ≤ S.tolerance i) (htij : t i d ≤ t j d)
    (hstrong : ∀ c : Bool, F (t j d) (child x v c) = true)
    (w : V) (c : Bool) (a : I)
    (hoff : parent S F i (flip x {((w,c),a)}) = false) :
    (w = v ∧ F (t i d) (flip (child x v c) {a}) = false) ∨
      ExtraFailure S F i j x v w c a := by
  classical
  by_cases he : ExtraFailure S F i j x v w c a
  · exact Or.inr he
  · left
    have hcount : (failed S F i (flip x {((w,c),a)}) v).card ≤ d := by
      rw [← hd]
      exact Finset.card_le_card (failed_after_subset_of_no_extra S F hF i j hg x v w c a he)
    have hweak : ∀ e : Bool, F (t i d) (child x v e) = true :=
      fun e => hF _ _ htij _ (hstrong e)
    by_cases hw : w = v
    · subst w
      refine ⟨rfl, ?_⟩
      cases hf : F (t i d) (flip (child x v c) {a}) with
      | false => rfl
      | true =>
          have htargets : ∀ e : Bool,
              F (t i d) (child (flip x {((v,c),a)}) v e) = true := by
            intro e
            by_cases hec : e = c
            · subst e
              simpa only [child_flip_same] using hf
            · have hp : (v,e) ≠ (v,c) := fun h => hec (congrArg Prod.snd h)
              simpa only [child_flip_other x v v c e a hp] using hweak e
          have hon := parent_true_of_count_bound S F hF t i ht hgraded _ v d hdQ hcount
            (htargets false) (htargets true)
          rw [hoff] at hon
          contradiction
    · have htargets : ∀ e : Bool,
          F (t i d) (child (flip x {((w,c),a)}) v e) = true := by
        intro e
        have hp : (v,e) ≠ (w,c) := fun h => hw (congrArg Prod.fst h).symm
        simpa only [child_flip_other x w v c e a hp] using hweak e
      have hon := parent_true_of_count_bound S F hF t i ht hgraded _ v d hdQ hcount
        (htargets false) (htargets true)
      rw [hoff] at hon
      contradiction

/-- An available next graded branch prevents every guard-only destroying flip. -/
theorem no_guard_destruction_of_next_branch (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (t : L → ℕ → L) (i j : L)
    (ht : Monotone (t i)) (hg : S.guard j ≤ S.guard i)
    (hgraded : ∀ d u z, S.target i d u z = (F (t i d) u && F (t i d) z))
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hd : (failed S F j x v).card = d)
    (hdQ : d+1 ≤ S.tolerance i) (htij : t i (d+1) ≤ t j d)
    (hstrong : ∀ c : Bool, F (t j d) (child x v c) = true)
    (w : V) (c : Bool) (a : I) (hw : w ≠ v) :
    parent S F i (flip x {((w,c),a)}) = true := by
  have hcount := failed_after_card_le_add_one S F hF i j hg x v w c a
  rw [hd] at hcount
  apply parent_true_of_count_bound S F hF t i ht hgraded _ v (d+1) hdQ hcount
  · have hp : (v,false) ≠ (w,c) := fun h => hw (congrArg Prod.fst h).symm
    rw [child_flip_other x w v c false a hp]
    exact hF _ _ htij _ (hstrong false)
  · have hp : (v,true) ≠ (w,c) := fun h => hw (congrArg Prod.fst h).symm
    rw [child_flip_other x w v c true a hp]
    exact hF _ _ htij _ (hstrong true)

def childEmbedding (v : V) (c : Bool) : I ↪ ((V × Bool) × I) :=
  ⟨fun a => ((v,c),a), fun _ _ h => congrArg Prod.snd h⟩

def liftBits (v : V) (c : Bool) (s : Finset I) : Finset ((V × Bool) × I) :=
  s.map (childEmbedding v c)

@[simp] theorem mem_liftBits (v w : V) (c e : Bool) (a : I) (s : Finset I) :
    ((w,e),a) ∈ liftBits v c s ↔ w = v ∧ e = c ∧ a ∈ s := by
  unfold liftBits
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    change ((v,c),b) = ((w,e),a) at he
    have hvw := congrArg (fun p => p.1.1) he
    have hce := congrArg (fun p => p.1.2) he
    have hba : b = a := congrArg Prod.snd he
    exact ⟨hvw.symm,hce.symm,hba ▸ hb⟩
  · rintro ⟨rfl,rfl,ha⟩
    exact ⟨a,ha,rfl⟩

@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

def outgoing (S : Stage L I V) (v : V) : Finset V :=
  Finset.univ.filter (S.Adj v)

def passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset V :=
  outgoing S v \ failed S F j x v

@[simp] theorem mem_passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passing S F j x v ↔
      S.Adj v w ∧ F (S.guard j) (child x w (S.label v w)) = false := by
  simp only [passing, outgoing, failed, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases F (S.guard j) (child x w (S.label v w)) <;> simp

theorem card_passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (passing S F j x v).card = (outgoing S v).card - (failed S F j x v).card := by
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.1⟩

def targetBits (F : L → (I → Bool) → Bool) (t : L)
    (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  liftBits v false (flipsTo (F t) false (child x v false)) ∪
    liftBits v true (flipsTo (F t) false (child x v true))

def guardBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  (passing S F j x v).biUnion fun w =>
    liftBits w (S.label v w) (flipsTo (F (S.guard i)) true (child x w (S.label v w)))

theorem targetBits_card_le (F : L → (I → Bool) → Bool) (ti tj : L)
    (x : ((V × Bool) × I) → Bool) (v : V) (b : ℕ)
    (hb : BBound F ti tj b) (hstrong : ∀ c : Bool, F tj (child x v c) = true) :
    (targetBits F ti x v).card ≤ 2*b := by
  calc
    (targetBits F ti x v).card ≤
        (flipsTo (F ti) false (child x v false)).card +
        (flipsTo (F ti) false (child x v true)).card := by
      simpa only [targetBits, card_liftBits] using Finset.card_union_le
        (liftBits v false (flipsTo (F ti) false (child x v false)))
        (liftBits v true (flipsTo (F ti) false (child x v true)))
    _ ≤ b+b := Nat.add_le_add (hb _ (hstrong false)) (hb _ (hstrong true))
    _ = 2*b := by omega

theorem guardBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (v : V) (a : ℕ)
    (ha : ABound F (S.guard j) (S.guard i) a) :
    (guardBits S F i j x v).card ≤
      ((outgoing S v).card - (failed S F j x v).card)*a := by
  unfold guardBits
  calc
    _ ≤ ∑ w ∈ passing S F j x v,
        (liftBits w (S.label v w)
          (flipsTo (F (S.guard i)) true (child x w (S.label v w)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ passing S F j x v, a := by
      apply Finset.sum_le_sum
      intro w hw
      rw [card_liftBits]
      exact ha _ ((mem_passing S F j x v w).mp hw).2
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, card_passing]

theorem destroying_bits_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (i j : L)
    (ht : Monotone (t i)) (hg : S.guard j ≤ S.guard i)
    (hgraded : ∀ d u z, S.target i d u z = (F (t i d) u && F (t i d) z))
    (x : ((V × Bool) × I) → Bool) (v : V)
    (d : ℕ) (hd : (failed S F j x v).card = d)
    (hdQ : d ≤ S.tolerance i) (htij : t i d ≤ t j d)
    (hstrong : ∀ c : Bool, F (t j d) (child x v c) = true) :
    flipsTo (parent S F i) false x ⊆
      targetBits F (t i d) x v ∪ guardBits S F i j x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  rcases destroying_flip_cover S F hF t i j ht hg hgraded x v d hd hdQ htij hstrong w c a hoff with
    hh | he
  · rcases hh with ⟨hw,hf⟩
    subst w
    apply Finset.mem_union.mpr
    left
    have hfmem : a ∈ flipsTo (F (t i d)) false (child x v c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hfmem⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hfmem⟩))
  · apply Finset.mem_union.mpr
    right
    rcases he with ⟨hR,hl,hbefore,hafter⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w, (mem_passing S F j x v w).2 ⟨hR,?_⟩, ?_⟩
    · simpa only [hl] using hbefore
    · apply (mem_liftBits _ _ _ _ _ _).2
      refine ⟨rfl,hl.symm,?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hl] using hafter⟩

/-- Exact per-winning-row graded B bound, with guard destruction omitted when
    the next weak branch already accepts the strong targets. -/
theorem graded_positive_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (i j : L)
    (ht : Monotone (t i)) (hg : S.guard j ≤ S.guard i)
    (hgraded : ∀ d u z, S.target i d u z = (F (t i d) u && F (t i d) z))
    (x : ((V × Bool) × I) → Bool) (v : V)
    (d : ℕ) (hd : (failed S F j x v).card = d)
    (hdQ : d ≤ S.tolerance i) (htij : t i d ≤ t j d)
    (hstrong : ∀ c : Bool, F (t j d) (child x v c) = true)
    (a b : ℕ) (ha : ABound F (S.guard j) (S.guard i) a)
    (hb : BBound F (t i d) (t j d) b) :
    (flipsTo (parent S F i) false x).card ≤
      2*b + if d+1 ≤ S.tolerance i ∧ t i (d+1) ≤ t j d then 0
        else ((outgoing S v).card-d)*a := by
  classical
  by_cases hsafe : d+1 ≤ S.tolerance i ∧ t i (d+1) ≤ t j d
  · rw [if_pos hsafe, Nat.add_zero]
    apply (Finset.card_le_card (show flipsTo (parent S F i) false x ⊆
      targetBits F (t i d) x v from ?_)).trans (targetBits_card_le F _ _ x v b hb hstrong)
    intro p hp
    rcases p with ⟨⟨w,c⟩,k⟩
    have hoff := (Finset.mem_filter.mp hp).2
    rcases destroying_flip_cover S F hF t i j ht hg hgraded x v d hd hdQ htij hstrong w c k hoff with
      hh | he
    · rcases hh with ⟨hw,hf⟩
      subst w
      have hfmem : k ∈ flipsTo (F (t i d)) false (child x v c) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
      cases c
      · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hfmem⟩))
      · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hfmem⟩))
    · have hw : w ≠ v := by
        intro heq
        subst w
        exact S.loopless v he.1
      have hon := no_guard_destruction_of_next_branch S F hF t i j ht hg hgraded
        x v d hd hsafe.1 hsafe.2 hstrong w c k hw
      rw [hoff] at hon
      contradiction
  · rw [if_neg hsafe]
    calc
      _ ≤ (targetBits F (t i d) x v ∪ guardBits S F i j x v).card :=
        Finset.card_le_card (destroying_bits_subset S F hF t i j ht hg hgraded
          x v d hd hdQ htij hstrong)
      _ ≤ (targetBits F (t i d) x v).card + (guardBits S F i j x v).card :=
        Finset.card_union_le _ _
      _ ≤ 2*b + ((outgoing S v).card-d)*a := by
        apply Nat.add_le_add (targetBits_card_le F _ _ x v b hb hstrong)
        simpa only [hd] using guardBits_card_le S F i j x v a ha

def rawB (S : Stage L I V) (t : L → ℕ → L) (i j : L)
    (degree a : ℕ) (b : ℕ → ℕ) : ℕ :=
  (Finset.range (S.tolerance j+1)).sup fun d =>
    2*b d + if d+1 ≤ S.tolerance i ∧ t i (d+1) ≤ t j d then 0 else (degree-d)*a

/-- The numerical graded rawB formula is sound for the concrete parent family.
    Its inputs are semantic child A/B bounds, not an assumed parent estimate. -/
theorem graded_pair_B_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (i j : L)
    (ht : Monotone (t i)) (hg : S.guard j ≤ S.guard i)
    (hq : S.tolerance j ≤ S.tolerance i)
    (hij : ∀ d, d ≤ S.tolerance j → t i d ≤ t j d)
    (hgradedi : ∀ d u z, S.target i d u z = (F (t i d) u && F (t i d) z))
    (hgradedj : ∀ d u z, S.target j d u z = (F (t j d) u && F (t j d) z))
    (degree a : ℕ) (b : ℕ → ℕ) (hdegree : ∀ v, (outgoing S v).card = degree)
    (ha : ABound F (S.guard j) (S.guard i) a)
    (hb : ∀ d, d ≤ S.tolerance j → BBound F (t i d) (t j d) (b d)) :
    BBound (parent S F) i j (rawB S t i j degree a b) := by
  intro x hx
  obtain ⟨v,hcount,hwin⟩ := (parent_true_iff S F j x).1 hx
  let d := (failed S F j x v).card
  have hdQ : d ≤ S.tolerance j := hcount
  have hstrong : ∀ c : Bool, F (t j d) (child x v c) = true := by
    rw [hgradedj] at hwin
    have hp : F (t j d) (child x v false) = true ∧
        F (t j d) (child x v true) = true := by simpa using hwin
    intro c
    cases c
    · exact hp.1
    · exact hp.2
  have hbound := graded_positive_bound S F hF t i j ht hg hgradedi
    x v d rfl (hdQ.trans hq) (hij d hdQ) hstrong a (b d) ha (hb d hdQ)
  rw [hdegree v] at hbound
  apply hbound.trans
  apply Finset.le_sup (f := fun e =>
    2*b e + if e+1 ≤ S.tolerance i ∧ t i (e+1) ≤ t j e then 0 else (degree-e)*a)
  exact Finset.mem_range.mpr (by omega)

end
end ThreeBoundPositive

#print axioms ThreeBoundPositive.destroying_flip_cover
#print axioms ThreeBoundPositive.no_guard_destruction_of_next_branch
#print axioms ThreeBoundPositive.graded_positive_bound
#print axioms ThreeBoundPositive.graded_pair_B_bound


