-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxUnionRows
-- name    : BS2_b3ba934b_MinmaxUnionRows
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:36:35.076102+00:00
-- url     : https://prove2.me/theorems/e3abe697-2ffc-40af-a6ac-65d20b8003d5
-- title:
--   Sensitivity separation: MinmaxUnionRows (complete source module)
-- statement:
--   Complete Lean source module `MinmaxUnionRows` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxUnionRows.lean; original SHA-256 17418b5cf872e53082d9dd2b05e88be630d509b641c2c942139c347192a0fef8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact unions of destruction and repair bits for oriented min/max rows. -/
import Definitions.Def_BS2_b3ba934b_MinmaxMParent
import Definitions.Def_BS2_b3ba934b_StrictUnion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped BigOperators Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem oriented_implies_ordinary (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t u g : L) (htu : t ≤ u) (q : ℕ)
    (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (h : orientedRow S F t u g q x v c) : ordinaryRow S F t g q x v := by
  refine ⟨?_,h.2.2⟩
  intro e
  cases c <;> cases e <;> first | exact h.1 | exact hF _ _ htu _ h.2.1

theorem oriented_union_subset (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (G : (((V × Bool) × I) → Bool) → Bool)
    (ti ui tl gi gl : L) (htiu : ti ≤ ui) (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (haccept : ∀ y, orientedRow S F ti ui gi 0 y v c → G y=true) :
    flipsTo G false x ∪ flipsTo (ordinaryParent S F tl gl 0) true x ⊆
      flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪
        flipsTo (ordinaryRowBool S F tl gl 0 v) true x := by
  intro bit hbit
  rcases Finset.mem_union.mp hbit with hd | hu
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(oriented_row_false S F ti ui gi 0 v c _).2 ?_⟩
    intro hr
    have hh := haccept _ hr
    rw [(Finset.mem_filter.mp hd).2] at hh
    contradiction
  · obtain ⟨w,hw⟩ := (ordinary_parent_true S F tl gl 0 _).1 (Finset.mem_filter.mp hu).2
    by_cases he : w=v
    · subst w
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(ordinary_row_true S F tl gl 0 _ v).2 hw⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,(oriented_row_false S F ti ui gi 0 v c _).2 ?_⟩
      intro hr
      exact zero_rows_incompatible S hT F hF ti tl gi gl hgil hgli _ v w (Ne.symm he)
        (oriented_implies_ordinary S F hF ti ui gi htiu 0 _ v c hr) hw

theorem oriented_union_weighted (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui gi : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (hv : orientedRow S F ti ui gi 0 x v c)
    (Ulo Uhi : Finset ((V × Bool) × I)) (W : V → Finset ((V × Bool) × I))
    (E : Finset ((V × Bool) × I))
    (hlo : liftBits v (!c) (flipsTo (F ti) false (child x v (!c))) ⊆ Ulo)
    (hhi : liftBits v c (flipsTo (F ui) false (child x v c)) ⊆ Uhi)
    (hg : ∀ w ∈ outgoing S v,
      liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w))) ⊆ W w)
    (he : E ⊆ Ulo ∪ Uhi ∪ (outgoing S v).biUnion W)
    (ulo uhi : ℕ) (z : V → ℕ) (hUlo : Ulo.card ≤ ulo) (hUhi : Uhi.card ≤ uhi)
    (hW : ∀ w ∈ outgoing S v, (W w).card ≤ z w) :
    (flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪ E).card ≤
      ulo+uhi+∑ w ∈ outgoing S v, z w := by
  have hsub : flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪ E ⊆
      Ulo ∪ Uhi ∪ (outgoing S v).biUnion W := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have hh := oriented_down_cover S F hF ti ui ti ui gi gi le_rfl le_rfl le_rfl 0 x v c hv hp
      rcases Finset.mem_union.mp hh with ht | hguard
      · apply Finset.mem_union_left
        rcases Finset.mem_union.mp ht with ht | ht
        · exact Finset.mem_union_left _ (hlo ht)
        · exact Finset.mem_union_right _ (hhi ht)
      · obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp hguard
        have hw' : w ∈ outgoing S v := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,((mem_passingGuards S F gi x v w).1 hw).1⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w,hw',hg w hw' hp⟩)
    · exact he hp
  have hcU : (Ulo ∪ Uhi).card ≤ ulo+uhi :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hUlo hUhi)
  have hcW : ((outgoing S v).biUnion W).card ≤ ∑ w ∈ outgoing S v, z w :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum hW)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hcU hcW))

theorem oriented_union_target_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tl gi gl : L) (degree b a u : ℕ)
    (hb : BBound F ui tl b) (ha : ABound F gl gi a)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hd : (outgoing S v).card=degree)
    (hvi : orientedRow S F ti ui gi 0 x v (!c₀))
    (hfalse : F tl (child x v c₀)=false)
    (hother : ∀ c : Bool, c ≠ c₀ → F tl (child x v c)=true)
    (hgl : guardFailures S F gl x v=∅)
    (hu : (flipsTo (F ti) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀)).card ≤ u) :
    (flipsTo (orientedRowBool S F ti ui gi 0 v (!c₀)) false x ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ b+degree*a+u := by
  let Ulo := liftBits v c₀ (flipsTo (F ti) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀))
  let Uhi := liftBits v (!c₀) (flipsTo (F ui) false (child x v (!c₀)))
  let W := fun w : V => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))
  have hwc : ∀ w ∈ outgoing S v, (W w).card ≤ a := by
    intro w hw
    have hz : F gl (child x w (S.label v w))=false := by
      cases h : F gl (child x w (S.label v w)) with
      | false => rfl
      | true =>
        have hm := (mem_guardFailures S F gl x v w).2 ⟨(Finset.mem_filter.mp hw).2,h⟩
        rw [hgl] at hm
        exact False.elim (Finset.notMem_empty _ hm)
    exact (card_liftBits _ _ _).le.trans (ha _ hz)
  have h := oriented_union_weighted S F hF ti ui gi x v (!c₀) hvi Ulo Uhi W
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x)
    (by simp only [Bool.not_not]; dsimp [Ulo]; rw [liftBits_union]; exact Finset.subset_union_left)
    (Finset.Subset.refl _)
    (by intro w _; exact Finset.Subset.refl _)
    (by
      intro p hp
      have hh := strict_target_repair_subset S F tl gl x v c₀ hfalse hother hgl hp
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      dsimp [Ulo]
      rw [liftBits_union]
      exact Finset.mem_union_right _ hh)
    u b (fun _ => a)
    (by simpa only [Ulo,card_liftBits] using hu)
    ((card_liftBits _ _ _).le.trans (hb _ (hother (!c₀) (by cases c₀ <;> decide)))) hwc
  simpa [Finset.sum_const,nsmul_eq_mul,hd,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem oriented_union_guard_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tl gi gl : L) (degree b0 b1 a u : ℕ)
    (hb0 : BBound F ti tl b0) (hb1 : BBound F ui tl b1) (ha : ABound F gl gi a)
    (x : ((V × Bool) × I) → Bool) (v w₀ : V) (c : Bool)
    (hd : (outgoing S v).card=degree)
    (hvi : orientedRow S F ti ui gi 0 x v c)
    (ht : ∀ e : Bool, F tl (child x v e)=true)
    (hgl : guardFailures S F gl x v={w₀})
    (hu : (flipsTo (F gi) true (child x w₀ (S.label v w₀)) ∪
      flipsTo (F gl) false (child x w₀ (S.label v w₀))).card ≤ u) :
    (flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ b0+b1+(degree-1)*a+u := by
  let Ulo := liftBits v (!c) (flipsTo (F ti) false (child x v (!c)))
  let Uhi := liftBits v c (flipsTo (F ui) false (child x v c))
  let W := fun w : V => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)) ∪
    if w=w₀ then flipsTo (F gl) false (child x w (S.label v w)) else ∅)
  have hwmem : w₀ ∈ guardFailures S F gl x v := by rw [hgl]; simp
  have hwout : w₀ ∈ outgoing S v := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,((mem_guardFailures S F gl x v w₀).1 hwmem).1⟩
  have hwc : ∀ w ∈ outgoing S v, (W w).card ≤ if w=w₀ then u else a := by
    intro w hw
    by_cases he : w=w₀
    · subst w; simpa [W] using hu
    · have hz : F gl (child x w (S.label v w))=false := by
        cases h : F gl (child x w (S.label v w)) with
        | false => rfl
        | true =>
          have hm := (mem_guardFailures S F gl x v w).2 ⟨(Finset.mem_filter.mp hw).2,h⟩
          rw [hgl,Finset.mem_singleton] at hm
          exact False.elim (he hm)
      simpa only [W,if_neg he,Finset.union_empty,card_liftBits] using ha _ hz
  have h := oriented_union_weighted S F hF ti ui gi x v c hvi Ulo Uhi W
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x)
    (Finset.Subset.refl _) (Finset.Subset.refl _)
    (by intro w _; dsimp [W]; rw [liftBits_union]; exact Finset.subset_union_left)
    (by
      intro p hp
      have hh := strict_guard_repair_subset S F tl gl x v w₀ ht hgl hp
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w₀,hwout,?_⟩
      dsimp [W]
      rw [if_pos rfl,liftBits_union]
      exact Finset.mem_union_right _ hh)
    b0 b1 (fun w => if w=w₀ then u else a)
    ((card_liftBits _ _ _).le.trans (hb0 _ (ht (!c))))
    ((card_liftBits _ _ _).le.trans (hb1 _ (ht c))) hwc
  rw [finset_sum_special _ _ hwout,hd] at h
  omega

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.oriented_union_subset
#print axioms ThreeBoundMinmaxTransfer.oriented_union_target_bound
#print axioms ThreeBoundMinmaxTransfer.oriented_union_guard_bound


