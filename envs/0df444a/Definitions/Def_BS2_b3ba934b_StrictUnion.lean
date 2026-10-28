-- Prove2me | Definitions.Def_BS2_b3ba934b_StrictUnion
-- name    : BS2_b3ba934b_StrictUnion
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:01:10.836522+00:00
-- url     : https://prove2.me/theorems/247f720d-624a-4502-8bf2-0364bb0d6f43
-- title:
--   Sensitivity separation: StrictUnion (complete source module)
-- statement:
--   Complete Lean source module `StrictUnion` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/StrictUnion.lean; original SHA-256 b8cb65cdc129887eb3729182f514b30c59d50d82acb433874b9fc2b49ed81538; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Strict conditional union transfer for actual Boolean rows and parents. -/
import Definitions.Def_BS2_b3ba934b_ConditionalOrdinary
import Definitions.Def_BS2_b3ba934b_TournamentHighRows
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem zero_row_guard_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hv : ordinaryRow S F t g 0 x v) (w : V) (hvw : S.Adj v w) :
    F g (child x w (S.label v w)) = false := by
  have hempty : guardFailures S F g x v = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hv.2)
  cases hf : F g (child x w (S.label v w)) with
  | false => rfl
  | true =>
    have hm := (mem_guardFailures S F g x v w).2 ⟨hvw,hf⟩
    rw [hempty] at hm
    exact False.elim (Finset.notMem_empty _ hm)

theorem zero_rows_incompatible (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : L) (hab : ga ≤ tb) (hba : gb ≤ ta)
    (x : ((V × Bool) × I) → Bool) (v w : V) (hne : v ≠ w)
    (hv : ordinaryRow S F ta ga 0 x v) (hw : ordinaryRow S F tb gb 0 x w) : False := by
  by_cases h : S.Adj v w
  · have hf := zero_row_guard_false S F ta ga x v hv w h
    have ht := hF _ _ hab _ (hw.1 (S.label v w))
    rw [hf] at ht
    contradiction
  · have hr : S.Adj w v := (hR.orient w v hne.symm).2 h
    have hf := zero_row_guard_false S F tb gb x w hw v hr
    have ht := hF _ _ hba _ (hv.1 (S.label w v))
    rw [hf] at ht
    contradiction

theorem parent_exits_subset_row_exits (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti tl gi gl : L) (hil : gi ≤ tl) (hli : gl ≤ ti)
    (x : ((V × Bool) × I) → Bool) (v : V) :
    flipsTo (ordinaryParent S F ti gi 0) false x ∪
      flipsTo (ordinaryParent S F tl gl 0) true x ⊆
      flipsTo (ordinaryRowBool S F ti gi 0 v) false x ∪
        flipsTo (ordinaryRowBool S F tl gl 0 v) true x := by
  intro a ha
  rcases Finset.mem_union.mp ha with hd | hu
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(ordinary_row_false S F ti gi 0 _ v).2 ?_⟩
    intro hv
    have hon := (ordinary_parent_true S F ti gi 0 _).2 ⟨v,hv⟩
    rw [(Finset.mem_filter.mp hd).2] at hon
    contradiction
  · obtain ⟨w,hw⟩ := (ordinary_parent_true S F tl gl 0 _).1 (Finset.mem_filter.mp hu).2
    by_cases he : w=v
    · subst w
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(ordinary_row_true S F tl gl 0 _ v).2 hw⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,(ordinary_row_false S F ti gi 0 _ v).2 ?_⟩
      intro hv
      exact zero_rows_incompatible S hR F hF ti tl gi gl hil hli _ v w (Ne.symm he) hv hw

theorem guardFailures_own_flip (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (a : I) :
    guardFailures S F g (flip x {((v,c),a)}) v = guardFailures S F g x v := by
  ext w
  by_cases hR : S.Adj v w
  · have hw : w ≠ v := by intro he; subst w; exact S.loopless v hR
    simp only [mem_guardFailures,hR,true_and,
      child_flip_other x v w c (S.label v w) a (fun h => hw (congrArg Prod.fst h))]
  · simp only [mem_guardFailures,hR,false_and]

/-- A strict row can be repaired only at its unique failed target or guard. -/
theorem strict_repair_cases (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hoff : ¬ordinaryRow S F t g 0 x v)
    (hon : ordinaryRow S F t g 0 (flip x {((w,c),a)}) v) :
    (w=v ∧ F t (child x v c)=false ∧
      (∀ e : Bool, e ≠ c → F t (child x v e)=true) ∧
      guardFailures S F g x v = ∅ ∧ F t (flip (child x v c) {a})=true) ∨
    ((∀ e : Bool, F t (child x v e)=true) ∧ guardFailures S F g x v = {w} ∧
      S.Adj v w ∧ S.label v w=c ∧ F g (child x w c)=true ∧
      F g (flip (child x w c) {a})=false) := by
  have hfempty : guardFailures S F g (flip x {((w,c),a)}) v = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hon.2)
  by_cases hw : w=v
  · subst w
    have hg : guardFailures S F g x v = ∅ := by
      rw [guardFailures_own_flip] at hfempty
      exact hfempty
    have hother : ∀ e : Bool, e ≠ c → F t (child x v e)=true := by
      intro e he
      have h := hon.1 e
      rw [child_flip_other x v v c e a (fun h => he (congrArg Prod.snd h))] at h
      exact h
    have hfalse : F t (child x v c)=false := by
      cases h : F t (child x v c) with
      | false => rfl
      | true =>
        apply False.elim
        apply hoff
        refine ⟨?_,by simp [hg]⟩
        intro e
        by_cases he : e=c
        · simpa only [he] using h
        · exact hother e he
    exact Or.inl ⟨rfl,hfalse,hother,hg,by simpa only [child_flip_same] using hon.1 c⟩
  · have ht : ∀ e : Bool, F t (child x v e)=true := by
      intro e
      have h := hon.1 e
      rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)] at h
      exact h
    have hex : (guardFailures S F g x v).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hoff ⟨ht,by simp [he]⟩
    obtain ⟨z,hz⟩ := hex
    have hzprop := (mem_guardFailures S F g x v z).1 hz
    have hloc : (z,S.label v z)=(w,c) := by
      by_contra hp
      have hf : F g (child (flip x {((w,c),a)}) z (S.label v z))=true := by
        rw [child_flip_other x w z c (S.label v z) a hp]
        exact hzprop.2
      have hmem := (mem_guardFailures S F g _ v z).2 ⟨hzprop.1,hf⟩
      rw [hfempty] at hmem
      exact Finset.notMem_empty _ hmem
    have he : z=w := congrArg Prod.fst hloc
    subst z
    have hl : S.label v w=c := congrArg Prod.snd hloc
    have hsingleton : guardFailures S F g x v = {w} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hz,?_⟩
      intro z hz
      by_contra hzw
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F g x v z).1 hz
      have hf' : F g (child (flip x {((w,c),a)}) z (S.label v z))=true := by
        rw [child_flip_other x w z c (S.label v z) a (fun h => hzw (congrArg Prod.fst h))]
        exact hf
      have hmem := (mem_guardFailures S F g _ v z).2 ⟨hR,hf'⟩
      rw [hfempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hafter : F g (flip (child x w c) {a})=false := by
      cases h : F g (flip (child x w c) {a}) with
      | false => rfl
      | true =>
        have hmem : w ∈ guardFailures S F g (flip x {((w,c),a)}) v := by
          apply (mem_guardFailures S F g _ v w).2
          refine ⟨hzprop.1,?_⟩
          rw [hl,child_flip_same]
          exact h
        rw [hfempty] at hmem
        exact False.elim (Finset.notMem_empty _ hmem)
    exact Or.inr ⟨ht,hsingleton,hzprop.1,hl,by simpa only [hl] using hzprop.2,hafter⟩

def StrictTargetCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  ∃ c : Bool, F t (child x v c)=false ∧
    (∀ e : Bool, e ≠ c → F t (child x v e)=true) ∧ guardFailures S F g x v=∅

def StrictGuardCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  (∀ e : Bool, F t (child x v e)=true) ∧ ∃ w, guardFailures S F g x v={w}

theorem strict_no_repair (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hoff : ¬ordinaryRow S F t g 0 x v)
    (ht : ¬StrictTargetCandidate S F t g x v)
    (hg : ¬StrictGuardCandidate S F t g x v) :
    flipsTo (ordinaryRowBool S F t g 0 v) true x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F t g 0 _ v).1 (Finset.mem_filter.mp ha).2
  rcases strict_repair_cases S F t g x v w c a hoff hon with hh | hh
  · exact ht ⟨c,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  · exact hg ⟨hh.1,w,hh.2.1⟩

/-- Finite-set row accounting with independently weighted child and guard sets. -/
theorem row_union_weighted (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hv : ordinaryRow S F t g 0 x v)
    (U : Bool → Finset ((V × Bool) × I)) (W : V → Finset ((V × Bool) × I))
    (E : Finset ((V × Bool) × I))
    (ht : ∀ c, liftBits v c (flipsTo (F t) false (child x v c)) ⊆ U c)
    (hg : ∀ w ∈ outgoing S v,
      liftBits w (S.label v w) (flipsTo (F g) true (child x w (S.label v w))) ⊆ W w)
    (he : E ⊆ Finset.univ.biUnion U ∪ (outgoing S v).biUnion W)
    (u : Bool → ℕ) (z : V → ℕ)
    (hU : ∀ c, (U c).card ≤ u c) (hW : ∀ w ∈ outgoing S v, (W w).card ≤ z w) :
    (flipsTo (ordinaryRowBool S F t g 0 v) false x ∪ E).card ≤
      (u false+u true) + ∑ w ∈ outgoing S v, z w := by
  have hsub : flipsTo (ordinaryRowBool S F t g 0 v) false x ∪ E ⊆
      Finset.univ.biUnion U ∪ (outgoing S v).biUnion W := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have hc := row_destroying_subset S F hF t t g g le_rfl le_rfl 0 0 le_rfl x v hv hp
      rcases Finset.mem_union.mp hc with hc | hc
      · rcases Finset.mem_union.mp hc with hc | hc
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨false,Finset.mem_univ _,ht false hc⟩)
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨true,Finset.mem_univ _,ht true hc⟩)
      · obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp hc
        have hw' : w ∈ outgoing S v := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,((mem_passingGuards S F g x v w).1 hw).1⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w,hw',hg w hw' hp⟩)
    · exact he hp
  have huc : (Finset.univ.biUnion U).card ≤ u false+u true := by
    apply Finset.card_biUnion_le.trans
    have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset Bool)) => hU c)
    simpa only [Fintype.sum_bool,Nat.add_comm] using h
  have hwc : ((outgoing S v).biUnion W).card ≤ ∑ w ∈ outgoing S v, z w :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum hW)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add huc hwc))


/-- A target candidate's every successful strict repair uses its missing child. -/
theorem strict_target_repair_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hfalse : F t (child x v c₀)=false)
    (hother : ∀ c : Bool, c ≠ c₀ → F t (child x v c)=true)
    (hg : guardFailures S F g x v=∅) :
    flipsTo (ordinaryRowBool S F t g 0 v) true x ⊆
      liftBits v c₀ (flipsTo (F t) true (child x v c₀)) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F t g 0 _ v).1 (Finset.mem_filter.mp ha).2
  have hoff : ¬ordinaryRow S F t g 0 x v := by
    intro hv
    have ht := hv.1 c₀
    rw [hfalse] at ht
    contradiction
  rcases strict_repair_cases S F t g x v w c a hoff hon with hh | hh
  · obtain ⟨hw,hf,_,_,ht⟩ := hh
    subst w
    have hc : c=c₀ := by
      by_contra hn
      have hp := hother c hn
      rw [hf] at hp
      contradiction
    subst c
    exact (mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
  · rw [hg] at hh
    exact False.elim (by simpa using hh.2.1)

theorem strict_guard_repair_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v w₀ : V)
    (ht : ∀ c : Bool, F t (child x v c)=true)
    (hg : guardFailures S F g x v={w₀}) :
    flipsTo (ordinaryRowBool S F t g 0 v) true x ⊆
      liftBits w₀ (S.label v w₀) (flipsTo (F g) false (child x w₀ (S.label v w₀))) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F t g 0 _ v).1 (Finset.mem_filter.mp ha).2
  have hoff : ¬ordinaryRow S F t g 0 x v := by
    intro hv
    have hc := hv.2
    simp [hg] at hc
  rcases strict_repair_cases S F t g x v w c a hoff hon with hh | hh
  · have h := ht c
    rw [hh.2.1] at h
    contradiction
  · obtain ⟨_,hgs,hR,hl,_,hf⟩ := hh
    have hw : w=w₀ := by rw [hg] at hgs; simpa using hgs.symm
    subst w
    subst c
    exact (mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩⟩

theorem liftBits_union (v : V) (c : Bool) (A B : Finset I) :
    liftBits v c (A ∪ B) = liftBits v c A ∪ liftBits v c B := by
  exact Finset.map_union _ _

theorem row_union_target_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti tl gi gl : L) (d b a u : ℕ)
    (hd : ∀ v, (outgoing S v).card=d) (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hvi : ordinaryRow S F ti gi 0 x v)
    (hfalse : F tl (child x v c₀)=false)
    (hother : ∀ c : Bool, c ≠ c₀ → F tl (child x v c)=true)
    (hgl : guardFailures S F gl x v=∅)
    (hu : (flipsTo (F ti) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀)).card ≤ u) :
    (flipsTo (ordinaryRowBool S F ti gi 0 v) false x ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ b+d*a+u := by
  let U := fun c : Bool => liftBits v c (flipsTo (F ti) false (child x v c) ∪
    if c=c₀ then flipsTo (F tl) true (child x v c) else ∅)
  let W := fun w : V => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))
  have huc : ∀ c, (U c).card ≤ if c=c₀ then u else b := by
    intro c
    by_cases he : c=c₀
    · subst c; simpa [U] using hu
    · simpa only [U,if_neg he,Finset.union_empty,card_liftBits] using hb _ (hother c he)
  have hwc : ∀ w ∈ outgoing S v, (W w).card ≤ a := by
    intro w hw
    have hR := (Finset.mem_filter.mp hw).2
    have hz : F gl (child x w (S.label v w))=false := by
      cases h : F gl (child x w (S.label v w)) with
      | false => rfl
      | true =>
        have hm := (mem_guardFailures S F gl x v w).2 ⟨hR,h⟩
        rw [hgl] at hm
        exact False.elim (Finset.notMem_empty _ hm)
    exact (card_liftBits _ _ _).le.trans (ha _ hz)
  have h := row_union_weighted S F hF ti gi x v hvi U W
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x)
    (by intro c; dsimp [U]; rw [liftBits_union]; exact Finset.subset_union_left)
    (by intro w _; exact Finset.Subset.refl _)
    (by
      intro p hp
      have hh := strict_target_repair_subset S F tl gl x v c₀ hfalse hother hgl hp
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨c₀,Finset.mem_univ _,?_⟩
      dsimp [U]
      rw [if_pos rfl,liftBits_union]
      exact Finset.mem_union_right _ hh)
    (fun c => if c=c₀ then u else b) (fun _ => a) huc hwc
  have hs : (if false=c₀ then u else b)+(if true=c₀ then u else b)=u+b := by
    cases c₀ <;> simp [Nat.add_comm]
  rw [hs] at h
  simpa [Finset.sum_const,nsmul_eq_mul,hd v,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem finset_sum_special {J : Type} [DecidableEq J] (A : Finset J) (w₀ : J)
    (hw : w₀ ∈ A) (p a : ℕ) :
    (∑ w ∈ A, if w=w₀ then p else a)=(A.card-1)*a+p := by
  calc
    _ = (∑ w ∈ A.erase w₀, if w=w₀ then p else a)+p := by
      simpa using (Finset.sum_erase_add A (fun w => if w=w₀ then p else a) hw).symm
    _ = (A.card-1)*a+p := by
      have he : (∑ w ∈ A.erase w₀, if w=w₀ then p else a)=∑ _w ∈ A.erase w₀, a := by
        apply Finset.sum_congr rfl
        intro w hw
        exact if_neg (Finset.ne_of_mem_erase hw)
      rw [he]
      simp [Finset.card_erase_of_mem hw]

theorem row_union_guard_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti tl gi gl : L) (d b a u : ℕ)
    (hd : ∀ v, (outgoing S v).card=d) (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (x : ((V × Bool) × I) → Bool) (v w₀ : V)
    (hvi : ordinaryRow S F ti gi 0 x v)
    (ht : ∀ c : Bool, F tl (child x v c)=true)
    (hgl : guardFailures S F gl x v={w₀})
    (hu : (flipsTo (F gi) true (child x w₀ (S.label v w₀)) ∪
      flipsTo (F gl) false (child x w₀ (S.label v w₀))).card ≤ u) :
    (flipsTo (ordinaryRowBool S F ti gi 0 v) false x ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ 2*b+(d-1)*a+u := by
  let U := fun c : Bool => liftBits v c (flipsTo (F ti) false (child x v c))
  let W := fun w : V => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)) ∪
    if w=w₀ then flipsTo (F gl) false (child x w (S.label v w)) else ∅)
  have hwmem : w₀ ∈ guardFailures S F gl x v := by rw [hgl]; simp
  have hwout : w₀ ∈ outgoing S v := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,((mem_guardFailures S F gl x v w₀).1 hwmem).1⟩
  have huc : ∀ c, (U c).card ≤ b := fun c => (card_liftBits _ _ _).le.trans (hb _ (ht c))
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
  have h := row_union_weighted S F hF ti gi x v hvi U W
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x)
    (by intro c; exact Finset.Subset.refl _)
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
    (fun _ => b) (fun w => if w=w₀ then u else a) huc hwc
  rw [finset_sum_special _ _ hwout,hd v] at h
  omega


/-- Strict parent union transfer. The R input bounds the actual strict component
    row; it is not a bound for a potentially larger graded weak parent. -/
theorem zero_union_of_row_boundary (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk tl gi gj gk gl : L)
    (htij : ti ≤ tj) (htjk : tj ≤ tk) (htkl : tk ≤ tl)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (d b a dt dg R : ℕ) (hd : ∀ v, (outgoing S v).card=d)
    (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj 0 x = true)
    (hxk : ordinaryParent S F tk gk 0 x = false)
    (hR : ∀ v, ordinaryRow S F tj gj 0 x v → ¬ordinaryRow S F tk gk 0 x v →
      (flipsTo (ordinaryRowBool S F ti gi 0 v) false x).card ≤ R) :
    (flipsTo (ordinaryParent S F ti gi 0) false x ∪
      flipsTo (ordinaryParent S F tl gl 0) true x).card ≤
      max R (max (if tj<tk then b+d*a+dt else 0)
        (if gk<gj then 2*b+(d-1)*a+dg else 0)) := by
  obtain ⟨v,hvj⟩ := (ordinary_parent_true S F tj gj 0 x).1 hxj
  have hvk : ¬ordinaryRow S F tk gk 0 x v := by
    intro h
    have hh := (ordinary_parent_true S F tk gk 0 x).2 ⟨v,h⟩
    rw [hxk] at hh
    contradiction
  have hvi : ordinaryRow S F ti gi 0 x v :=
    ⟨fun c => hF _ _ htij _ (hvj.1 c),
      (Finset.card_le_card (guardFailures_mono S F hF gi gj hgjgi x v)).trans hvj.2⟩
  have hvl : ¬ordinaryRow S F tl gl 0 x v := by
    intro hv
    apply hvk
    exact ⟨fun c => hF _ _ htkl _ (hv.1 c),
      (Finset.card_le_card (guardFailures_mono S F hF gk gl hglgk x v)).trans hv.2⟩
  apply (Finset.card_le_card (parent_exits_subset_row_exits S hT F hF ti tl gi gl hgil hgli x v)).trans
  by_cases hcT : StrictTargetCandidate S F tl gl x v
  · obtain ⟨c₀,hfalse,hother,hgl⟩ := hcT
    have hglk : guardFailures S F gk x v=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hh := guardFailures_mono S F hF gk gl hglgk x v hw
      rw [hgl] at hh
      exact Finset.notMem_empty _ hh
    have hkt : F tk (child x v c₀)=false := by
      cases h : F tk (child x v c₀) with
      | false => rfl
      | true =>
        apply False.elim
        apply hvk
        refine ⟨?_,by simp [hglk]⟩
        intro c
        by_cases he : c=c₀
        · simpa only [he] using h
        · exact hF _ _ htkl _ (hother c he)
    have hlt : tj<tk := by
      apply lt_of_le_of_ne htjk
      intro he
      have hh := hvj.1 c₀
      rw [he,hkt] at hh
      contradiction
    have hbound := row_union_target_bound S F hF ti tl gi gl d b a dt hd hb ha x v c₀
      hvi hfalse hother hgl (hdt _ (hvj.1 c₀) hkt)
    exact hbound.trans ((by rw [if_pos hlt]; exact le_max_left _ _ :
      b+d*a+dt ≤ max (if tj<tk then b+d*a+dt else 0)
        (if gk<gj then 2*b+(d-1)*a+dg else 0)).trans (le_max_right _ _))
  · by_cases hcG : StrictGuardCandidate S F tl gl x v
    · obtain ⟨ht,w₀,hgl⟩ := hcG
      have hwmem : w₀ ∈ guardFailures S F gl x v := by rw [hgl]; simp
      have hadj := ((mem_guardFailures S F gl x v w₀).1 hwmem).1
      have hjoff := zero_row_guard_false S F tj gj x v hvj w₀ hadj
      have hkon : F gk (child x w₀ (S.label v w₀))=true := by
        cases h : F gk (child x w₀ (S.label v w₀)) with
        | true => rfl
        | false =>
          have hempty : guardFailures S F gk x v=∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            have hglw := guardFailures_mono S F hF gk gl hglgk x v hw
            rw [hgl,Finset.mem_singleton] at hglw
            subst w
            have htr := ((mem_guardFailures S F gk x v w₀).1 hw).2
            rw [h] at htr
            contradiction
          exact False.elim (hvk ⟨fun c => hF _ _ htkl _ (ht c),by simp [hempty]⟩)
      have hlt : gk<gj := by
        apply lt_of_le_of_ne hgkgj
        intro he
        rw [he,hjoff] at hkon
        contradiction
      have hlocal : (flipsTo (F gi) true (child x w₀ (S.label v w₀)) ∪
          flipsTo (F gl) false (child x w₀ (S.label v w₀))).card ≤ dg := by
        simpa only [Finset.union_comm] using hdg _ hkon hjoff
      have hbound := row_union_guard_bound S F hF ti tl gi gl d b a dg hd hb ha x v w₀
        hvi ht hgl hlocal
      exact hbound.trans ((by rw [if_pos hlt]; exact le_max_right _ _ :
        2*b+(d-1)*a+dg ≤ max (if tj<tk then b+d*a+dt else 0)
          (if gk<gj then 2*b+(d-1)*a+dg else 0)).trans (le_max_right _ _))
    · rw [strict_no_repair S F tl gl x v hvl hcT hcG,Finset.union_empty]
      exact (hR v hvj hvk).trans (le_max_left _ _)

/-- Exact strict D formula with the improved primitive-M component. -/
theorem strictD (S : Stage L I V) (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk tl gi gj gk gl : L)
    (htij : ti ≤ tj) (htjk : tj ≤ tk) (htkl : tk ≤ tl)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (d m b₀ a₀ p b a dt dg : ℕ) (hd : ∀ v, (outgoing S v).card=d)
    (hm : MBound F ti tj tk m) (hb₀ : BBound F ti tk b₀)
    (ha₀ : ABound F gj gi a₀) (hp : PBound F gk gj gi p)
    (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj 0 x = true)
    (hxk : ordinaryParent S F tk gk 0 x = false) :
    (flipsTo (ordinaryParent S F ti gi 0) false x ∪
      flipsTo (ordinaryParent S F tl gl 0) true x).card ≤
      max (max (if tj<tk then max (2*m) (m+b₀)+d*a₀ else 0)
        (if gk<gj then 2*b₀+(d-1)*a₀+p else 0))
        (max (if tj<tk then b+d*a+dt else 0) (if gk<gj then 2*b+(d-1)*a+dg else 0)) := by
  apply zero_union_of_row_boundary S hT F hF ti tj tk tl gi gj gk gl
    htij htjk htkl hgjgi hgkgj hglgk hgil hgli d b a dt dg _ hd hb ha hdt hdg x hxj hxk
  intro v hvj hvk
  have h := row_primitiveM S F hF ti tj tk gi gj gk htij htjk hgjgi hgkgj 0 0 le_rfl
    d m b₀ a₀ p hd hm hb₀ ha₀ hp x v hvj hvk
  simpa only [ite_true,Nat.sub_zero,Nat.add_assoc] using h

end
end ThreeBoundConditional

#print axioms ThreeBoundConditional.strictD


