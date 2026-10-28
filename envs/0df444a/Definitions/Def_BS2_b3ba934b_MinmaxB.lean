-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxB
-- name    : BS2_b3ba934b_MinmaxB
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:26:46.613913+00:00
-- url     : https://prove2.me/theorems/df4e2013-0297-465b-a030-74f03310075d
-- title:
--   Sensitivity separation: MinmaxB (complete source module)
-- statement:
--   Complete Lean source module `MinmaxB` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxB.lean; original SHA-256 7df733d17f54816a0dcbd719e979656cc8a6ec02b0a08d28f0f7f689a93769a3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual min/max downward transfer, with the upper-child improvement and
exact next-tier guard-destruction gate. -/
import Definitions.Def_BS2_b3ba934b_MinmaxPairData

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_left_eq_lower (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤ u) (y : I → Bool) (hy : F u y=true) :
    (fun x => mm F t u x y)=F t := by
  funext x
  have hyt := hF _ _ htu _ hy
  simp only [mm,hyt,hy,Bool.and_true,Bool.or_true]

theorem mm_left_eq_upper (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤ u) (y : I → Bool) (hyt : F t y=true) (hyu : F u y=false) :
    (fun x => mm F t u x y)=F u := by
  funext x
  simp only [mm,hyt,hyu,Bool.and_true,Bool.or_false]
  cases hu : F u x with
  | false => simp
  | true => simp only [hF _ _ htu _ hu,Bool.and_self]

def orientedBits (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Finset ((V × Bool) × I) :=
  liftBits w (!c) (flipsTo (F t) false (child x w (!c))) ∪
    liftBits w c (flipsTo (F u) false (child x w c))

def mmTargetBits (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) : Finset ((V × Bool) × I) :=
  liftBits w false (flipsTo (fun z => mm F t u z (child x w true)) false (child x w false)) ∪
    liftBits w true (flipsTo (fun z => mm F t u z (child x w false)) false (child x w true))

theorem orientedBits_card (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a b : ℕ)
    (ha : (flipsTo (F t) false (child x w (!c))).card ≤ a)
    (hb : (flipsTo (F u) false (child x w c)).card ≤ b) :
    (orientedBits F t u x w c).card ≤ a+b := by
  exact (Finset.card_union_le _ _).trans (by simpa only [card_liftBits] using Nat.add_le_add ha hb)

theorem mmTargetBits_eq_oriented (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤ u) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool)
    (hh : F u (child x w c)=true) (hl : F t (child x w (!c))=true) :
    mmTargetBits F t u x w =
      if F u (child x w (!c))=true then orientedBits F t t x w c else orientedBits F t u x w c := by
  cases c
  · simp only [Bool.not_false] at hl ⊢
    by_cases ho : F u (child x w true)=true
    · rw [if_pos ho]
      unfold mmTargetBits orientedBits
      simp only [Bool.not_false]
      rw [mm_left_eq_lower F hF t u htu _ ho,mm_left_eq_lower F hF t u htu _ hh,Finset.union_comm]
    · rw [if_neg ho]
      have ho' : F u (child x w true)=false := by cases he : F u (child x w true) <;> simp_all
      unfold mmTargetBits orientedBits
      simp only [Bool.not_false]
      rw [mm_left_eq_upper F hF t u htu _ hl ho',mm_left_eq_lower F hF t u htu _ hh,Finset.union_comm]
  · simp only [Bool.not_true] at hl ⊢
    by_cases ho : F u (child x w false)=true
    · rw [if_pos ho]
      unfold mmTargetBits orientedBits
      simp only [Bool.not_true]
      rw [mm_left_eq_lower F hF t u htu _ hh,mm_left_eq_lower F hF t u htu _ ho]
    · rw [if_neg ho]
      have ho' : F u (child x w false)=false := by cases he : F u (child x w false) <;> simp_all
      unfold mmTargetBits orientedBits
      simp only [Bool.not_true]
      rw [mm_left_eq_lower F hF t u htu _ hh,mm_left_eq_upper F hF t u htu _ hl ho']

theorem mmTargetBits_card (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (hlu : ti ≤ ui) (ht : ti ≤ tj) (hu : ui ≤ uj)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (hstrong : mm F tj uj (child x w false) (child x w true)=true)
    (b0 b1 bu m : ℕ) (hb0 : BBound F ti tj b0) (hb1 : BBound F ti uj b1)
    (hbu : BBound F ui uj bu) (hm : MBound F ti tj ui m) :
    (mmTargetBits F ti ui x w).card ≤ max (b0+b1) (if tj<ui then bu+m else 0) := by
  obtain ⟨hl0,hl1,hup⟩ := (mm_true F tj uj _ _).1 hstrong
  have hor : ∃ c : Bool, F uj (child x w c)=true ∧ F tj (child x w (!c))=true := by
    rcases hup with hh | hh
    · exact ⟨false,hh,hl1⟩
    · exact ⟨true,hh,hl0⟩
  obtain ⟨c,hhigh,hlow⟩ := hor
  have hh := hF _ _ hu _ hhigh
  have hl := hF _ _ ht _ hlow
  rw [mmTargetBits_eq_oriented F hF ti ui hlu x w c hh hl]
  by_cases ho : F ui (child x w (!c))=true
  · rw [if_pos ho]
    exact (orientedBits_card F ti ti x w c b0 b1 (hb0 _ hlow) (hb1 _ hhigh)).trans (le_max_left _ _)
  · rw [if_neg ho]
    have ho' : F ui (child x w (!c))=false := by cases he : F ui (child x w (!c)) <;> simp_all
    have hlt : tj<ui := by
      by_contra hn
      have he := hF _ _ (le_of_not_gt hn) _ hlow
      rw [ho'] at he
      contradiction
    apply (orientedBits_card F ti ui x w c m bu (hm _ hlow ho') (hbu _ hhigh)).trans
    rw [if_pos hlt]
    omega

theorem own_mm_bit_mem (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : mm F t u (child (flip x {((w,c),a)}) w false)
      (child (flip x {((w,c),a)}) w true)=false) :
    ((w,c),a) ∈ mmTargetBits F t u x w := by
  cases c
  · rw [child_flip_same,child_flip_other x w w false true a (by simp)] at hoff
    exact Finset.mem_union_left _ ((mem_liftBits _ _ _ _ _ _).2
      ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hoff⟩⟩)
  · rw [child_flip_other x w w true false a (by simp),child_flip_same,mm_comm] at hoff
    exact Finset.mem_union_right _ ((mem_liftBits _ _ _ _ _ _).2
      ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hoff⟩⟩)

theorem minmax_down_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hd : (failed S F j x v).card=d) (hdq : d ≤ S.tolerance j)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x v false) (child x v true)=true) :
    flipsTo (parent S F i) false x ⊆
      mmTargetBits F (P.weakLower d) (P.weakUpper d) x v ∪ guardBits S F i j x v := by
  intro bit hbit
  obtain ⟨⟨w,c⟩,a⟩ := bit
  have hoff := (Finset.mem_filter.mp hbit).2
  by_cases he : ExtraFailure S F i j x v w c a
  · apply Finset.mem_union_right
    obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passing S F j x v w).2 ⟨hR,by simpa only [hl] using hbefore⟩,?_⟩
    apply (mem_liftBits _ _ _ _ _ _).2
    exact ⟨rfl,hl.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩⟩
  · have hcount : (failed S F i (flip x {((w,c),a)}) v).card ≤ d := by
      rw [← hd]
      exact Finset.card_le_card (failed_after_subset_of_no_extra S F hF i j P.guards x v w c a he)
    have hweak := mm_mono F hF _ _ _ _ (P.lowerOrder d hdq) (P.upperOrder d hdq) _ _ hstrong
    have hfalse : mm F (P.weakLower d) (P.weakUpper d)
        (child (flip x {((w,c),a)}) v false) (child (flip x {((w,c),a)}) v true)=false := by
      cases hh : mm F (P.weakLower d) (P.weakUpper d)
          (child (flip x {((w,c),a)}) v false) (child (flip x {((w,c),a)}) v true) with
      | false => rfl
      | true =>
          have hon := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
            P.weakDef _ v d (hdq.trans P.tolerances) hcount hh
          rw [hoff] at hon
          contradiction
    have hw : w=v := by
      by_contra hn
      rw [child_flip_other x w v c false a (fun h => hn (congrArg Prod.fst h).symm),
        child_flip_other x w v c true a (fun h => hn (congrArg Prod.fst h).symm),hweak] at hfalse
      contradiction
    subst w
    exact Finset.mem_union_left _ (own_mm_bit_mem F _ _ x v c a hfalse)

theorem minmax_safe_next_survives (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hd : (failed S F j x v).card=d)
    (hnext : d+1 ≤ S.tolerance i ∧ P.weakLower (d+1) ≤ P.strongLower d ∧ P.weakUpper (d+1) ≤ P.strongUpper d)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x v false) (child x v true)=true)
    (w : V) (c : Bool) (a : I) (hw : w≠v) : parent S F i (flip x {((w,c),a)})=true := by
  have hcount := failed_after_card_le_add_one S F hF i j P.guards x v w c a
  rw [hd] at hcount
  apply parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
    P.weakDef _ v (d+1) hnext.1 hcount
  rw [child_flip_other x w v c false a (fun h => hw (congrArg Prod.fst h).symm),
    child_flip_other x w v c true a (fun h => hw (congrArg Prod.fst h).symm)]
  exact mm_mono F hF _ _ _ _ hnext.2.1 hnext.2.2 _ _ hstrong

/-- Exact per-winning-row formula used by minmax_transfer.rawB. -/
theorem minmax_B_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : (failed S F j x w).card=d) (hdq : d ≤ S.tolerance j)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true)
    (a b0 b1 bu m : ℕ) (ha : ABound F (S.guard j) (S.guard i) a)
    (hb0 : BBound F (P.weakLower d) (P.strongLower d) b0)
    (hb1 : BBound F (P.weakLower d) (P.strongUpper d) b1)
    (hbu : BBound F (P.weakUpper d) (P.strongUpper d) bu)
    (hm : MBound F (P.weakLower d) (P.strongLower d) (P.weakUpper d) m) :
    (flipsTo (parent S F i) false x).card ≤
      max (b0+b1) (if P.strongLower d<P.weakUpper d then bu+m else 0)+
      if d+1 ≤ S.tolerance i ∧ P.weakLower (d+1) ≤ P.strongLower d ∧ P.weakUpper (d+1) ≤ P.strongUpper d
      then 0 else ((outgoing S w).card-d)*a := by
  have htarget := mmTargetBits_card F hF _ _ _ _ (P.weakLowerUpper d (hdq.trans P.tolerances))
    (P.lowerOrder d hdq) (P.upperOrder d hdq) x w hstrong b0 b1 bu m hb0 hb1 hbu hm
  have hcover := minmax_down_cover S F hF i j P x w d hd hdq hstrong
  by_cases hs : d+1 ≤ S.tolerance i ∧ P.weakLower (d+1) ≤ P.strongLower d ∧ P.weakUpper (d+1) ≤ P.strongUpper d
  · rw [if_pos hs,Nat.add_zero]
    apply (Finset.card_le_card (show flipsTo (parent S F i) false x ⊆
      mmTargetBits F (P.weakLower d) (P.weakUpper d) x w from ?_)).trans htarget
    intro bit hb
    obtain ht | hg := Finset.mem_union.mp (hcover hb)
    · exact ht
    · obtain ⟨z,hz,hbit⟩ := Finset.mem_biUnion.mp hg
      obtain ⟨hR,_⟩ := (mem_passing S F j x w z).1 hz
      obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hbit
      change ((z,S.label w z),a)=bit at he
      subst bit
      have hzw : z≠w := fun he => by subst z; exact S.loopless w hR
      have hon := minmax_safe_next_survives S F hF i j P x w d hd hs hstrong z (S.label w z) a hzw
      have hoff := (Finset.mem_filter.mp hb).2
      rw [hoff] at hon
      contradiction
  · rw [if_neg hs]
    apply (Finset.card_le_card hcover).trans
    apply (Finset.card_union_le _ _).trans
    have hg := guardBits_card_le S F i j x w a ha
    rw [hd] at hg
    exact Nat.add_le_add htarget hg

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.mmTargetBits_card
#print axioms ThreeBoundMinmaxTransfer.minmax_B_row


