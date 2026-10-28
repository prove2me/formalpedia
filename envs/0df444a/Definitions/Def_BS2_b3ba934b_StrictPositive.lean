-- Prove2me | Definitions.Def_BS2_b3ba934b_StrictPositive
-- name    : BS2_b3ba934b_StrictPositive
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:05:16.357605+00:00
-- url     : https://prove2.me/theorems/580db8e1-9968-4a19-a8e2-f7318f05e645
-- title:
--   Sensitivity separation: StrictPositive (complete source module)
-- statement:
--   Complete Lean source module `StrictPositive` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/StrictPositive.lean; original SHA-256 549e6ba1808bd229a847f779827b54a74eae41146d2a38e7d8ed2b2cf1b42923; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Refined strict conditional positive transfer, including source-labeled cap. -/
import Definitions.Def_BS2_b3ba934b_StrictUnion
import Definitions.Def_BS2_b3ba934b_ResidualCaps

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def strictOutHeads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (tl gl : L) (x : ((V × Bool) × I) → Bool) (p : V) : Finset V :=
  Finset.univ.filter fun v => S.Adj p v ∧ StrictTargetCandidate S F tl gl x v

def strictOutBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (tl gl : L) (x : ((V × Bool) × I) → Bool) (p : V) : Finset ((V × Bool) × I) :=
  (strictOutHeads S F tl gl x p).biUnion fun v =>
    liftBits v (S.label p v) (flipsTo (F tl) true (child x v (S.label p v)))

theorem strictOutHeads_other_true (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L) (hgt : gj ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (v : V) (hv : v ∈ strictOutHeads S F tl gl x p) (c : Bool) (hc : c ≠ S.label p v) :
    F tl (child x v c)=true := by
  obtain ⟨_,hR,c₀,hfalse,hother,hgl⟩ := Finset.mem_filter.mp hv
  have hz := zero_row_guard_false S F tj gj x p hp v hR
  have htl : F tl (child x v (S.label p v))=false := rejects_of_le F hF gj tl hgt _ hz
  have he : S.label p v=c₀ := by
    by_contra hn
    have hh := hother _ hn
    rw [htl] at hh
    contradiction
  exact hother c (by simpa only [← he] using hc)

theorem strictOutHeads_card (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L)
    (hgt : gj ≤ tl) (hglt : gl ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (cap : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1)) :
    (strictOutHeads S F tl gl x p).card ≤ cap := by
  classical
  let A := strictOutHeads S F tl gl x p
  have hdis : Disjoint A {p} := by
    apply Finset.disjoint_left.mpr
    intro v hv hpv
    have he : v=p := Finset.mem_singleton.mp hpv
    subst v
    exact S.loopless p (Finset.mem_filter.mp hv).2.1
  have hdom : ∀ v ∈ ({p} : Finset V), ∀ w ∈ A, S.Adj v w := by
    intro v hv w hw
    have he : v=p := Finset.mem_singleton.mp hv
    subst v
    exact (Finset.mem_filter.mp hw).2.1
  have hzero : ∀ v ∈ A ∪ {p},
      (CandidateCoherence.mismatch S.Adj S.label A (S.label p) v).card=0 := by
    intro v hv
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwA,hR,hne⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_union.mp hv with hvA | hvp
    · obtain ⟨_,_,c₀,hfalse,hother,hgl⟩ := Finset.mem_filter.mp hvA
      have htrue := hF _ _ hglt _
        (strictOutHeads_other_true S F hF tj gj tl gl hgt x p hp w hwA (S.label v w) hne)
      have hmem := (mem_guardFailures S F gl x v w).2 ⟨hR,htrue⟩
      rw [hgl] at hmem
      exact Finset.notMem_empty _ hmem
    · have he : v=p := Finset.mem_singleton.mp hvp
      subst v
      exact hne rfl
  have hh := hcap A {p} (S.label p) hdis (by simp) hdom hzero
  change A.card ≤ cap
  omega

theorem strictOutBits_card (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L)
    (hgt : gj ≤ tl) (hglt : gl ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (cap a : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (ha : ABound F gj tl a) : (strictOutBits S F tl gl x p).card ≤ cap*a := by
  calc
    _ ≤ ∑ v ∈ strictOutHeads S F tl gl x p,
      (liftBits v (S.label p v) (flipsTo (F tl) true (child x v (S.label p v)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ strictOutHeads S F tl gl x p, a := by
      apply Finset.sum_le_sum
      intro v hv
      rw [card_liftBits]
      exact ha _ (zero_row_guard_false S F tj gj x p hp v (Finset.mem_filter.mp hv).2.1)
    _ ≤ cap*a := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      simpa using Nat.mul_le_mul_right a (strictOutHeads_card S F hF tj gj tl gl hgt hglt x p hp cap hcap)

/-- An outgoing new winner repairs precisely the selected private target. -/
theorem strict_outgoing_repair (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L) (hgt : gj ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p v w : V) (c : Bool) (a : I)
    (hp : ordinaryRow S F tj gj 0 x p) (hpv : S.Adj p v)
    (hv : ordinaryRow S F tl gl 0 (flip x {((w,c),a)}) v) :
    ((w,c),a) ∈ strictOutBits S F tl gl x p := by
  have hz := zero_row_guard_false S F tj gj x p hp v hpv
  have hloc : (v,S.label p v)=(w,c) := by
    by_contra hn
    have ht := hv.1 (S.label p v)
    rw [child_flip_other x w v c (S.label p v) a hn] at ht
    have hh := hF _ _ hgt _ ht
    rw [hz] at hh
    contradiction
  have hvw : v=w := congrArg Prod.fst hloc
  subst w
  have hc : S.label p v=c := congrArg Prod.snd hloc
  subst c
  have hoff : ¬ordinaryRow S F tl gl 0 x v := by
    intro ho
    have ht := hF _ _ hgt _ (ho.1 (S.label p v))
    rw [hz] at ht
    contradiction
  have hcand : StrictTargetCandidate S F tl gl x v := by
    rcases strict_repair_cases S F tl gl x v v (S.label p v) a hoff hv with hh | hh
    · exact ⟨S.label p v,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    · exact False.elim (S.loopless v hh.2.2.1)
  apply Finset.mem_biUnion.mpr
  refine ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpv,hcand⟩,?_⟩
  apply (mem_liftBits _ _ _ _ _ _).2
  refine ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  simpa only [child_flip_same] using hv.1 (S.label p v)

/-- Cross winners incoming to the fixed weak row destroy a selected guard child. -/
theorem strict_incoming_repair (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L) (hgt : gl ≤ tj)
    (x : ((V × Bool) × I) → Bool) (p v w : V) (c : Bool) (a : I)
    (hp : ordinaryRow S F tj gj 0 x p) (hvp : S.Adj v p)
    (hv : ordinaryRow S F tl gl 0 (flip x {((w,c),a)}) v) :
    ((w,c),a) ∈ targetBits F gl x p := by
  have hz := zero_row_guard_false S F tl gl _ v hv p hvp
  have hloc : (p,S.label v p)=(w,c) := by
    by_contra hn
    rw [child_flip_other x w p c (S.label v p) a hn] at hz
    have ht := hF _ _ hgt _ (hp.1 (S.label v p))
    rw [hz] at ht
    contradiction
  have hpw : p=w := congrArg Prod.fst hloc
  subst w
  have hc : S.label v p=c := congrArg Prod.snd hloc
  rw [hc,child_flip_same] at hz
  have hm : a ∈ flipsTo (F gl) false (child x p c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
  cases c
  · exact Finset.mem_union_left _ ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩)
  · exact Finset.mem_union_right _ ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩)

/-- Complete successful-upward-flip cover relative to one weak winning row. -/
theorem strict_parent_up_cover (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L)
    (hgt : gj ≤ tl) (hgl : gl ≤ tj)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p) :
    flipsTo (ordinaryParent S F tl gl 0) true x ⊆
      strictOutBits S F tl gl x p ∪ (targetBits F gl x p ∪
        flipsTo (ordinaryRowBool S F tl gl 0 p) true x) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  obtain ⟨v,hv⟩ := (ordinary_parent_true S F tl gl 0 _).1 (Finset.mem_filter.mp ha).2
  by_cases he : v=p
  · subst v
    exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ordinary_row_true S F tl gl 0 _ p).2 hv⟩))
  · by_cases hout : S.Adj p v
    · exact Finset.mem_union_left _ (strict_outgoing_repair S F hF tj gj tl gl hgt x p v w c a hp hout hv)
    · have hin : S.Adj v p := (hT.orient v p he).2 hout
      exact Finset.mem_union_right _ (Finset.mem_union_left _
        (strict_incoming_repair S F hF tj gj tl gl hgl x p v w c a hp hin hv))


/-- A known missing intermediate target pins every same-row strong repair. -/
theorem same_row_up_target_location (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tk tl gl : L) (ht : tk ≤ tl)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hmiss : F tk (child x v c₀)=false) (w : V) (c : Bool) (a : I)
    (hon : ordinaryRow S F tl gl 0 (flip x {((w,c),a)}) v) :
    (v,c₀)=(w,c) := by
  by_contra hn
  have hh := hon.1 c₀
  rw [child_flip_other x w v c c₀ a hn] at hh
  have hk := hF _ _ ht _ hh
  rw [hmiss] at hk
  contradiction

theorem same_row_up_target_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tk tl gl : L) (ht : tk ≤ tl)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hmiss : F tk (child x v c₀)=false) :
    flipsTo (ordinaryRowBool S F tl gl 0 v) true x ⊆
      liftBits v c₀ (flipsTo (F tl) true (child x v c₀)) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
  have hh := same_row_up_target_location S F hF tk tl gl ht x v c₀ hmiss w c a hon
  cases hh
  apply (mem_liftBits _ _ _ _ _ _).2
  exact ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [child_flip_same] using hon.1 c₀⟩⟩

/-- A known intermediate failed guard similarly pins all same-row repairs. -/
theorem same_row_up_guard_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (gk tl gl : L) (hg : gl ≤ gk)
    (x : ((V × Bool) × I) → Bool) (v w₀ : V)
    (hR : S.Adj v w₀) (hgk : F gk (child x w₀ (S.label v w₀))=true) :
    flipsTo (ordinaryRowBool S F tl gl 0 v) true x ⊆
      liftBits w₀ (S.label v w₀) (flipsTo (F gl) false (child x w₀ (S.label v w₀))) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
  have hz := zero_row_guard_false S F tl gl _ v hon w₀ hR
  have hloc : (w₀,S.label v w₀)=(w,c) := by
    by_contra hn
    rw [child_flip_other x w w₀ c (S.label v w₀) a hn] at hz
    have ht := hF _ _ hg _ hgk
    rw [hz] at ht
    contradiction
  cases hloc
  apply (mem_liftBits _ _ _ _ _ _).2
  exact ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [child_flip_same] using hz⟩⟩

/-- Same-row conditional repairs have the maximum of the target/guard gap costs. -/
theorem same_row_up_conditional_card (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tj tk tl gj gk gl : L) (ht : tk ≤ tl) (hg : gl ≤ gk)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (hvj : ordinaryRow S F tj gj 0 x v) (hvk : ¬ordinaryRow S F tk gk 0 x v)
    (p m : ℕ) (hp : PBound F tj tk tl p) (hm : MBound F gl gk gj m) :
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ max p m := by
  by_cases hmiss : ∃ c : Bool, F tk (child x v c)=false
  · obtain ⟨c,hc⟩ := hmiss
    have hs := Finset.card_le_card (same_row_up_target_subset S F hF tk tl gl ht x v c hc)
    rw [card_liftBits] at hs
    exact (hs.trans (hp _ (hvj.1 c) hc)).trans (le_max_left _ _)
  · have htk : ∀ c : Bool, F tk (child x v c)=true := by
      intro c
      cases h : F tk (child x v c) with
      | false => exact False.elim (hmiss ⟨c,h⟩)
      | true => rfl
    have hnon : (guardFailures S F gk x v).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hvk ⟨htk,by simp [he]⟩
    obtain ⟨w,hw⟩ := hnon
    obtain ⟨hR,hk⟩ := (mem_guardFailures S F gk x v w).1 hw
    have hj := zero_row_guard_false S F tj gj x v hvj w hR
    have hs := Finset.card_le_card (same_row_up_guard_subset S F hF gk tl gl hg x v w hR hk)
    rw [card_liftBits] at hs
    exact (hs.trans (hm _ hk hj)).trans (le_max_right _ _)

/-- First exact strict-P improvement (separate same-row and cross repairs). -/
theorem strictP_basic (S : Stage L I V) (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (tj tk tl gj gk gl : L) (htkl : tk ≤ tl) (hglgk : gl ≤ gk)
    (hgjtl : gj ≤ tl) (hgltj : gl ≤ tj) (hgltl : gl ≤ tl)
    (cap b a p m : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (hb : BBound F gl tj b) (ha : ABound F gj tl a)
    (hp : PBound F tj tk tl p) (hm : MBound F gl gk gj m)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj 0 x=true)
    (hxk : ordinaryParent S F tk gk 0 x=false) :
    (flipsTo (ordinaryParent S F tl gl 0) true x).card ≤ 2*b+cap*a+max p m := by
  obtain ⟨v,hvj⟩ := (ordinary_parent_true S F tj gj 0 x).1 hxj
  have hvk : ¬ordinaryRow S F tk gk 0 x v := by
    intro h
    have hh := (ordinary_parent_true S F tk gk 0 x).2 ⟨v,h⟩
    rw [hxk] at hh
    contradiction
  calc
    _ ≤ (strictOutBits S F tl gl x v ∪ (targetBits F gl x v ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x)).card :=
      Finset.card_le_card (strict_parent_up_cover S hT F hF tj gj tl gl hgjtl hgltj x v hvj)
    _ ≤ (strictOutBits S F tl gl x v).card + ((targetBits F gl x v).card +
      (flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ ≤ cap*a+(2*b+max p m) := Nat.add_le_add
      (strictOutBits_card S F hF tj gj tl gl hgjtl hgltl x v hvj cap a hcap ha)
      (Nat.add_le_add (targetBits_card_le F gl tj x v b hb hvj.1)
        (same_row_up_conditional_card S F hF tj tk tl gj gk gl htkl hglgk x v hvj hvk p m hp hm))
    _ = _ := by omega

/-- Two private-child boundaries plus repair of one child can use a joint bound. -/
theorem targetBits_union_one_up_card (F : L → (I → Bool) → Bool)
    (gi tl : L) (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (E : Finset ((V × Bool) × I))
    (he : E ⊆ liftBits v c₀ (flipsTo (F tl) true (child x v c₀))) (u b : ℕ)
    (hu : (flipsTo (F gi) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀)).card ≤ u)
    (hb : ∀ c : Bool, c ≠ c₀ → (flipsTo (F gi) false (child x v c)).card ≤ b) :
    (targetBits F gi x v ∪ E).card ≤ u+b := by
  have hh := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl (targetBits F gi x v)) he)
  apply hh.trans
  cases c₀
  · rw [targetBits,Finset.union_right_comm,← liftBits_union]
    exact (Finset.card_union_le _ _).trans (by simpa only [card_liftBits] using Nat.add_le_add hu (hb true (by decide)))
  · rw [targetBits,Finset.union_assoc,← liftBits_union]
    exact (Finset.card_union_le _ _).trans (by
      have hh := Nat.add_le_add (hb false (by decide)) hu
      simpa only [card_liftBits,Nat.add_comm] using hh)


/-- Target-defect cross repairs and same-row repairs share their private child. -/
theorem strictP_target_local (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tj tk tl gl : L) (ht : tk ≤ tl)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (htj : ∀ c : Bool, F tj (child x v c)=true)
    (hmiss : ∃ c : Bool, F tk (child x v c)=false)
    (m bₖ bₗ u : ℕ) (hm : MBound F gl tj tk m)
    (hbₖ : BBound F gl tk bₖ) (hbₗ : BBound F gl tl bₗ) (hu : DBound F gl tj tk tl u) :
    (targetBits F gl x v ∪ flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤
      max (max (2*m) (m+bₖ)) (u+bₗ) := by
  by_cases he : flipsTo (ordinaryRowBool S F tl gl 0 v) true x=∅
  · rw [he,Finset.union_empty]
    exact (targetBits_conditional_card F gl tj tk x v m bₖ hm hbₖ htj hmiss).trans (le_max_left _ _)
  · obtain ⟨⟨⟨w,c⟩,a⟩,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨c₀,hc₀⟩ := hmiss
    have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
    have hloc := same_row_up_target_location S F hF tk tl gl ht x v c₀ hc₀ w c a hon
    have hw : v=w := congrArg Prod.fst hloc
    subst w
    have hc : c₀=c := congrArg Prod.snd hloc
    subst c
    have hother : ∀ e : Bool, e ≠ c₀ → F tl (child x v e)=true := by
      intro e he
      have h := hon.1 e
      rw [child_flip_other x v v c₀ e a (fun h => he (congrArg Prod.snd h))] at h
      exact h
    have hbound := targetBits_union_one_up_card F gl tl x v c₀ _
      (same_row_up_target_subset S F hF tk tl gl ht x v c₀ hc₀) u bₗ
      (hu _ (htj c₀) hc₀) (fun e he => hbₗ _ (hother e he))
    exact hbound.trans (le_max_right _ _)

/-- Guard-defect cross repairs use stronger target states if a same-row repair exists. -/
theorem strictP_guard_local (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tj tk tl gj gk gl : L) (hg : gl ≤ gk)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (hvj : ordinaryRow S F tj gj 0 x v)
    (htk : ∀ c : Bool, F tk (child x v c)=true)
    (hvk : ¬ordinaryRow S F tk gk 0 x v)
    (bₖ bₗ m : ℕ) (hbₖ : BBound F gl tk bₖ) (hbₗ : BBound F gl tl bₗ)
    (hm : MBound F gl gk gj m) :
    (targetBits F gl x v ∪ flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤
      max (2*bₖ) (2*bₗ+m) := by
  by_cases he : flipsTo (ordinaryRowBool S F tl gl 0 v) true x=∅
  · rw [he,Finset.union_empty]
    exact (targetBits_card_le F gl tk x v bₖ hbₖ htk).trans (le_max_left _ _)
  · have hnon : (guardFailures S F gk x v).Nonempty := by
      by_contra hn
      have hh := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hvk ⟨htk,by simp [hh]⟩
    obtain ⟨w₀,hw₀⟩ := hnon
    obtain ⟨hR,hk⟩ := (mem_guardFailures S F gk x v w₀).1 hw₀
    have hj := zero_row_guard_false S F tj gj x v hvj w₀ hR
    have hsub := same_row_up_guard_subset S F hF gk tl gl hg x v w₀ hR hk
    have hup : (flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ m := by
      have hh := Finset.card_le_card hsub
      rw [card_liftBits] at hh
      exact hh.trans (hm _ hk hj)
    obtain ⟨⟨⟨w,c⟩,a⟩,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨hw,hc,_⟩ := (mem_liftBits _ _ _ _ _ _).1 (hsub ha)
    subst w
    have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
    have hne : v ≠ w₀ := by intro h; subst w₀; exact S.loopless v hR
    have htl : ∀ e : Bool, F tl (child x v e)=true := by
      intro e
      have h := hon.1 e
      rw [child_flip_other x w₀ v c e a (fun h => hne (congrArg Prod.fst h))] at h
      exact h
    exact ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (targetBits_card_le F gl tl x v bₗ hbₗ htl) hup)).trans (le_max_right _ _)

/-- Second exact strict-P improvement, separating target and guard defects. -/
theorem strictP_refined (S : Stage L I V) (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (tj tk tl gj gk gl : L) (htjk : tj ≤ tk) (htkl : tk ≤ tl)
    (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgjtl : gj ≤ tl) (hgltj : gl ≤ tj) (hgltl : gl ≤ tl)
    (cap a mₜ bₖ bₗ u m₉ : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (ha : ABound F gj tl a) (hmₜ : MBound F gl tj tk mₜ)
    (hbₖ : BBound F gl tk bₖ) (hbₗ : BBound F gl tl bₗ)
    (hu : DBound F gl tj tk tl u) (hm₉ : MBound F gl gk gj m₉)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj 0 x=true)
    (hxk : ordinaryParent S F tk gk 0 x=false) :
    (flipsTo (ordinaryParent S F tl gl 0) true x).card ≤
      max (if tj<tk then cap*a+max (max (2*mₜ) (mₜ+bₖ)) (u+bₗ) else 0)
        (if gk<gj then cap*a+max (2*bₖ) (2*bₗ+m₉) else 0) := by
  obtain ⟨v,hvj⟩ := (ordinary_parent_true S F tj gj 0 x).1 hxj
  have hvk : ¬ordinaryRow S F tk gk 0 x v := by
    intro h
    have hh := (ordinary_parent_true S F tk gk 0 x).2 ⟨v,h⟩
    rw [hxk] at hh
    contradiction
  have hout := strictOutBits_card S F hF tj gj tl gl hgjtl hgltl x v hvj cap a hcap ha
  have hcover := Finset.card_le_card (strict_parent_up_cover S hT F hF tj gj tl gl hgjtl hgltj x v hvj)
  have hsplit := hcover.trans (Finset.card_union_le _ _)
  by_cases hmiss : ∃ c : Bool, F tk (child x v c)=false
  · have hlt : tj<tk := by
      apply lt_of_le_of_ne htjk
      intro he
      obtain ⟨c,hc⟩ := hmiss
      have hh := hvj.1 c
      rw [he,hc] at hh
      contradiction
    have hh := hsplit.trans (Nat.add_le_add hout
      (strictP_target_local S F hF tj tk tl gl htkl x v hvj.1 hmiss mₜ bₖ bₗ u hmₜ hbₖ hbₗ hu))
    exact hh.trans (by rw [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c : Bool, F tk (child x v c)=true := by
      intro c
      cases h : F tk (child x v c) with
      | false => exact False.elim (hmiss ⟨c,h⟩)
      | true => rfl
    have hlt : gk<gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      apply hvk
      refine ⟨htk,?_⟩
      simpa only [he] using hvj.2
    have hh := hsplit.trans (Nat.add_le_add hout
      (strictP_guard_local S F hF tj tk tl gj gk gl hglgk x v hvj htk hvk bₖ bₗ m₉ hbₖ hbₗ hm₉))
    exact hh.trans (by rw [if_pos hlt]; exact le_max_right _ _)

end
end ThreeBoundConditional

#print axioms ThreeBoundConditional.strictP_basic
#print axioms ThreeBoundConditional.strictP_refined


