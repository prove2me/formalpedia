-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxStrictUnion
-- name    : BS2_b3ba934b_MinmaxStrictUnion
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:38:05.568418+00:00
-- url     : https://prove2.me/theorems/9dbea224-e905-43b6-b894-7b1bf8c76e99
-- title:
--   Sensitivity separation: MinmaxStrictUnion (complete source module)
-- statement:
--   Complete Lean source module `MinmaxStrictUnion` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxStrictUnion.lean; original SHA-256 8a21f7eb563e5a3438be926a180cf61a7a958b80f94507dd304561b820079d88; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Strict conditional union transfer for a symmetric min/max middle witness.
The target-repair branch chooses its orientation after locating the missing child. -/
import Definitions.Def_BS2_b3ba934b_MinmaxUnionRows

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem oriented_zero_union_of_boundary (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (G : (((V × Bool) × I) → Bool) → Bool)
    (ti ui tj uj tk uk tl gi gj gk gl : L)
    (htiu : ti ≤ ui) (htij : ti ≤ tj) (huij : ui ≤ uj)
    (hujl : uj ≤ tl) (htkl : tk ≤ tl) (hukl : uk ≤ tl)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (degree b0 b1 a dt dg R : ℕ)
    (hb0 : BBound F ti tl b0) (hb1 : BBound F ui tl b1) (ha : ABound F gl gi a)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((V × Bool) × I) → Bool) (v : V) (hd : (outgoing S v).card=degree)
    (hjmm : mm F tj uj (child x v false) (child x v true)=true)
    (hjguard : (guardFailures S F gj x v).card=0)
    (hk : ∀ c, ¬orientedRow S F tk uk gk 0 x v c)
    (haccept : ∀ c y, orientedRow S F ti ui gi 0 y v c → G y=true)
    (hR : ∀ c, orientedRow S F tj uj gj 0 x v c →
      (flipsTo (orientedRowBool S F ti ui gi 0 v c) false x).card ≤ R) :
    (flipsTo G false x ∪ flipsTo (ordinaryParent S F tl gl 0) true x).card ≤
      max R (max (if tj<tk then b1+degree*a+dt else 0)
        (if gk<gj then b0+b1+(degree-1)*a+dg else 0)) := by
  have hweak : ∀ c, orientedRow S F tj uj gj 0 x v c → orientedRow S F ti ui gi 0 x v c := by
    intro c hc
    exact ⟨hF _ _ htij _ hc.1,hF _ _ huij _ hc.2.1,
      (Finset.card_le_card (guardFailures_mono S F hF gi gj hgjgi x v)).trans hc.2.2⟩
  have hvl : ¬ordinaryRow S F tl gl 0 x v := by
    intro hr
    apply hk false
    exact ⟨hF _ _ htkl _ (hr.1 true),hF _ _ hukl _ (hr.1 false),
      (Finset.card_le_card (guardFailures_mono S F hF gk gl hglgk x v)).trans hr.2⟩
  obtain ⟨cMain,hloMain,hhiMain⟩ := mm_orientation F tj uj x v hjmm
  have hjMain : orientedRow S F tj uj gj 0 x v cMain := ⟨hloMain,hhiMain,hjguard.le⟩
  by_cases hcT : StrictTargetCandidate S F tl gl x v
  · obtain ⟨c₀,hfalse,hother,hgl⟩ := hcT
    have hlow : F tj (child x v c₀)=true := by
      have hh := (mm_true F tj uj _ _).1 hjmm
      cases c₀
      · exact hh.1
      · exact hh.2.1
    have hhigh : F uj (child x v (!c₀))=true :=
      hF _ _ hujl _ (hother (!c₀) (by cases c₀ <;> decide))
    have hj : orientedRow S F tj uj gj 0 x v (!c₀) := by
      exact ⟨by simpa only [Bool.not_not] using hlow,hhigh,hjguard.le⟩
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
        apply hk (!c₀)
        refine ⟨by simpa only [Bool.not_not] using h,?_,by simp [hglk]⟩
        exact hF _ _ hukl _ (hother (!c₀) (by cases c₀ <;> decide))
    have hlt : tj<tk := true_false_lt F hF tj tk _ hlow hkt
    have hsub := oriented_union_subset S hT F hF G ti ui tl gi gl htiu hgil hgli x v (!c₀) (haccept (!c₀))
    have hbound := oriented_union_target_bound S F hF ti ui tl gi gl degree b1 a dt hb1 ha
      x v c₀ hd (hweak (!c₀) hj) hfalse hother hgl (hdt _ hlow hkt)
    apply ((Finset.card_le_card hsub).trans hbound).trans
    rw [if_pos hlt]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · by_cases hcG : StrictGuardCandidate S F tl gl x v
    · obtain ⟨ht,w₀,hgl⟩ := hcG
      have hwmem : w₀ ∈ guardFailures S F gl x v := by rw [hgl]; simp
      have hadj := ((mem_guardFailures S F gl x v w₀).1 hwmem).1
      have hjoff : F gj (child x w₀ (S.label v w₀))=false := by
        cases h : F gj (child x w₀ (S.label v w₀)) with
        | false => rfl
        | true =>
          have hh := (mem_guardFailures S F gj x v w₀).2 ⟨hadj,h⟩
          rw [Finset.card_eq_zero.mp hjguard] at hh
          exact False.elim (Finset.notMem_empty _ hh)
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
            have hh := ((mem_guardFailures S F gk x v w₀).1 hw).2
            rw [h] at hh
            contradiction
          apply False.elim
          apply hk cMain
          exact ⟨hF _ _ htkl _ (ht (!cMain)),hF _ _ hukl _ (ht cMain),by simp [hempty]⟩
      have hlt : gk<gj := true_false_lt F hF gk gj _ hkon hjoff
      have hlocal : (flipsTo (F gi) true (child x w₀ (S.label v w₀)) ∪
          flipsTo (F gl) false (child x w₀ (S.label v w₀))).card ≤ dg := by
        simpa only [Finset.union_comm] using hdg _ hkon hjoff
      have hsub := oriented_union_subset S hT F hF G ti ui tl gi gl htiu hgil hgli x v cMain (haccept cMain)
      have hbound := oriented_union_guard_bound S F hF ti ui tl gi gl degree b0 b1 a dg hb0 hb1 ha
        x v w₀ cMain hd (hweak cMain hjMain) ht hgl hlocal
      apply ((Finset.card_le_card hsub).trans hbound).trans
      rw [if_pos hlt]
      exact (le_max_right _ _).trans (le_max_right _ _)
    · have hsub := oriented_union_subset S hT F hF G ti ui tl gi gl htiu hgil hgli x v cMain (haccept cMain)
      rw [strict_no_repair S F tl gl x v hvl hcT hcG,Finset.union_empty] at hsub
      exact ((Finset.card_le_card hsub).trans (hR cMain hjMain)).trans (le_max_left _ _)

theorem oriented_strictD (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (G : (((V × Bool) × I) → Bool) → Bool)
    (ti ui tj uj tk uk tl gi gj gk gl : L)
    (htiu : ti ≤ ui) (htij : ti ≤ tj) (huij : ui ≤ uj)
    (hujl : uj ≤ tl) (htkl : tk ≤ tl) (hukl : uk ≤ tl)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (degree aM m0 m1 bm0 bm1 p b0 b1 aD dt dg : ℕ)
    (haM : ABound F gj gi aM) (hm0 : MBound F ti tj tk m0) (hm1 : MBound F ui uj uk m1)
    (hbm0 : BBound F ti tk bm0) (hbm1 : BBound F ui uk bm1) (hp : PBound F gk gj gi p)
    (hb0 : BBound F ti tl b0) (hb1 : BBound F ui tl b1) (haD : ABound F gl gi aD)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((V × Bool) × I) → Bool) (v : V) (hd : (outgoing S v).card=degree)
    (hjmm : mm F tj uj (child x v false) (child x v true)=true)
    (hjguard : (guardFailures S F gj x v).card=0)
    (hk : ∀ c, ¬orientedRow S F tk uk gk 0 x v c)
    (haccept : ∀ c y, orientedRow S F ti ui gi 0 y v c → G y=true) :
    (flipsTo G false x ∪ flipsTo (ordinaryParent S F tl gl 0) true x).card ≤
      max (pairMCost degree 0 tj uj tk uk gj gk aM m0 m1 bm0 bm1 p)
        (max (if tj<tk then b1+degree*aD+dt else 0)
          (if gk<gj then b0+b1+(degree-1)*aD+dg else 0)) := by
  apply oriented_zero_union_of_boundary S hT F hF G ti ui tj uj tk uk tl gi gj gk gl htiu htij huij
    hujl htkl hukl hgjgi hgkgj hglgk hgil hgli degree b0 b1 aD dt dg _ hb0 hb1 haD hdt hdg
    x v hd hjmm hjguard hk haccept
  intro c hc
  exact oriented_pairM_row S F hF ti ui tj uj tk uk gi gj gk htij huij hgjgi hgkgj 0 degree
    x v c hc hjguard (hk c) hd aM m0 m1 bm0 bm1 p haM hm0 hm1 hbm0 hbm1 hp

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.oriented_zero_union_of_boundary
#print axioms ThreeBoundMinmaxTransfer.oriented_strictD


