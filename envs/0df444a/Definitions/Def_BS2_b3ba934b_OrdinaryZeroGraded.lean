-- Prove2me | Definitions.Def_BS2_b3ba934b_OrdinaryZeroGraded
-- name    : BS2_b3ba934b_OrdinaryZeroGraded
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:10:05.327497+00:00
-- url     : https://prove2.me/theorems/96b448e7-c52e-43e5-8f0d-796b794225ae
-- title:
--   Sensitivity separation: OrdinaryZeroGraded (complete source module)
-- statement:
--   Complete Lean source module `OrdinaryZeroGraded` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/OrdinaryZeroGraded.lean; original SHA-256 a435aeb4309cab306eb524503c73c5518095ff821e5fb850d5c5ac6b421a6754; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The q=0 ordinary formula for a graded weak parent. A permissible next
weak tier eliminates strong guard candidates, while target repairs still
use the weak tier at zero. -/
import Definitions.Def_BS2_b3ba934b_OrdinaryNoGuards
import Definitions.Def_BS2_b3ba934b_OrdinaryNumericA

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]

theorem ordinary_zero_noguards_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b : ℕ) (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (x : ((Fin 10007 × Bool) × I) → Bool)
    (hx : ordinaryParent S F ta ga 0 x=false)
    (hng : ∀ w, (∀ c : Bool, F tb (child x w c)=true) → (guardFailures S F gb x w).card ≠ 1) :
    (flipsTo (ordinaryParent S F tb gb 0) true x).card ≤ max (22*b) (a+19*b) := by
  have hrel : ∀ v w, ThreeBoundOrdinarySelected.tournament.Adj v w ↔ S.Adj v w := by
    intro v w
    rw [hAdj]
    rfl
  have hlab : ∀ v w, finTwoEquiv (ThreeBoundOrdinarySelected.label v w)=S.label v w := by
    intro v w
    rw [hLabel]
    exact selected_archive_label v w
  let xx : ((Fin 10007 × Fin 2) × I) → Bool := fun a => x (ordinaryCoordEquiv a)
  have hchild (w : Fin 10007) (c : Fin 2) :
      ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild xx w c=child x w (finTwoEquiv c) := rfl
  have hfailed (w : Fin 10007) :
      ThreeBoundOrdinaryArchive.Sensitivity2075.failedGuards ThreeBoundOrdinarySelected.tournament
        ThreeBoundOrdinarySelected.label F gb xx w=guardFailures S F gb x w := by
    ext z
    simp only [ThreeBoundOrdinaryArchive.Sensitivity2075.failedGuards,guardFailures,
      Finset.mem_filter,Finset.mem_univ,true_and,hchild,hrel,hlab]
  have hG : ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantGuards ThreeBoundOrdinarySelected.tournament
      ThreeBoundOrdinarySelected.label F tb gb 0 xx=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨_,hmiss,hcount⟩ := Finset.mem_filter.mp hw
    have htold := (ThreeBoundOrdinaryArchive.Sensitivity2075.missingTargets_empty F tb xx w).mp hmiss
    have hboth : ∀ c : Bool, F tb (child x w c)=true := by
      intro c
      have hh := htold (finTwoEquiv.symm c)
      simpa only [hchild,Equiv.apply_symm_apply] using hh
    exact hng w hboth (by simpa only [hfailed] using hcount)
  rw [ordinary_archive_flips_card S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F tb gb 0 true x]
  rw [← ordinary_archive_eq S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F ta ga 0] at hx
  dsimp only [reindex] at hx
  exact ThreeBoundOrdinaryArchive.ZT.zero_tolerance_of_no_guards
    ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    F ⟨fun {i j} {y} hij hy => hF i j hij y hy⟩ ta tb ga gb ht hg hga a b ha hb
    (ThreeBoundOrdinarySelected.labelCaps.ordinary 0 (by decide))
    ThreeBoundOrdinarySelected.labelCaps.source xx hx hG

/-- Exact q=0 branch of raw A, including its next-tier guard exclusion gate. -/
theorem rawAExpr_zero_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (records : List (List ℕ)) (hq : (recipe j).tolerance=0)
    (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j ((rawAExpr n ordinaryCaps10007 records (recipe i) (recipe j)).eval v) := by
  intro x hx
  simp only [rawAExpr,hq,ite_true]
  by_cases hnext : 1 ≤ (recipe i).tolerance ∧ (recipe i).threshold 1 ≤ (recipe j).t0
  · rw [if_pos hnext]
    have ht : P.weak 0 ≤ P.strong 0 := P.targets 0 (Nat.zero_le _)
    have h1 : 1 ≤ S.tolerance i := by simpa only [hm.weakTolerance] using hnext.1
    have ht1 : P.weak 1 ≤ P.strong 0 := by
      change (P.weak 1).val ≤ (P.strong 0).val
      simpa only [hm.weakThreshold,hm.strongThreshold,threshold_zero] using hnext.2
    have hcomp : ordinaryParent S F (P.weak 0) (S.guard i) 0 x=false := by
      cases he : ordinaryParent S F (P.weak 0) (S.guard i) 0 x with
      | false => rfl
      | true =>
          have hh := ordinary_component_accepts S F hF (fun _ => P.weak) i (P.weak 0) (S.guard i) 0
            le_rfl (Nat.zero_le _) (fun d hd => P.weakMono hd) P.weakDef x he
          rw [hx] at hh
          contradiction
    have hng (w : Fin 10007) (hb : ∀ c : Bool, F (P.strong 0) (child x w c)=true) :
        (guardFailures S F (S.guard j) x w).card ≠ 1 := by
      intro hcount
      have hc : (failed S F i x w).card ≤ 1 :=
        (Finset.card_le_card (failed_weak_subset S F hF i j P x w)).trans (le_of_eq hcount)
      have hh := parent_true_of_count_bound S F hF (fun _ => P.weak) i P.weakMono P.weakDef x w 1 h1 hc
        (hF _ _ ht1 _ (hb false)) (hF _ _ ht1 _ (hb true))
      rw [hx] at hh
      contradiction
    have ha := plusExpr_bound_all F hF v hv (S.guard j) (P.weak 0) (P.strong 0) ht
    have hb := aExpr_bound F v hv (S.guard j) (P.strong 0) (P.guardTarget 0 (Nat.zero_le _))
    have hh := ordinary_zero_noguards_bound S hAdj hLabel F hF (P.weak 0) (P.strong 0)
      (S.guard i) (S.guard j) ht P.guards (P.weakGuardTarget 0 (Nat.zero_le _)) _ _ ha hb x hcomp hng
    have hjParent := matched_ordinary_strong S F i j P (recipe i) (recipe j) hm (ordinary_of_zero _ hq)
    have hjq : S.tolerance j=0 := hm.strongTolerance.trans hq
    rw [hjq] at hjParent
    rw [hjParent,ordinaryAExpr_zero_strict v _ _ 1 _ _ (by decide)]
    simpa only [hm.weakThreshold,hm.strongThreshold,threshold_zero,hm.strongGuard] using hh
  · rw [if_neg hnext]
    have ht : (recipe i).threshold 0 ≤ (recipe j).t0 := by
      have hh := P.targets 0 (Nat.zero_le _)
      change (P.weak 0).val ≤ (P.strong 0).val at hh
      simpa only [hm.weakThreshold,hm.strongThreshold,threshold_zero] using hh
    have hh := ordinaryComponentAExpr_bound S hAdj hLabel F hF recipe i j P hm 0
      (Nat.zero_le _) (by rw [hq]) (by rw [hq]; omega) ht (ordinary_of_zero _ hq) v hv x hx
    simpa only [threshold_zero,hq] using hh

/-- Ordinary q≥3 branch of raw A. The weaker tolerance is also at least three,
so its threshold is constant at every permitted weak budget. -/
theorem rawAExpr_large_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (records : List (List ℕ)) (hq : 3 ≤ (recipe j).tolerance) (hq8 : (recipe j).tolerance ≤ 8)
    (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j ((rawAExpr n ordinaryCaps10007 records (recipe i) (recipe j)).eval v) := by
  have hqi : (recipe j).tolerance ≤ (recipe i).tolerance := by
    simpa only [hm.weakTolerance,hm.strongTolerance] using P.tolerances
  have hqi3 : 3 ≤ (recipe i).tolerance := hq.trans hqi
  have he : (recipe i).threshold (recipe i).tolerance=(recipe i).t0 := by simp [Entry.threshold,hqi3]
  have ht : (recipe i).threshold (recipe i).tolerance ≤ (recipe j).t0 := by
    rw [he]
    have hh := P.targets 0 (Nat.zero_le _)
    change (P.weak 0).val ≤ (P.strong 0).val at hh
    simpa only [hm.weakThreshold,hm.strongThreshold,threshold_zero] using hh
  have hord : (recipe j).ordinary=true := by simp [Entry.ordinary,hq]
  have hh := ordinaryComponentAExpr_bound S hAdj hLabel F hF recipe i j P hm
    (recipe i).tolerance le_rfl hqi hq8 ht hord v hv
  simpa only [rawAExpr,if_neg (by omega : (recipe j).tolerance≠0),if_pos hq,he] using hh

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawAExpr_zero_bound
#print axioms ThreeBoundConditionalNumeric.rawAExpr_large_bound


