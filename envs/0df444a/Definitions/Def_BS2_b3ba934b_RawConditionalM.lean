-- Prove2me | Definitions.Def_BS2_b3ba934b_RawConditionalM
-- name    : BS2_b3ba934b_RawConditionalM
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:05:13.170339+00:00
-- url     : https://prove2.me/theorems/fc09d040-2a30-417a-9c26-fc2b38859fa3
-- title:
--   Sensitivity separation: RawConditionalM (complete source module)
-- statement:
--   Complete Lean source module `RawConditionalM` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawConditionalM.lean; original SHA-256 ca6f1a7307ac35db8b20698ed1df32434b4feb9b357c43f1b2dc3d761af1b076; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Complete raw-M expression semantics, including the strict ordinary component
inside a genuinely graded weak parent. -/
import Definitions.Def_BS2_b3ba934b_RawConditionalBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem matched_middle (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (recipe : Fin n → Entry) (i j k : Fin n) (P : PairData S F i j) (Q : PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k)) (d : ℕ) : P.strong d=Q.weak d :=
  Fin.ext ((hm.strongThreshold d).trans (hn.weakThreshold d).symm)

theorem rawMExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k : Fin n) (P : PairData S F i j) (Q : PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    MBound (parent S F) i j k ((rawMExpr n degree (recipe i) (recipe j) (recipe k)).eval v) := by
  classical
  intro x hxj hxk
  have hb := rawBExpr_bound S F hF recipe i j P hm degree hd v hv x hxj
  dsimp only [rawMExpr]
  split_ifs with hs hbad hi
  · have he := matched_same_parent S F j k Q (recipe j) (recipe k) hn hs
    rw [he,hxk] at hxj
    contradiction
  · exact hb
  · have hjOrd : (recipe j).ordinary=true := by
      cases he : (recipe j).ordinary with
      | false => exact False.elim (hbad (Or.inl (by simp [he])))
      | true => rfl
    have hkOrd : (recipe k).ordinary=true := by
      cases he : (recipe k).ordinary with
      | false => exact False.elim (hbad (Or.inr (Or.inl (by simp [he]))))
      | true => rfl
    have heq : (recipe j).tolerance=(recipe k).tolerance := by
      by_contra he
      exact hbad (Or.inr (Or.inr he))
    have hq : S.tolerance j=S.tolerance k := by rw [hn.weakTolerance,hn.strongTolerance,heq]
    have hjParent := matched_ordinary_weak S F j k Q (recipe j) (recipe k) hn hjOrd
    have hkParent := matched_ordinary_strong S F j k Q (recipe j) (recipe k) hn hkOrd
    have hiParent := matched_ordinary_weak S F i j P (recipe i) (recipe j) hm hi
    rw [hjParent] at hxj
    rw [hkParent,← hq] at hxk
    have htij : P.weak 0 ≤ Q.weak 0 := by
      rw [← matched_middle S F recipe i j k P Q hm hn 0]
      exact P.targets 0 (Nat.zero_le _)
    have hh := primitiveMExpr_bound S F hF (P.weak 0) (Q.weak 0) (Q.strong 0)
      (S.guard i) (S.guard j) (S.guard k) (S.tolerance i) (S.tolerance j)
      (recipe j) (recipe k)
      (by rw [hn.weakThreshold,threshold_zero]) (by rw [hn.strongThreshold,threshold_zero])
      hn.weakGuard hn.strongGuard hn.weakTolerance.symm
      htij (Q.targets 0 (Nat.zero_le _)) P.guards Q.guards P.tolerances
      degree hd v hv x hxj hxk
    rw [hiParent]
    simpa only [hm.weakThreshold,threshold_zero,hm.weakGuard,hm.weakTolerance] using hh
  · have hjOrd : (recipe j).ordinary=true := by
      cases he : (recipe j).ordinary with
      | false => exact False.elim (hbad (Or.inl (by simp [he])))
      | true => rfl
    have hkOrd : (recipe k).ordinary=true := by
      cases he : (recipe k).ordinary with
      | false => exact False.elim (hbad (Or.inr (Or.inl (by simp [he]))))
      | true => rfl
    have heq : (recipe j).tolerance=(recipe k).tolerance := by
      by_contra he
      exact hbad (Or.inr (Or.inr he))
    have hq : S.tolerance j=S.tolerance k := by rw [hn.weakTolerance,hn.strongTolerance,heq]
    have hjParent := matched_ordinary_weak S F j k Q (recipe j) (recipe k) hn hjOrd
    have hkParent := matched_ordinary_strong S F j k Q (recipe j) (recipe k) hn hkOrd
    rw [hjParent] at hxj
    rw [hkParent,← hq] at hxk
    have htop : P.strong (S.tolerance j)=Q.weak 0 := by
      apply Fin.ext
      rw [hm.strongThreshold,hn.weakThreshold,threshold_zero]
      exact ordinary_threshold (recipe j) hjOrd _ (by rw [← hm.strongTolerance])
    have htij : P.weak (S.tolerance j) ≤ Q.weak 0 := by
      rw [← htop]
      exact P.targets _ le_rfl
    have hh := primitiveMExpr_bound S F hF (P.weak (S.tolerance j)) (Q.weak 0) (Q.strong 0)
      (S.guard i) (S.guard j) (S.guard k) (S.tolerance j) (S.tolerance j)
      (recipe j) (recipe k)
      (by rw [hn.weakThreshold,threshold_zero]) (by rw [hn.strongThreshold,threshold_zero])
      hn.weakGuard hn.strongGuard hn.weakTolerance.symm
      htij (Q.targets 0 (Nat.zero_le _)) P.guards Q.guards le_rfl
      degree hd v hv x hxj hxk
    have hsub := ordinary_component_down_subset S F hF (fun _ => P.weak) i
      (P.weak (S.tolerance j)) (S.guard i) (S.tolerance j) le_rfl P.tolerances
      (fun d hd => P.weakMono hd) P.weakDef x
    have hc := (Finset.card_le_card hsub).trans hh
    rw [eval_min]
    refine le_min hb ?_
    simpa only [hm.weakThreshold,hm.weakGuard,hm.strongTolerance] using hc

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawMExpr_bound


