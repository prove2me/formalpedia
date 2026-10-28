-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRecordAllowed
-- name    : BS2_b3ba934b_MinmaxRecordAllowed
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:57:05.330906+00:00
-- url     : https://prove2.me/theorems/413fb749-c3f1-4ad9-bcf5-d0bc9d5f49b5
-- title:
--   Sensitivity separation: MinmaxRecordAllowed (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRecordAllowed` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRecordAllowed.lean; original SHA-256 e94c1d2ab7f451c36fcea68eb3808e3c048928ad2c56489bf22b7d0d20f2b92f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Recipe-dependent min/max filters hold for every actual record. -/
import Definitions.Def_BS2_b3ba934b_MinmaxKindCost
import Definitions.Def_BS2_b3ba934b_RecordAllowedAlgorithm
import Definitions.Def_BS2_b3ba934b_TypeCountSums

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxQ2
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem recordAllowedFor_of (caps : Caps) (a c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record)
    (hallowed : allowedRecord caps c.tolerance r=true)
    (hguard : ∀ b, b ≤ c.tolerance → b < a.tolerance →
      a.lowerAt (b+1) ≤ c.lowerAt b → a.upperAt (b+1) ≤ c.upperAt b →
      r (3+b)=0 ∧ (b=0 → r 6=0) ∧ (b=1 → r 7=0))
    (hpositive : ∀ b, b ≤ c.tolerance → r b≠0 →
      ¬ (c.guard=a.lowerAt b ∧ c.guard=a.upperAt b)) :
    recordAllowedFor caps a c r=true := by
  unfold recordAllowedFor
  simp only [Bool.and_eq_true]
  constructor
  · refine ⟨hallowed,?_⟩
    apply List.all_eq_true.mpr
    intro b hb
    have hb' : b ≤ c.tolerance := Nat.le_of_lt_succ (List.mem_range.mp hb)
    by_cases he : b < a.tolerance ∧ a.lowerAt (b+1) ≤ c.lowerAt b ∧ a.upperAt (b+1) ≤ c.upperAt b
    · obtain ⟨hg,h0,h1⟩ := hguard b hb' he.1 he.2.1 he.2.2
      simp only [he,decide_true,Bool.not_true,Bool.false_or,hg,beq_self_eq_true,Bool.true_and]
      split_ifs with hz ho
      · simp [h0 hz]
      · simp [h1 ho]
      · rfl
    · simp [he]
  · apply List.all_eq_true.mpr
    intro b hb
    have hb' : b ≤ c.tolerance := Nat.le_of_lt_succ (List.mem_range.mp hb)
    by_cases hz : r b=0
    · simp [hz]
    · have he := hpositive b hb' hz
      simp [hz]
      tauto

theorem actual_recordAllowedFor (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hm : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hoff : parent S F i input=false)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j input w)
        (GuardCandidate S F P.strongLower P.strongUpper j input w) (tag w))
    (caps : Caps) (r : Q2Record)
    (hx : ∀ k : Fin 8, r k.val=typeCount (highHeads S F P.strongLower P.strongUpper j input) tag k)
    (hprefix : ∀ b, b ≤ c.tolerance → positivePrefix r b ≤ capPrefix caps r b) :
    recordAllowedFor caps a c r=true := by
  let H := highHeads S F P.strongLower P.strongUpper j input
  have hcQ : c.tolerance ≤ 2 := by rw [← hm.strongTolerance]; exact hQ
  have hz (kind : Fin 8) (h : ∀ w ∈ H, tag w≠kind) : r kind.val=0 :=
    (hx kind).trans (typeCount_zero_of_forbidden H tag kind h)
  have hguardZero (b : ℕ) (hba : b < a.tolerance)
      (ht : a.lowerAt (b+1) ≤ c.lowerAt b) (hu : a.upperAt (b+1) ≤ c.upperAt b)
      (kind : Fin 8) (hkind : 3 ≤ kind.val) (hlevel : guardLevel kind.val=b) : r kind.val=0 := by
    apply hz kind
    intro w hw he
    have hkw := hk w hw
    rw [he] at hkw
    have hg := kind_guard _ _ kind hkw hkind
    rw [hlevel] at hg
    have hbi : b+1 ≤ S.tolerance i := by rw [hm.weakTolerance]; omega
    apply guard_forbidden_next S F hF i j P input hoff w b hg hbi
    · change (P.weakLower (b+1)).val ≤ (P.strongLower b).val
      rw [hm.weakLower (b+1) hbi,hm.strongLower b hg.1]
      exact ht
    · change (P.weakUpper (b+1)).val ≤ (P.strongUpper b).val
      rw [hm.weakUpper (b+1) hbi,hm.strongUpper b hg.1]
      exact hu
  apply recordAllowedFor_of caps a c r
  · apply ThreeBoundRecordAllowedAlgorithm.allowedRecord_of caps c.tolerance r
    · intro hq1
      have hS : S.tolerance j ≤ 1 := by rw [hm.strongTolerance,hq1]
      have hne (kind : Fin 8) (he : kind.val=2 ∨ kind.val=5 ∨ kind.val=7) : r kind.val=0 := by
        apply hz kind
        intro w hw heq
        have h := kind_tolerance_one S F P.strongLower P.strongUpper j input w hS (tag w) (hk w hw)
        have hv := congrArg Fin.val heq
        rcases he with h2 | h5 | h7 <;> omega
      exact ⟨hne ⟨2,by omega⟩ (Or.inl rfl),
        hne ⟨5,by omega⟩ (Or.inr (Or.inl rfl)),hne ⟨7,by omega⟩ (Or.inr (Or.inr rfl))⟩
    · exact hprefix
  · intro b hb hba ht hu
    refine ⟨?_,?_,?_⟩
    · exact hguardZero b hba ht hu ⟨3+b,by omega⟩ (by change 3 ≤ 3+b; omega)
        (by simp [guardLevel]; omega)
    · intro hb0
      subst b
      exact hguardZero 0 hba ht hu ⟨6,by omega⟩ (by change 3 ≤ 6; decide) (by norm_num [guardLevel])
    · intro hb1
      subst b
      exact hguardZero 1 hba ht hu ⟨7,by omega⟩ (by change 3 ≤ 7; decide) (by norm_num [guardLevel])
  · intro b hb hnz he
    let kind : Fin 8 := ⟨b,by omega⟩
    have hpos : 0 < typeCount H tag kind := by rw [← hx kind]; exact Nat.pos_of_ne_zero hnz
    obtain ⟨w,hw,heq⟩ := nonempty_type_of_count_pos H tag kind hpos
    have hkw := hk w hw
    rw [heq] at hkw
    have hp := kind_positive 2 _ _ kind hkw (by dsimp [kind]; omega)
    have hbj : b ≤ S.tolerance j := by rw [hm.strongTolerance]; exact hb
    have hbi := hbj.trans P.tolerances
    have ht : S.guard j=P.weakLower b := Fin.ext (by rw [hm.strongGuard,hm.weakLower b hbi]; exact he.1)
    have hu : S.guard j=P.weakUpper b := Fin.ext (by rw [hm.strongGuard,hm.weakUpper b hbi]; exact he.2)
    have hmm : mm F (P.weakLower b) (P.weakUpper b) (child input w false) (child input w true)=true := by
      rw [← ht,← hu]
      simp only [mm,hp.2 false,hp.2 true,Bool.and_self,Bool.or_self]
    have hf := weak_target_false S F hF i j P input hoff w b hbj hp.1.2.1.le
    rw [hf] at hmm
    contradiction

end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.actual_recordAllowedFor


