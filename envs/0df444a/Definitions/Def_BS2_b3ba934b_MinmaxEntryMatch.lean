-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxEntryMatch
-- name    : BS2_b3ba934b_MinmaxEntryMatch
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:40:39.835825+00:00
-- url     : https://prove2.me/theorems/ef02505a-438a-40c1-a2fc-b1e912f106c2
-- title:
--   Sensitivity separation: MinmaxEntryMatch (complete source module)
-- statement:
--   Complete Lean source module `MinmaxEntryMatch` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxEntryMatch.lean; original SHA-256 e1fbb1954cacdebb48a91e574b50614244ec228f9d1aa17da86d086910652779; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The exact link between finite numeric min/max entries and Boolean recipes. -/
import Definitions.Def_BS2_b3ba934b_MinmaxExpressions
import Definitions.Def_BS2_b3ba934b_MinmaxDParent
import Definitions.Def_BS2_b3ba934b_MinmaxOrdinaryComponent

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

structure EntryMatch (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry) : Prop where
  weakTolerance : S.tolerance i=a.tolerance
  strongTolerance : S.tolerance j=c.tolerance
  weakGuard : (S.guard i).val=a.guard
  strongGuard : (S.guard j).val=c.guard
  weakLower : ∀ d, d ≤ S.tolerance i → (P.weakLower d).val=a.lowerAt d
  weakUpper : ∀ d, d ≤ S.tolerance i → (P.weakUpper d).val=a.upperAt d
  strongLower : ∀ d, d ≤ S.tolerance j → (P.strongLower d).val=c.lowerAt d
  strongUpper : ∀ d, d ≤ S.tolerance j → (P.strongUpper d).val=c.upperAt d

theorem plain_spec (e : Entry) (he : e.plain=true) (d : ℕ) (hd : d ≤ e.tolerance) :
    e.lowerAt d=e.upperAt d := by
  exact beq_iff_eq.mp (List.all_eq_true.mp he d (List.mem_range.mpr (by omega)))

theorem ordinary_spec (e : Entry) (he : e.ordinary=true) (d : ℕ) (hd : d ≤ e.tolerance) :
    e.lowerAt d=e.lowerAt 0 ∧ e.upperAt d=e.lowerAt 0 := by
  have hh := List.all_eq_true.mp he d (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true,beq_iff_eq] using hh

theorem ordinary_of_zero_plain (e : Entry) (hq : e.tolerance=0) (he : e.plain=true) :
    e.ordinary=true := by
  apply List.all_eq_true.mpr
  intro d hd
  have hd0 : d=0 := by have hh := List.mem_range.mp hd; omega
  subst d
  simp only [beq_self_eq_true,Bool.true_and,beq_iff_eq]
  exact (plain_spec e he 0 (Nat.zero_le _)).symm

theorem same_spec (e f : Entry) (he : e.same f=true) :
    e.tolerance=f.tolerance ∧ e.guard=f.guard ∧
      ∀ d, d ≤ e.tolerance → e.lowerAt d=f.lowerAt d ∧ e.upperAt d=f.upperAt d := by
  simp only [Entry.same,Bool.decide_and,Bool.and_eq_true,decide_eq_true_eq] at he
  obtain ⟨hq,hg,ht⟩ := he
  refine ⟨hq,hg,?_⟩
  intro d hd
  have hh := List.all_eq_true.mp ht d (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true,beq_iff_eq] using hh

theorem matched_middle_lower (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (recipe : Fin n → Entry) (i j k : Fin n)
    (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k)) (d : ℕ) (hd : d ≤ S.tolerance j) :
    P.strongLower d=Q.weakLower d := Fin.ext ((hm.strongLower d hd).trans (hn.weakLower d hd).symm)

theorem matched_middle_upper (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (recipe : Fin n → Entry) (i j k : Fin n)
    (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k)) (d : ℕ) (hd : d ≤ S.tolerance j) :
    P.strongUpper d=Q.weakUpper d := Fin.ext ((hm.strongUpper d hd).trans (hn.weakUpper d hd).symm)

theorem matched_ordinary_weak (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (ha : a.ordinary=true) :
    parent S F i=ordinaryParent S F (P.weakLower 0) (S.guard i) (S.tolerance i) := by
  apply ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
  intro d hd u z
  obtain ⟨hl,hu⟩ := ordinary_spec a ha d (by simpa only [hm.weakTolerance] using hd)
  have hl' : P.weakLower d=P.weakLower 0 := Fin.ext (by rw [hm.weakLower d hd,hm.weakLower 0 (Nat.zero_le _)]; exact hl)
  have hu' : P.weakUpper d=P.weakLower 0 := Fin.ext (by rw [hm.weakUpper d hd,hm.weakLower 0 (Nat.zero_le _)]; exact hu)
  rw [P.weakDef,hl',hu',mm_same]

theorem matched_ordinary_strong (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (hc : c.ordinary=true) :
    parent S F j=ordinaryParent S F (P.strongLower 0) (S.guard j) (S.tolerance j) := by
  apply ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
  intro d hd u z
  obtain ⟨hl,hu⟩ := ordinary_spec c hc d (by simpa only [hm.strongTolerance] using hd)
  have hl' : P.strongLower d=P.strongLower 0 := Fin.ext (by rw [hm.strongLower d hd,hm.strongLower 0 (Nat.zero_le _)]; exact hl)
  have hu' : P.strongUpper d=P.strongLower 0 := Fin.ext (by rw [hm.strongUpper d hd,hm.strongLower 0 (Nat.zero_le _)]; exact hu)
  rw [P.strongDef,hl',hu',mm_same]

theorem matched_same_parent (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (hs : a.same c=true) : parent S F i=parent S F j := by
  obtain ⟨hq,hg,ht⟩ := same_spec a c hs
  have hq' : S.tolerance i=S.tolerance j := by rw [hm.weakTolerance,hm.strongTolerance,hq]
  have hg' : S.guard i=S.guard j := Fin.ext (by rw [hm.weakGuard,hm.strongGuard,hg])
  have hlow (d : ℕ) (hd : d ≤ S.tolerance i) : P.weakLower d=P.strongLower d := by
    apply Fin.ext
    rw [hm.weakLower d hd,hm.strongLower d (by omega)]
    exact (ht d (by simpa only [hm.weakTolerance] using hd)).1
  have hupp (d : ℕ) (hd : d ≤ S.tolerance i) : P.weakUpper d=P.strongUpper d := by
    apply Fin.ext
    rw [hm.weakUpper d hd,hm.strongUpper d (by omega)]
    exact (ht d (by simpa only [hm.weakTolerance] using hd)).2
  funext x
  have hf (w : V) : failed S F i x w=failed S F j x w := by simp only [failed,hg']
  have he : parent S F i x=true ↔ parent S F j x=true := by
    rw [parent_true_iff,parent_true_iff]
    constructor
    · rintro ⟨w,hc,hh⟩
      refine ⟨w,by simpa only [← hf,← hq'] using hc,?_⟩
      rw [P.strongDef,← hf,← hlow _ hc,← hupp _ hc,← P.weakDef]
      exact hh
    · rintro ⟨w,hc,hh⟩
      have hc' : (failed S F i x w).card ≤ S.tolerance i := by simpa only [hf,hq'] using hc
      refine ⟨w,hc',?_⟩
      rw [P.weakDef,hlow _ hc',hupp _ hc',hf,← P.strongDef]
      exact hh
  cases h1 : parent S F i x <;> cases h2 : parent S F j x <;> simp_all

theorem eval_ite {m : ℕ} (v : Profile m) (p : Prop) [Decidable p] (a b : Expr m) :
    (if p then a else b).eval v=if p then a.eval v else b.eval v := by
  split_ifs <;> rfl

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.matched_same_parent
#print axioms ThreeBoundMinmaxNumeric.matched_ordinary_strong


