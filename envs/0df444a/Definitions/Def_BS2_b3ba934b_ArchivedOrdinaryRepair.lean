-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryRepair
-- name    : BS2_b3ba934b_ArchivedOrdinaryRepair
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:36:50.985232+00:00
-- url     : https://prove2.me/theorems/57d7f89b-d500-4a4f-98d0-10c4272c5a9c
-- title:
--   Sensitivity separation: ArchivedOrdinaryRepair (complete source module)
-- statement:
--   Complete Lean source module `ArchivedOrdinaryRepair` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedOrdinaryRepair.lean; original SHA-256 1dc9e9066ae1aaa070f39f899af9c64a43193aae6b976a2927e148ae06da4a2a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryDefinitions

open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_Sensitivity2075_tolerant_repair_cases.lean -/
set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)









end Tournament



















end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













@[simp] theorem mem_missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) (c : Fin r) :
    c ∈ missingTargets F A x i ↔ F A (recursiveChild x i c) = false := by
  simp [missingTargets]

@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]

theorem missingTargets_empty {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    missingTargets F A x i = ∅ ↔ ∀ c, F A (recursiveChild x i c) = true := by
  simp [missingTargets, Finset.filter_eq_empty_iff]







section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem guard_mem_flip_iff {v : Fin k} (hne : (v, label i v) ≠ (j,c)) :
    v ∈ failedGuards T label F G (_root_.OAI.Paper320.flip x {((j,c),a)}) i ↔
      v ∈ failedGuards T label F G x i := by
  simp only [mem_failedGuards, recursiveChild_flip_other x j v c (label i v) a hne]



theorem guards_subset_flip :
    failedGuards T label F G x i ⊆
      insert j (failedGuards T label F G (_root_.OAI.Paper320.flip x {((j,c),a)}) i) := by
  intro v hv
  by_cases he : v = j
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr
      ((guard_mem_flip_iff T label F G x i j c a (by
        intro hh; exact he (congrArg Prod.fst hh))).mpr hv))



theorem guards_card_le_flip :
    (failedGuards T label F G x i).card ≤
      (failedGuards T label F G (_root_.OAI.Paper320.flip x {((j,c),a)}) i).card + 1 :=
  (Finset.card_le_card (guards_subset_flip T label F G x i j c a)).trans
    (Finset.card_insert_le _ _)

theorem guards_flip_own :
    failedGuards T label F G (_root_.OAI.Paper320.flip x {((i,c),a)}) i =
      failedGuards T label F G x i := by
  ext v
  by_cases hv : T.Adj i v
  · exact guard_mem_flip_iff T label F G x i i c a (by
      intro hh; exact T.ne_of_adj hv (congrArg Prod.fst hh).symm)
  · simp only [mem_failedGuards, hv, false_and]

theorem guard_decrease_location
    (hdec : (failedGuards T label F G (_root_.OAI.Paper320.flip x {((j,c),a)}) i).card <
      (failedGuards T label F G x i).card) :
    T.Adj i j ∧ c = label i j ∧ F G (recursiveChild x j c) = true ∧
      F G (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) = false := by
  obtain ⟨v, hv, hv'⟩ := Finset.exists_mem_notMem_of_card_lt_card hdec
  have hloc : (v, label i v) = (j,c) := by
    by_contra hh
    exact hv' ((guard_mem_flip_iff T label F G x i j c a hh).mpr hv)
  have hvj : v = j := congrArg Prod.fst hloc
  subst v
  have hcl : c = label i j := (congrArg Prod.snd hloc).symm
  subst c
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F G x i j).mp hv
  refine ⟨hij, rfl, hon, ?_⟩
  have hoff : F G (recursiveChild (_root_.OAI.Paper320.flip x {((j,label i j),a)}) j (label i j)) = false := by
    simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hv'
  simpa only [recursiveChild_flip_same] using hoff



end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem _root_.ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases
    (hoff : tolerantRow T label F A G q x i = false)
    (hon : tolerantRow T label F A G q (_root_.OAI.Paper320.flip x {((j,c),a)}) i = true) :
    (i ∈ tolerantTargets T label F A G q x ∧ j = i ∧
      F A (recursiveChild x j c) = false ∧
      F A (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ tolerantGuards T label F A G q x ∧ T.Adj i j ∧ c = label i j ∧
      F G (recursiveChild x j c) = true ∧
      F G (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) = false) := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F A G q _ i).mp hon
  by_cases hji : j = i
  · subst j
    rw [guards_flip_own] at hg
    have hton : F A (_root_.OAI.Paper320.flip (recursiveChild x i c) {a}) = true := by
      simpa only [recursiveChild_flip_same] using ht c
    have hother : ∀ d, d ≠ c → F A (recursiveChild x i d) = true := by
      intro d hdc
      simpa only [recursiveChild_flip_other x i i c d a (by
        intro he; exact hdc (congrArg Prod.snd he))] using ht d
    have htoff : F A (recursiveChild x i c) = false := by
      cases hc : F A (recursiveChild x i c)
      · rfl
      · have hrow := (tolerantRow_true T label F A G q x i).mpr ⟨?_, hg⟩
        · simp [hoff] at hrow
        · intro d
          by_cases hd : d = c
          · simpa only [hd] using hc
          · exact hother d hd
    have hmissing : missingTargets F A x i = {c} := by
      ext d
      simp only [mem_missingTargets, Finset.mem_singleton]
      constructor
      · intro hd
        by_contra hne
        have hh := hother d hne
        simp [hd] at hh
      · rintro rfl
        exact htoff
    exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hmissing], hg⟩,
      rfl, htoff, hton⟩
  · have htargets : ∀ d, F A (recursiveChild x i d) = true := by
      intro d
      simpa only [recursiveChild_flip_other x j i c d a (by
        intro he; exact hji (congrArg Prod.fst he).symm)] using ht d
    have hcount : q < (failedGuards T label F G x i).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F A G q x i).mpr
        ⟨htargets, by omega⟩
      simp [hoff] at hh
    have hupper := guards_card_le_flip T label F G x i j c a
    have hexact : (failedGuards T label F G x i).card = q+1 := by omega
    have hl := guard_decrease_location T label F G x i j c a (by omega)
    exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (missingTargets_empty F A x i).mpr htargets, hexact⟩, hl⟩



end RowFlips

section Nesting






end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

end ThreeBoundOrdinaryArchive


