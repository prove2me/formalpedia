-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxQ2Types
-- name    : BS2_b3ba934b_MinmaxQ2Types
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:40:49.666251+00:00
-- url     : https://prove2.me/theorems/38eded1c-5780-4ae1-9636-5cad4cbfe868
-- title:
--   Sensitivity separation: MinmaxQ2Types (complete source module)
-- statement:
--   Complete Lean source module `MinmaxQ2Types` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxQ2Types.lean; original SHA-256 43ceccecd356e1288f72565c26dd1e022fe0f565822a19f58779e218f6c78658; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact q2 type and prefix identities for actual min/max candidates. -/
import Definitions.Def_BS2_b3ba934b_MinmaxPrefixCaps
import Definitions.Def_BS2_b3ba934b_RecordCapStats

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxQ2
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem budget_eq (k : Fin 8) : ThreeBoundHighTypes.budget 2 k=ThreeBoundQ2.budget k := by
  fin_cases k <;> rfl

theorem isGuard_eq (k : Fin 8) : ThreeBoundHighTypes.isGuard 2 k=ThreeBoundQ2.isGuard k := by
  fin_cases k <;> rfl

theorem positivePrefix_eq (b : ℕ) (k : Fin 8) :
    ThreeBoundHighTypes.positivePrefix 2 b k=ThreeBoundQ2.positivePrefix b k := by
  fin_cases k <;> simp [ThreeBoundHighTypes.positivePrefix,
    ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel]

theorem kind_target_prefix_iff
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (w : V) (kind : Fin 8)
    (hk : ThreeBoundHighTypes.OfKind 2
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) kind) (q : ℕ) :
    w ∈ targetPrefix S F P.strongLower P.strongUpper j x q ↔
      ThreeBoundQ2.positivePrefix q kind=true := by
  have hhigh : w ∈ highHeads S F P.strongLower P.strongUpper j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ThreeBoundHighTypes.ofKind_high 2 _ _ kind hk⟩
  have he := ThreeBoundHighTypes.positivePrefix_iff 2 (failed S F j x w).card q _ _ kind
    (fun b hb => ⟨hb.1.1.trans hQ,hb.1.2.1⟩)
    (fun b hb => ⟨hb.1.trans hQ,hb.2.1⟩) hk
  rw [positivePrefix_eq] at he
  rw [← he]
  simp only [targetPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨b,hb,ht⟩
    exact ⟨b,hb,ht,high_guards_true S F hF i j P x w hhigh⟩
  · rintro ⟨b,hb,hp⟩
    exact ⟨b,hb,hp.1⟩

theorem prefix_high_eq
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) (q : ℕ) :
    targetPrefix S F P.strongLower P.strongUpper j x q ∩
        highHeads S F P.strongLower P.strongUpper j x =
      (highHeads S F P.strongLower P.strongUpper j x).filter
        fun w => ThreeBoundQ2.positivePrefix q (tag w)=true := by
  ext w
  simp only [Finset.mem_inter,Finset.mem_filter]
  constructor
  · rintro ⟨ht,hh⟩
    exact ⟨hh,(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).1 ht⟩
  · rintro ⟨hh,ht⟩
    exact ⟨(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).2 ht,hh⟩

theorem outside_high_eq
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) (q b : ℕ) :
    ((highHeads S F P.strongLower P.strongUpper j x \
      targetPrefix S F P.strongLower P.strongUpper j x q).filter
      fun w => (failed S F j x w).card ≤ b) =
      (highHeads S F P.strongLower P.strongUpper j x).filter fun w =>
        ThreeBoundQ2.positivePrefix q (tag w)=false ∧ ThreeBoundQ2.budget (tag w) ≤ b := by
  ext w
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  by_cases hh : w ∈ highHeads S F P.strongLower P.strongUpper j x
  · have ht := kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q
    have hc := ThreeBoundHighTypes.ofKind_count 2 (failed S F j x w).card _ _ (tag w)
      (fun b hb => hb.1.2.1) (fun b hb => hb.2.1) (hk w hh)
    rw [budget_eq] at hc
    simp only [hh,true_and,hc,ht]
    cases ThreeBoundQ2.positivePrefix q (tag w) <;> simp
  · simp [hh]

theorem guardSources_eq_filter
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) :
    guardSources S F P.strongLower P.strongUpper j x =
      (highHeads S F P.strongLower P.strongUpper j x).filter
        fun w => ThreeBoundQ2.isGuard (tag w)=true := by
  ext w
  constructor
  · intro hw
    have hg := (Finset.mem_filter.mp hw).2
    have hh : w ∈ highHeads S F P.strongLower P.strongUpper j x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hg⟩
    refine Finset.mem_filter.mpr ⟨hh,?_⟩
    rw [← isGuard_eq]
    exact (ThreeBoundHighTypes.guard_iff 2 (failed S F j x w).card _ _ (tag w)
      (fun b hb => ⟨hb.1.1.trans hQ,hb.1.2.1⟩)
      (fun b hb => ⟨hb.1.trans hQ,hb.2.1⟩) (hk w hh)).1 hg
  · intro hw
    obtain ⟨hh,hg⟩ := Finset.mem_filter.mp hw
    rw [← isGuard_eq] at hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (ThreeBoundHighTypes.guard_iff 2 (failed S F j x w).card _ _ (tag w)
        (fun b hb => ⟨hb.1.1.trans hQ,hb.1.2.1⟩)
        (fun b hb => ⟨hb.1.trans hQ,hb.2.1⟩) (hk w hh)).2 hg⟩

end
end ThreeBoundMinmaxQ2

#print axioms ThreeBoundMinmaxQ2.kind_target_prefix_iff
#print axioms ThreeBoundMinmaxQ2.guardSources_eq_filter


