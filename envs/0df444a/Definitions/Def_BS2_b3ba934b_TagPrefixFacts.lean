-- Prove2me | Definitions.Def_BS2_b3ba934b_TagPrefixFacts
-- name    : BS2_b3ba934b_TagPrefixFacts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:31:59.234588+00:00
-- url     : https://prove2.me/theorems/887908f8-5e80-471d-b428-e8d0c4d30546
-- title:
--   Sensitivity separation: TagPrefixFacts (complete source module)
-- statement:
--   Complete Lean source module `TagPrefixFacts` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/TagPrefixFacts.lean; original SHA-256 37625d9efa0163c9bb1fb859d5eaf3ee7862e3f1aac96302868f475f4bb1c04d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_ActualTargetAccounting
import Definitions.Def_BS2_b3ba934b_ActualKindFilters

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundTagPrefixes
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundAllKindHeadCosts
open ThreeBoundActualTargets
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem kind_target_prefix_iff
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind) (q : ℕ) :
    w ∈ targetPrefix S F P.strong j x q ↔ ThreeBoundQ2.positivePrefix q kind = true := by
  have hhigh := Q2CandidateTypes.ofKind_high (fun z => F (S.guard j) z = true)
    (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
    (child x w false) (child x w true) kind hk
  have hH : w ∈ highHeads S F P.strong j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩
  have htP := fun b hp => target_of_positive S F P.strong j x w b hp
  have hpT := fun ht => positive_of_target_high S F hF i j P x w hH ht
  simp only [targetPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk
  · have ht := htP 0 hk
    have hc := hk.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have ht := htP 1 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have ht := htP 2 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have hc := hk.1.2.1
    have hn : ¬ targetAt S F P.strong j x w := by
      intro ht
      apply hk.2
      simpa only [hc] using hpT ht
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,hn]
  · have hc := hk.1.2.1
    have hn : ¬ targetAt S F P.strong j x w := by
      intro ht
      apply hk.2
      simpa only [hc] using hpT ht
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,hn]
  · have hc := hk.2.1
    have hn : ¬ targetAt S F P.strong j x w := by
      intro ht
      have hh := ht.1
      omega
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,hn]
  · have ht := htP 1 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have ht := htP 2 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]

theorem prefix_high_eq
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strong j x,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
        (child x w false) (child x w true) (tag w)) (q : ℕ) :
    targetPrefix S F P.strong j x q ∩ highHeads S F P.strong j x =
      (highHeads S F P.strong j x).filter fun w => ThreeBoundQ2.positivePrefix q (tag w) = true := by
  ext w
  simp only [Finset.mem_inter,Finset.mem_filter]
  constructor
  · rintro ⟨ht,hh⟩
    exact ⟨hh,(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).1 ht⟩
  · rintro ⟨hh,ht⟩
    exact ⟨(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).2 ht,hh⟩

theorem outside_high_eq
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strong j x,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
        (child x w false) (child x w true) (tag w)) (q b : ℕ) :
    ((highHeads S F P.strong j x \ targetPrefix S F P.strong j x q).filter
      fun w => (failed S F j x w).card ≤ b) =
      (highHeads S F P.strong j x).filter fun w =>
        ThreeBoundQ2.positivePrefix q (tag w) = false ∧ ThreeBoundQ2.budget (tag w) ≤ b := by
  ext w
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  by_cases hh : w ∈ highHeads S F P.strong j x
  · have ht := kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q
    have hc := Q2CandidateTypes.ofKind_count (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) (tag w) (hk w hh)
    rw [Q2CandidateTypes.budget_eq_enumerator] at hc
    simp only [hh,true_and,hc,ht]
    cases ThreeBoundQ2.positivePrefix q (tag w) <;> simp
  · simp [hh]

end
end ThreeBoundTagPrefixes

#print axioms ThreeBoundTagPrefixes.kind_target_prefix_iff
#print axioms ThreeBoundTagPrefixes.outside_high_eq


