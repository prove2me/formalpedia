-- Prove2me | Definitions.Def_BS2_b3ba934b_AllKindHeadCosts
-- name    : BS2_b3ba934b_AllKindHeadCosts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:27:07.865488+00:00
-- url     : https://prove2.me/theorems/9a8a752e-b522-4481-96d6-1c8dfa270aa0
-- title:
--   Sensitivity separation: AllKindHeadCosts (complete source module)
-- statement:
--   Complete Lean source module `AllKindHeadCosts` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/AllKindHeadCosts.lean; original SHA-256 f9362d57c5ee851cdc0405597f749fdaa38de5cb115f32de411a222a2876dcd2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The eight actual q2 types all satisfy the exact symbolic head cost. -/
import Definitions.Def_BS2_b3ba934b_HeadCostExpressions

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundAllKindHeadCosts
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem target_of_positive
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ)
    (hp : Q2CandidateTypes.PositiveCandidate (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card b
      (child x w false) (child x w true)) : targetAt S F t j x w := by
  have he := hp.1.2.1
  simpa only [targetAt,he] using hp.1

theorem positive_of_target_high
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool) (w : V)
    (hH : w ∈ highHeads S F P.strong j x) (ht : targetAt S F P.strong j x w) :
    Q2CandidateTypes.PositiveCandidate (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (failed S F j x w).card (child x w false) (child x w true) :=
  ⟨ht,high_guards_true S F hF i j P x w hH false,high_guards_true S F hF i j P x w hH true⟩

theorem pure_guard_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (w : V) (b : ℕ) (hb : b ≤ 2)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true))
    (hnt : ¬ targetAt S F P.strong j x w) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      (headCost n a c (b+3) (min 2 (incomingSources S F P.strong j x w).card)).eval v := by
  by_cases htop : b = S.tolerance j
  · exact pure_top_guard_expr_bound S F hF i j P a c matchE v hv x w b hb htop hg hnt
  · exact pure_lower_guard_expr_bound S F hF i j P a c matchE v hv x hoff w b hb
      (by have hh := hg.1; omega) hg hnt

theorem actual_kind_headCost_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (hQ : S.tolerance j ≤ 2) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      (headCost n a c kind.val (min 2 (incomingSources S F P.strong j x w).card)).eval v := by
  have hhigh := Q2CandidateTypes.ofKind_high (fun z => F (S.guard j) z = true)
    (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
    (child x w false) (child x w true) kind hk
  have hH : w ∈ highHeads S F P.strong j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩
  have htP := fun b hp => target_of_positive S F P.strong j x w b hp
  have hpT := fun ht => positive_of_target_high S F hF i j P x w hH ht
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk
  · have hcount := hk.1.2.1
    have hnot : ¬ guardAt S F P.strong j x w := by
      rintro ⟨b,hb⟩
      have hbc := hb.2.1
      omega
    have hbound := positive_only_expr_bound S F hF i j P a c matchE v hv x hoff w hH
      (htP 0 hk) hnot (by omega)
    simpa only [hcount] using hbound
  · have hcount := hk.1.1.2.1
    have hnot : ¬ guardAt S F P.strong j x w := by
      rintro ⟨b,hb⟩
      have hbc := hb.2.1
      have he : b = 0 := by omega
      exact hk.2 (he ▸ hb)
    have hbound := positive_only_expr_bound S F hF i j P a c matchE v hv x hoff w hH
      (htP 1 hk.1) hnot (by omega)
    simpa only [hcount] using hbound
  · have hcount := hk.1.1.2.1
    have hnot : ¬ guardAt S F P.strong j x w := by
      rintro ⟨b,hb⟩
      have hbc := hb.2.1
      have he : b = 1 := by omega
      exact hk.2 (he ▸ hb)
    have hbound := positive_only_expr_bound S F hF i j P a c matchE v hv x hoff w hH
      (htP 2 hk.1) hnot (by omega)
    simpa only [hcount] using hbound
  · have hcount := hk.1.2.1
    have hnot : ¬ targetAt S F P.strong j x w := by
      intro ht
      have hp := hpT ht
      apply hk.2
      simpa only [hcount] using hp
    exact pure_guard_expr_bound S F hF i j P a c matchE v hv x hoff w 0 (by omega) hk.1 hnot
  · have hcount := hk.1.2.1
    have hnot : ¬ targetAt S F P.strong j x w := by
      intro ht
      have hp := hpT ht
      apply hk.2
      simpa only [hcount] using hp
    exact pure_guard_expr_bound S F hF i j P a c matchE v hv x hoff w 1 (by omega) hk.1 hnot
  · have hcount := hk.2.1
    have hnot : ¬ targetAt S F P.strong j x w := by
      intro ht
      have htQ := ht.1
      omega
    exact pure_guard_expr_bound S F hF i j P a c matchE v hv x hoff w 2 (by omega) hk hnot
  · have hcount := hk.1.1.2.1
    have hbound := overlap_expr_bound S F hF i j P a c matchE v hv x hoff w
      (htP 1 hk.1) ⟨0,hk.2⟩ (by omega)
    simpa only [hcount] using hbound
  · have hcount := hk.1.1.2.1
    have hbound := overlap_expr_bound S F hF i j P a c matchE v hv x hoff w
      (htP 2 hk.1) ⟨1,hk.2⟩ (by omega)
    simpa only [hcount] using hbound

end
end ThreeBoundAllKindHeadCosts

#print axioms ThreeBoundAllKindHeadCosts.actual_kind_headCost_bound


