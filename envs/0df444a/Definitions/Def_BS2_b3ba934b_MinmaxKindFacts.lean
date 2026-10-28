-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxKindFacts
-- name    : BS2_b3ba934b_MinmaxKindFacts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:44:59.463514+00:00
-- url     : https://prove2.me/theorems/e9fb7c8e-1680-4805-ac1b-1af5c88f5883
-- title:
--   Sensitivity separation: MinmaxKindFacts (complete source module)
-- statement:
--   Complete Lean source module `MinmaxKindFacts` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxKindFacts.lean; original SHA-256 e11c996aab4213784388265db9e8842babf9bfd6106f1f7a10bdc581bab77cd1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Elementary projections of the exact eight min/max head types. -/
import Definitions.Def_BS2_b3ba934b_MinmaxQ2Types

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxQ2
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def guardLevel (k : ℕ) : ℕ := if k ≤ 5 then k-3 else k-6

theorem kind_positive (q : ℕ) (P G : ℕ → Prop) (k : ThreeBoundHighTypes.Kind q)
    (hk : ThreeBoundHighTypes.OfKind q P G k) (hp : k.val ≤ q) : P k.val := by
  simp only [ThreeBoundHighTypes.OfKind,if_pos hp] at hk
  exact hk.1

theorem kind_guard (P G : ℕ → Prop) (k : Fin 8)
    (hk : ThreeBoundHighTypes.OfKind 2 P G k) (hg : 3 ≤ k.val) : G (guardLevel k.val) := by
  fin_cases k <;> norm_num [ThreeBoundHighTypes.OfKind,guardLevel] at * <;> tauto

theorem kind_overlap (P G : ℕ → Prop) (k : Fin 8)
    (hk : ThreeBoundHighTypes.OfKind 2 P G k) (hg : 6 ≤ k.val) : P (k.val-5) := by
  fin_cases k <;> norm_num [ThreeBoundHighTypes.OfKind] at * <;> tauto

theorem kind_no_positive (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) (hQ : S.tolerance j ≤ 2)
    (k : Fin 8) (hk : ThreeBoundHighTypes.OfKind 2
      (PositiveCandidate S F t u j x w) (GuardCandidate S F t u j x w) k)
    (hl : 3 ≤ k.val) (hu : k.val ≤ 5) : ¬ ∃ b, PositiveCandidate S F t u j x w b := by
  have hg := kind_guard _ _ k hk hl
  rintro ⟨b,hb⟩
  have hcb := hb.1.2.1
  have hcg := hg.2.1
  have hbd : b=guardLevel k.val+1 := by omega
  have hbq := hb.1.1
  fin_cases k <;> norm_num [ThreeBoundHighTypes.OfKind,guardLevel] at *
  · exact hk.2 (hbd ▸ hb)
  · exact hk.2 (hbd ▸ hb)
  · omega

theorem kind_tolerance_one (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V)
    (hQ : S.tolerance j ≤ 1) (k : Fin 8)
    (hk : ThreeBoundHighTypes.OfKind 2
      (PositiveCandidate S F t u j x w) (GuardCandidate S F t u j x w) k) :
    k.val≠2 ∧ k.val≠5 ∧ k.val≠7 := by
  fin_cases k <;> norm_num [ThreeBoundHighTypes.OfKind] at *
  · have hh := hk.1.1.1
    change 2 ≤ S.tolerance j at hh
    omega
  · have hh := hk.1
    omega
  · have hh := hk.1.1.1
    change 2 ≤ S.tolerance j at hh
    omega

end
end ThreeBoundMinmaxQ2

#print axioms ThreeBoundMinmaxQ2.kind_no_positive


