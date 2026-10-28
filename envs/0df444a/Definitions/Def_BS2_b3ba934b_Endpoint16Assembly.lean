-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Assembly
-- name    : BS2_b3ba934b_Endpoint16Assembly
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:30:35.214962+00:00
-- url     : https://prove2.me/theorems/b2e19189-3093-4172-a516-2713def54c3b
-- title:
--   Sensitivity separation: Endpoint16Assembly (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Assembly` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Assembly.lean; original SHA-256 38f28f1e6014e1427d6454871939c7dc2c199125a282c482773f176b1d313959; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Four-stage induction for the actual second endpoint. Semantic and
numerical transfer hypotheses remain explicit until their proofs are linked. -/
import Definitions.Def_BS2_b3ba934b_Endpoint16Invariant
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness

def input (p : Fin 4) : Profile 16 :=
  match p.val with | 0=>profile0 | 1=>profile1 | 2=>profile2 | _=>profile3
def rawInput (p : Fin 4) : Profile 16 :=
  match p.val with | 0=>rawProfile0 | 1=>rawProfile1 | 2=>rawProfile2 | _=>rawProfile3
def output (p : Fin 4) : Profile 16 :=
  match p.val with | 0=>profile1 | 1=>profile2 | 2=>profile3 | _=>profile4

def RawPreserves (p : Fin 4) : Prop :=
  ∀ (I : Type) [Fintype I] (F : Fin 16 → (I → Bool) → Bool), Nested F →
    ∀ v : Profile 16, Ordered v → Upper F v →
    Upper (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F) (raw p v)

def RawNumericalBounds : Prop :=
  ∀ p : Fin 4, ∀ coord : Coord 16, valid coord → raw p (input p) coord≤rawInput p coord

theorem input_ordered (p : Fin 4) : Ordered (input p) := by
  fin_cases p
  · exact ordered0
  · exact ordered1
  · exact ordered2
  · exact ordered3

theorem stage_from_raw {I : Type} [Fintype I]
    (p : Fin 4) (sound : RawPreserves p) (numerical : RawNumericalBounds)
    (F : Fin 16 → (I → Bool) → Bool) (hF : Nested F) (c : ℕ)
    (hv : Upper F (scale c (input p))) :
    Upper (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F) (scale c (output p)) := by
  have hr:=sound I F hF (scale c (input p))
    (ordered_scale (input p) c (input_ordered p)) hv
  have hhom : raw p (scale c (input p))=scale c (raw p (input p)) :=
    raw_homogeneous p (input p) c
  rw [hhom] at hr
  have hb : Upper (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F)
      (scale c (rawInput p)) := by
    intro coord
    by_cases hc : valid coord
    · exact sem_mono _ coord _ _ (Nat.mul_le_mul_left c (numerical p coord hc)) (hr coord)
    · exact sem_of_not_valid _ coord _ hc
  fin_cases p <;> exact hb

theorem family_succ_phase (d : ℕ) (p : Fin 4) (hp : d%4=p.val) :
    Sensitivity10007Endpoint16.family (d+1)=
      parent ((Sensitivity10007Endpoint16.recipe p).stage
        (Sensitivity10007Endpoint16.family d)) (Sensitivity10007Endpoint16.family d) := by
  have he : (⟨d%4,Nat.mod_lt d (by decide)⟩ : Fin 4)=p := Fin.ext hp
  simp only [Sensitivity10007Endpoint16.family,towerFamily,
    Sensitivity10007Endpoint16.periodicRecipe,he]
  rfl

theorem periodic_upper (sound : ∀ p : Fin 4, RawPreserves p)
    (numerical : RawNumericalBounds) : ∀ m : ℕ,
    Upper (Sensitivity10007Endpoint16.family (4*m)) (scale (31192129^m) profile0) := by
  intro m
  induction m with
  | zero =>
      change Upper (Sensitivity10007Endpoint16.family 0) (fun coord=>1*profile0 coord)
      simpa only [one_mul] using actual_base_upper
  | succ m ih =>
      let c:=31192129^m
      have h₁ : Upper (Sensitivity10007Endpoint16.family (4*m+1)) (scale c profile1) := by
        rw [family_succ_phase (4*m) 0 (by omega)]
        exact stage_from_raw 0 (sound 0) numerical _
          (Sensitivity10007Endpoint16.family_nested (4*m)) c ih
      have h₂ : Upper (Sensitivity10007Endpoint16.family (4*m+2)) (scale c profile2) := by
        rw [show 4*m+2=(4*m+1)+1 by omega,family_succ_phase (4*m+1) 1 (by omega)]
        exact stage_from_raw 1 (sound 1) numerical _
          (Sensitivity10007Endpoint16.family_nested (4*m+1)) c h₁
      have h₃ : Upper (Sensitivity10007Endpoint16.family (4*m+3)) (scale c profile3) := by
        rw [show 4*m+3=(4*m+2)+1 by omega,family_succ_phase (4*m+2) 2 (by omega)]
        exact stage_from_raw 2 (sound 2) numerical _
          (Sensitivity10007Endpoint16.family_nested (4*m+2)) c h₂
      have h₄ : Upper (Sensitivity10007Endpoint16.family (4*m+4)) (scale c profile4) := by
        rw [show 4*m+4=(4*m+3)+1 by omega,family_succ_phase (4*m+3) 3 (by omega)]
        exact stage_from_raw 3 (sound 3) numerical _
          (Sensitivity10007Endpoint16.family_nested (4*m+3)) c h₃
      have hf : Upper (Sensitivity10007Endpoint16.family (4*m+4))
          (scale (31192129^(m+1)) profile0) := by
        apply upper_mono _ _ _ _ h₄
        intro coord
        have hh:=Nat.mul_le_mul_left c (period_inequality coord)
        simpa only [c,scale,pow_succ,Nat.mul_assoc] using hh
      simpa only [Nat.mul_succ] using hf

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.periodic_upper


