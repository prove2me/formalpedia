-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40Assembly
-- name    : BS2_b3ba934b_Endpoint40Assembly
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:47:27.817546+00:00
-- url     : https://prove2.me/theorems/8985c118-a26f-43bf-a6bc-e361d1fefc30
-- title:
--   Sensitivity separation: Endpoint40Assembly (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40Assembly` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40Assembly.lean; original SHA-256 5e11e2852e2590adde247b7b73abd22e2f8b9662db43209d4c31e26a5a403d14; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Four-stage induction for the actual first endpoint.
RawPreserves and RawNumericalBounds are explicit remaining interfaces; this
module does not assert them as axioms or hide them behind an endpoint claim. -/
import Definitions.Def_BS2_b3ba934b_Endpoint40Invariant
import Definitions.Def_BS2_b3ba934b_Endpoint40ClosureProof0
import Definitions.Def_BS2_b3ba934b_Endpoint40ClosureProof1
import Definitions.Def_BS2_b3ba934b_Endpoint40ClosureProof2
import Definitions.Def_BS2_b3ba934b_Endpoint40ClosureProof3

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness

def input (p : Fin 4) : Profile 40 :=
  match p.val with | 0=>profile0 | 1=>profile1 | 2=>profile2 | _=>profile3
def rawInput (p : Fin 4) : Profile 40 :=
  match p.val with | 0=>rawProfile0 | 1=>rawProfile1 | 2=>rawProfile2 | _=>rawProfile3
def output (p : Fin 4) : Profile 40 :=
  match p.val with | 0=>profile1 | 1=>profile2 | 2=>profile3 | _=>profile4

def RawPreserves (p : Fin 4) : Prop :=
  ∀ (I : Type) [Fintype I] (F : Fin 40 → (I → Bool) → Bool), Nested F →
    ∀ v : Profile 40, Admissible (recipe p) v → Upper F v →
    Upper (parent ((Sensitivity10007Endpoint40.recipe p).stage F) F) (raw p v)

def RawNumericalBounds : Prop :=
  ∀ p : Fin 4, ∀ coord : Coord 40, valid coord → raw p (input p) coord≤rawInput p coord

theorem input_admissible (p : Fin 4) : Admissible (recipe p) (input p) := by
  fin_cases p
  · exact admissible0
  · exact admissible1
  · exact admissible2
  · exact admissible3

theorem stage_from_raw {I : Type} [Fintype I]
    (p : Fin 4) (sound : RawPreserves p) (numerical : RawNumericalBounds)
    (F : Fin 40 → (I → Bool) → Bool) (hF : Nested F) (c : ℕ)
    (hv : Upper F (scale c (input p))) :
    Upper (parent ((Sensitivity10007Endpoint40.recipe p).stage F) F) (scale c (output p)) := by
  let G:=parent ((Sensitivity10007Endpoint40.recipe p).stage F) F
  have hG : Nested G:=ThreeBoundNesting.parent_nested _
    (Sensitivity10007Endpoint40.recipe_ordered p) F hF
  have hr:=sound I F hF (scale c (input p))
    (admissible_scale (recipe p) (input p) c (input_admissible p)) hv
  have hhom : raw p (scale c (input p))=scale c (raw p (input p)) :=
    rawTransfer_homogeneous 40 5003 caps records (recipe p) (input p) c
  rw [hhom] at hr
  have hb : Upper G (scale c (rawInput p)) := by
    intro coord
    by_cases hc : valid coord
    · exact sem_mono G coord _ _ (Nat.mul_le_mul_left c (numerical p coord hc)) (hr coord)
    · exact sem_of_not_valid G coord _ hc
  fin_cases p
  · exact closure0_sound G hG c hb
  · exact closure1_sound G hG c hb
  · exact closure2_sound G hG c hb
  · exact closure3_sound G hG c hb

theorem family_succ_phase (d : ℕ) (p : Fin 4) (hp : d%4=p.val) :
    Sensitivity10007Endpoint40.family (d+1)=
      parent ((Sensitivity10007Endpoint40.recipe p).stage
        (Sensitivity10007Endpoint40.family d)) (Sensitivity10007Endpoint40.family d) := by
  have he : (⟨d%4,Nat.mod_lt d (by decide)⟩ : Fin 4)=p := Fin.ext hp
  simp only [Sensitivity10007Endpoint40.family,towerFamily,
    Sensitivity10007Endpoint40.periodicRecipe,he]
  rfl

theorem periodic_upper (sound : ∀ p : Fin 4, RawPreserves p)
    (numerical : RawNumericalBounds) : ∀ m : ℕ,
    Upper (Sensitivity10007Endpoint40.family (4*m)) (scale (31739938^m) profile0) := by
  intro m
  induction m with
  | zero =>
      change Upper (Sensitivity10007Endpoint40.family 0) (fun coord=>1*profile0 coord)
      simpa only [one_mul] using actual_base_upper
  | succ m ih =>
      let c:=31739938^m
      have h₁ : Upper (Sensitivity10007Endpoint40.family (4*m+1)) (scale c profile1) := by
        rw [family_succ_phase (4*m) 0 (by omega)]
        exact stage_from_raw 0 (sound 0) numerical _
          (Sensitivity10007Endpoint40.family_nested (4*m)) c ih
      have h₂ : Upper (Sensitivity10007Endpoint40.family (4*m+2)) (scale c profile2) := by
        rw [show 4*m+2=(4*m+1)+1 by omega,family_succ_phase (4*m+1) 1 (by omega)]
        exact stage_from_raw 1 (sound 1) numerical _
          (Sensitivity10007Endpoint40.family_nested (4*m+1)) c h₁
      have h₃ : Upper (Sensitivity10007Endpoint40.family (4*m+3)) (scale c profile3) := by
        rw [show 4*m+3=(4*m+2)+1 by omega,family_succ_phase (4*m+2) 2 (by omega)]
        exact stage_from_raw 2 (sound 2) numerical _
          (Sensitivity10007Endpoint40.family_nested (4*m+2)) c h₂
      have h₄ : Upper (Sensitivity10007Endpoint40.family (4*m+4)) (scale c profile4) := by
        rw [show 4*m+4=(4*m+3)+1 by omega,family_succ_phase (4*m+3) 3 (by omega)]
        exact stage_from_raw 3 (sound 3) numerical _
          (Sensitivity10007Endpoint40.family_nested (4*m+3)) c h₃
      have hf : Upper (Sensitivity10007Endpoint40.family (4*m+4))
          (scale (31739938^(m+1)) profile0) := by
        apply upper_mono _ _ _ _ h₄
        intro coord
        have hh:=Nat.mul_le_mul_left c (period_inequality coord)
        simpa only [c,scale,pow_succ,Nat.mul_assoc] using hh
      simpa only [Nat.mul_succ] using hf

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.periodic_upper


