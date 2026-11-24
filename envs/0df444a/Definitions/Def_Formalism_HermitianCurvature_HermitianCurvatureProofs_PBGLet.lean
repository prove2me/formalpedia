-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:22.184808+00:00
-- url     : https://prove2.me/theorems/cd23518d-9196-4bde-a38b-13d00c81f4fc
-- title:
--   PBGLet
-- statement:
--   Definitions and structural lemmas for PBGLet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_RdV
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_fun_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_add
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val


set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section poly
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
def PolyRepN (d : ℕ) (f : ℂ → E) (top : E) : Prop :=
  ∃ c : ℕ → E, c d = top ∧ ∀ u, f u = ∑ l ∈ range (d + 1), u ^ l • c l
end poly
section ops
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem loc_zero' (g : Mat k r) : Loc (⊤ : ℕ∞) (fun _ : Mat k r => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
theorem loc_of_eq {m : ℕ∞} {f f₂ : Mat k r → E} {g : Mat k r} (h : Loc m f g) {V : Set (Mat k r)}
    (hV : IsOpen V) (hg : g ∈ V) (he : ∀ x ∈ V, x ∈ GV k r → f₂ x = f x) : Loc m f₂ g := by
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := h
  exact ⟨U ∩ V, f', hU.inter hV, ⟨hgU, hg⟩, hf'.mono Set.inter_subset_left,
    fun x hx hxG => by rw [he x hx.2 hxG, hfe x hx.1 hxG]⟩
theorem hermitian_part_one_mem_lie (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart1_lie Z
theorem hermitian_part_two_mem_lie (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart2_lie Z
theorem eabH_loc (a b : Fin (2 * r + k + 1)) {f : Mat k r → E} {g : Mat k r} (h : Loc (⊤ : ℕ∞) f g) :
    Loc (⊤ : ℕ∞) (EabH (Hpk k r) a b f) g := by
  have h' : Loc ((⊤ : ℕ∞) + 1) f g := by rwa [top_add]
  exact loc_add (loc_RdV (hermitian_part_one_mem_lie _) h') (loc_RdV (hermitian_part_two_mem_lie _) h') Complex.I
theorem eabH_add (a b : Fin (2 * r + k + 1)) {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 f₁ g)
    (h₂ : Loc 1 f₂ g) (hg : g ∈ GV k r) (c : ℂ) :
    EabH (Hpk k r) a b (fun x => f₁ x + c • f₂ x) g = EabH (Hpk k r) a b f₁ g + c • EabH (Hpk k r) a b f₂ g := by
  unfold EabH
  rw [Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add h₁ h₂ hg (hermitian_part_one_mem_lie _) c, Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add h₁ h₂ hg (hermitian_part_two_mem_lie _) c]
  module
theorem eabH_zero (a b : Fin (2 * r + k + 1)) (g : Mat k r) :
    EabH (Hpk k r) a b (fun _ : Mat k r => (0 : E)) g = 0 := by
  simp [EabH, RdV]
def Wsm (U₀ : Set (Mat k r)) : Submodule ℂ (Mat k r → E) where
  carrier := {f | ∀ g ∈ U₀, g ∈ GV k r → Loc (⊤ : ℕ∞) f g}
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g hg hgG
    have := loc_add (h₁ g hg hgG) (h₂ g hg hgG) 1
    convert this using 1
    funext x; simp
  zero_mem' := fun g _ _ => loc_zero' g
  smul_mem' := by
    intro c f hf g hg hgG
    have := loc_add (loc_zero' (E := E) g) (hf g hg hgG) c
    convert this using 1
    funext x; simp
theorem loc1 {f : Mat k r → E} {g : Mat k r} (h : Loc (⊤ : ℕ∞) f g) : Loc 1 f g := loc_mono le_top h
def EHt (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀) (a b : Fin (2 * r + k + 1)) :
    Wsm (E := E) U₀ →ₗ[ℂ] Wsm (E := E) U₀ where
  toFun f := ⟨fun g => if g ∈ U₀ ∧ g ∈ GV k r then EabH (Hpk k r) a b f.1 g else 0, by
    intro g hg hgG
    exact loc_of_eq (eabH_loc a b (f.2 g hg hgG)) hU₀ hg (fun x hx hxG => by simp [hx, hxG])⟩
  map_add' f₁ f₂ := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [Submodule.coe_add, Pi.add_apply]
    split_ifs with hS
    · have e : ((f₁ : Mat k r → E) + f₂) = fun x => f₁.1 x + (1 : ℂ) • f₂.1 x := by funext x; simp
      rw [e, eabH_add a b (loc1 (f₁.2 g hS.1 hS.2)) (loc1 (f₂.2 g hS.1 hS.2)) hS.2, one_smul]
    · simp
  map_smul' c f := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs with hS
    · have e : (c • (f : Mat k r → E)) = fun x => (fun _ : Mat k r => (0 : E)) x + c • f.1 x := by
        funext x; simp
      rw [e, eabH_add a b (loc1 (loc_zero' g)) (loc1 (f.2 g hS.1 hS.2)) hS.2, eabH_zero, zero_add]
    · simp
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
end ops
section letters
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def xi0 (g₀ : Mat k r) : Fin r → Fin (2 * r + k + 1) → ℂ :=
  fun a p => herm (Hpk k r) (g₀ *ᵥ bvec p) (bvec (eI k r a))
def y0 (g₀ : Mat k r) : Fin r → Fin (2 * r + k + 1) → ℂ :=
  fun a p => (g₀⁻¹ *ᵥ bvec (eI k r a)) p
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
end letters
section final
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end final
section smooth
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r)
def Sd : Set (Mat k r) := {g | Dmin k r z z' g ⟨j, by omega⟩ ≠ 0}
end smooth
end Formalism.FourierDecayAlt.P.PBG


