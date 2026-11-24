-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:40.960875+00:00
-- url     : https://prove2.me/theorems/ec1d9ee8-3d9e-4825-a62e-440508a9cb25
-- title:
--   Conjugated Generator Gl Relation
-- statement:
--   Definitions and structural lemmas for Conjugated Generator Gl Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_ana_hpart1_add
import Theorems.Thm_AAInvW_ana_hpart1_smul
import Theorems.Thm_AAInvW_ana_hpart2_add
import Theorems.Thm_AAInvW_ana_hpart2_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def EcH {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (H Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (hpart1 H Z) f g + Complex.I • RdV (hpart2 H Z) f g
section Ec
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Ec
section Right
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma ana_Phi_add (hH : HInvol H) (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) (g Z W : Matrix (Fin n) (Fin n) ℂ) :
    L (g * hpart1 H (Z + W)) + Complex.I • L (g * hpart2 H (Z + W)) =
      (L (g * hpart1 H Z) + Complex.I • L (g * hpart2 H Z)) +
        (L (g * hpart1 H W) + Complex.I • L (g * hpart2 H W)) := by
  rw [ana_hpart1_add hH, ana_hpart2_add hH, Matrix.mul_add, Matrix.mul_add, map_add, map_add, smul_add]
  abel
lemma ana_Phi_smul (hH : HInvol H) (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) (g Z : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) :
    L (g * hpart1 H (c • Z)) + Complex.I • L (g * hpart2 H (c • Z)) =
      c • (L (g * hpart1 H Z) + Complex.I • L (g * hpart2 H Z)) := by
  have hr : ∀ (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ), L ((r : ℂ) • M) = (r : ℂ) • L M := by
    intro r M
    rw [show ((r : ℂ) • M) = r • M from Matrix.ext fun i j => by simp [Complex.real_smul], L.map_smul]
    exact (Complex.coe_smul r (L M)).symm
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, c = x + y * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  rw [ana_hpart1_smul hH, ana_hpart2_smul hH, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_smul, map_sub, map_add, hr, hr, hr, hr]
  match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
def anaPhi (hH : HInvol H) (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E where
  toFun Z := L (g * hpart1 H Z) + Complex.I • L (g * hpart2 H Z)
  map_add' Z W := ana_Phi_add hH L g Z W
  map_smul' c Z := ana_Phi_smul hH L g Z c
end Right
end AAInvW


