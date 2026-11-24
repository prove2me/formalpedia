-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:23.534637+00:00
-- url     : https://prove2.me/theorems/8553166e-b1a3-47b8-89c6-75a9456eb7d9
-- title:
--   The Section
-- statement:
--   Definitions and structural lemmas for The Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_Hb_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_transitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)
theorem herm_last_scaled (t : ℝ) (ht : 0 < t) :
    herm (Hb k) (((Real.sqrt t : ℝ) : ℂ) • Pi.single (Fin.last k) 1)
      (((Real.sqrt t : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = -(t : ℂ) := by
  have hcs : star ((Real.sqrt t : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  unfold herm Hb
  rw [dotProduct, Finset.sum_eq_single (Fin.last k)]
  · simp only [Matrix.mulVec_diagonal, Matrix.mulVec_smul, Pi.star_apply, Pi.smul_apply,
      Pi.single_eq_same, if_pos rfl, smul_eq_mul, mul_one, star_mul', star_one]
    rw [hcs]
    simp only [↓reduceIte]
    linear_combination (-1 : ℂ) * hs
  · intro i _ hi
    simp [Matrix.mulVec_diagonal, Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h
def gA (a : Fin (k + 1) → ℂ) (T : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if h : 0 < T ∧ herm (Hb k) a a = -(T : ℂ) then
    Classical.choose (transitive (Hb k) (Hb_herm k) _ a T h.1 (herm_last_scaled k T h.1) h.2)
  else 1
def gB (b : Fin (k + 1) → ℂ) (T' : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if h : 0 < T' ∧ herm (Hb k) b b = -(T' : ℂ) then
    Classical.choose (transitive (Hb k) (Hb_herm k) b _ T' h.1 h.2 (herm_last_scaled k T' h.1))
  else 1
def wZ (T T' : ℝ) (ζ : ℂ) : ℂ := (-((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)⁻¹) * ζ
def sZ (T T' : ℝ) (ζ : ℂ) : ℂ := ((Real.sqrt (Complex.normSq ζ / (T * T') - 1) : ℝ) : ℂ)
def theSecB (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (ζ : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  gA k a T * nu k (wZ T T' ζ) (sZ T T' ζ) * gB k b T'
def theSection (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z')
end Formalism.FourierDecayAlt.P.TheSec


