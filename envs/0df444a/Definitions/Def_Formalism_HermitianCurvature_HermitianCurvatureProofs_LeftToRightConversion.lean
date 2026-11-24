-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:08:56.762067+00:00
-- url     : https://prove2.me/theorems/56c431ed-3e03-4bab-a303-341a3375ac0e
-- title:
--   Left To Right Conversion
-- statement:
--   Definitions and structural lemmas for Left To Right Conversion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_co_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_co_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def cT (i : J k r) (X : Mat k r) (g : Mat k r) : ℂ := ((kc i (-(Hpk k r * gᴴ * Hpk k r * X * g)) : ℝ) : ℂ)
lemma kc_add (i : J k r) (Z Z' : Mat k r) : kc i (Z + Z') = kc i Z + kc i Z' := by
  unfold kc; rw [co_add]; ring
lemma kc_smul (i : J k r) (c : ℝ) (Z : Mat k r) : kc i (c • Z) = c * kc i Z := by
  unfold kc; rw [co_smul]; ring
def coL (j : J k r) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := ((co g j : ℝ) : ℂ)
  map_add' x y := by rw [co_add]; push_cast; rfl
  map_smul' c x := by rw [co_smul]; simp [Complex.real_smul]
def qL (i : J k r) (X : Mat k r) (j : J k r) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := ((kc i (-(Hpk k r * gᴴ * Hpk k r * X * Eb j)) : ℝ) : ℂ)
  map_add' x y := by
    rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, neg_add, kc_add]
    exact Complex.ofReal_add _ _
  map_smul' c x := by
    have e : Hpk k r * (c • x)ᴴ * Hpk k r * X * Eb j = c • (Hpk k r * xᴴ * Hpk k r * X * Eb j) := by
      rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    rw [e, ← smul_neg, kc_smul]
    simp [Complex.real_smul]
end Formalism.FourierDecayAlt.P.LeftToRightConversion
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


