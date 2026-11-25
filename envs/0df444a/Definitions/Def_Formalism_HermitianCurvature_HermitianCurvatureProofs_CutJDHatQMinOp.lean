-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:10:46.720613+00:00
-- url     : https://prove2.me/theorems/0027980b-4464-4764-9d83-9bc322d6de20
-- title:
--   Cut JDHat QMin Op
-- statement:
--   Definitions and structural lemmas for Cut JDHat QMin Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatQMinOp.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_coef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section terms
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp
open Classical in

def pTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [B.hsInner, _root_.smul_apply, ContinuousLinearMap.id_apply, hsv_smul,
      inner_smul_left, inner_smul_right]
    simp
end terms
section basic₂
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end basic₂
def QMinorCov : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (Pm Qm : Matrix (Fin n) (Fin n) ℂ),
    Qm * Pm = 1 → ∀ (a b : Fin t → Fin n) (u : ℂ),
      qminor (Formalism.FourierDecayAlt.Q.Econj E Pm Qm) a b u =
        ∑ a' : Fin t → Fin n, ∑ b' : Fin t → Fin n,
          ((∏ k, Pm (a' k) (a k)) * ∏ k, Qm (b k) (b' k)) • qminor E a' b' u
end
end Formalism.FourierDecayAlt.P.CutMP.QMinOp


