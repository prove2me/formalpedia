-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:50:34.327301+00:00
-- url     : https://prove2.me/theorems/6aff7022-607a-4a75-99c5-97e83ff0a00e
-- title:
--   Cv Rho Of Parts
-- statement:
--   Definitions and structural lemmas for Cv Rho Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def Xa (k r : ℕ) (c d : Fin (2 * r + k + 1)) : Mat k r := hpart1 (Hpk k r) (Matrix.single c d 1)
def Xb (k r : ℕ) (c d : Fin (2 * r + k + 1)) : Mat k r := hpart2 (Hpk k r) (Matrix.single c d 1)
def EHc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (y : Mat k r) (c d : Fin (2 * r + k + 1))
    (f : Mat k r → E) : Mat k r → E :=
  fun g => RdV (y⁻¹ * Xa k r c d * y) f g + Complex.I • RdV (y⁻¹ * Xb k r c d * y) f g
def CapAdInv : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (y : Mat k r) (u : ℂ) (f : Mat k r → E),
    y ∈ GV k r → CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) f → ∀ h ∈ GV k r,
      qminorOp (EHc k r y) (Q.posL k r 0) (Q.posL k r 0) u f h =
        qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) u f h
section Transport
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
end Transport
section Letters
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
end Letters
def Lq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (p : SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))
end Formalism.FourierDecayAlt.P.JFxB


