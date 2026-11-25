-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjIntCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjIntCut
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:09:34.671807+00:00
-- url     : https://prove2.me/theorems/c9e5e124-46f7-4bb0-a293-aa870d8ad156
-- title:
--   Cut JAFFStable Adj Int Cut
-- statement:
--   Definitions and structural lemmas for Cut JAFFStable Adj Int Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAdjIntCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
def RhoUni : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (p : B.SS k r), D.inSS p → ∃ p' : B.SS k r, D.inSS p' ∧
      ∀ X Y : B.Mat k r → (Wq →L[ℂ] Wp),
        ∫ x : Mt k r, B.hsInner (B.rho D p X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (B.rho D p' Y (Matrix.of x)) ∂D.μG
def FormAdj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → B.SuppIn (B.GPos D) F →
      B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      ∫ x : Mt k r, B.hsInner (B.opApply Θ F (Matrix.of x)) (F' (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (F (Matrix.of x)) (B.opAdj Θ F' (Matrix.of x)) ∂D.μG
def AdjIntAsm : Prop := RhoUni → FormAdj → AdjInt
end
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS


