-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroPointOver
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroPointOver
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:05.680922+00:00
-- url     : https://prove2.me/theorems/5063b000-d860-5ea2-aed2-69a6f584b794
-- title:
--   Level Zero Point Over
-- statement:
--   Definitions and structural lemmas for Level Zero Point Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelZeroPointOver.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Imports
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
def levelZeroPointOver {k r : ℕ} (a : C.LPt) (hle : D.ptSize a ≤ r) (g : B.Mat k (r - D.ptSize a)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g)
def LeftFubini : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (T : D.LevTower k r Wp Wq),
    D.TowerNormalised T → ∀ (j : ℕ) (hj : j ≤ r), 1 ≤ j → ∀ (a : C.LPt) (ha : D.IsLocPt a j),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k r),
      (∀ x, sx x ∈ Sset k r T.base.z) ∧
      ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z', ∀ H : B.Mat k r → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k r ∧ Dmin k r T.base.z T.base.z' x ⟨j, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj)
          (D.castM (by rw [ha.2]) g)))) μ ∧
        B.JF (T.bs j) (D.castF (by rw [ha.2]) (D.sliceAt k r T.base.z T.base.z' H a)) g =
          ∫ x, ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj) (D.castM (by rw [ha.2]) g))) ∂μ
end Formalism.FourierDecayAlt.P.LeftFubiniLemmas


