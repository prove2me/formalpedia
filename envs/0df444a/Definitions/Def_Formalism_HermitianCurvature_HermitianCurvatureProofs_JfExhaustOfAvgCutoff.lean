-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:11:53.290955+00:00
-- url     : https://prove2.me/theorems/6a73b8fe-2069-53f9-84bc-951994521af1
-- title:
--   Jf Exhaust Of Avg Cutoff
-- statement:
--   Definitions and structural lemmas for Jf Exhaust Of Avg Cutoff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfExhaustOfAvgCutoff.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
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
namespace Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def AvgCutoff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    ∃ φ : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) φ ∧
      (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → φ g = 0) ∧
      ∀ p₀, D.inSS p₀ → ∀ q ∈ K, ∫ p, φ (B.sgs p (B.sgs p₀ (B.gq D q))) ∂D.μSS = 1
def AdjLeibniz : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq),
    B.SmoothCoef (Om k r D.z D.z') Θ →
    ∃ Θ' : B.DiffOp k r Wp Wq, B.opOrder Θ' = B.opOrder Θ ∧
      ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (Om k r D.z D.z') f →
        ∀ g ∈ Om k r D.z D.z', B.opApply Θ' f g = B.opAdj Θ f g
def AdjCommutes : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq),
    B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ →
    ∀ p, D.inSS p → ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (B.GV k r) f →
      ∀ g ∈ Om k r D.z D.z', B.opAdj Θ (B.rho D p f) g = B.rho D p (B.opAdj Θ f) g
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.JFxI
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


