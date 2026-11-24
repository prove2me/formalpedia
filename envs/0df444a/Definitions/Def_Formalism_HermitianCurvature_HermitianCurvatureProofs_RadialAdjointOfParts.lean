-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:20:29.162962+00:00
-- url     : https://prove2.me/theorems/46baa14f-b8d2-4726-a670-1f3bc7dde4d0
-- title:
--   Radial Adjoint Of Parts
-- statement:
--   Definitions and structural lemmas for Radial Adjoint Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RadialAdjointOfParts.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
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
namespace Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def Exhaust : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) (K : Set ((Fin r → ℂ) × ℂ)),
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') f → IsEqv D (Om k r D.z D.z') f →
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    (∀ q ∈ QDom k r D.z D.z', q ∉ K → f (B.gq D q) = 0) →
    ∃ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F ∧
      (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) ∧
      ∀ g ∈ Om k r D.z D.z', B.JF D F g = f g
def JThetaC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ → B.CkOn ⊤ (B.GV k r) F →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) →
    ∀ g ∈ Om k r D.z D.z', B.JF D (B.opApply Θ F) g = B.opApply Θ (B.JF D F) g ∧
      B.JF D (B.opAdj Θ F) g = B.opAdj Θ (B.JF D F) g
def BetaAdjC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.IntFormula D → B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ →
    B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F' →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F' g = 0) →
    B.beta D (B.opApply Θ F) F' = B.beta D F (B.opAdj Θ F')
def RadAdjOfParts : Prop := Exhaust → JThetaC → BetaAdjC → RadAdj
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end Formalism.FourierDecayAlt.P.JFxG
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


