-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:25:21.049003+00:00
-- url     : https://prove2.me/theorems/201846fc-bdc0-5a17-83c6-07c10e993c77
-- title:
--   Last Level Slice Of Scalar
-- statement:
--   Definitions and structural lemmas for Last Level Slice Of Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
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
namespace Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}
def NNSlice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m → ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        B.gN ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN)
def Slice1 : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)
def SliceRegularityClauses : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) →
      B.InCC (k := k) (r := 0) ((A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))) m (sliceR D F c)) ∧
    ∀ (d : ℕ) (O : Set (Fin d → ℝ)) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0),
      IsOpen O → ContDiffOn ℝ ∞ cx O → ContDiffOn ℝ ∞ μx O → (∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) O
end Formalism.FourierDecayAlt.P.JFxDs5


