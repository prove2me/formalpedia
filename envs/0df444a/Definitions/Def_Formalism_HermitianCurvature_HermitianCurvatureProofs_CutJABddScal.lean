-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:31:07.836069+00:00
-- url     : https://prove2.me/theorems/941cf16a-4b5d-543d-8a71-c108ec8335a7
-- title:
--   Cut JABdd Scal
-- statement:
--   Definitions and structural lemmas for Cut JABdd Scal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.JA
noncomputable section
def phiR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g ⟨r, by omega⟩ / Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))
def phiD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)) / (starRingEnd ℂ) (Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)))
section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def ScalOK (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ) : Prop :=
  B.CkOn ⊤ (B.GPos D) φ ∧
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m)
end
def JAScalBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ), K * ((r : ℝ) + 1) ≤ Bg →
    ScalOK D Bg (phiR k r D.z D.z') ∧ ScalOK D Bg (phiD k r D.z D.z')
def JAScalConj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ),
    ScalOK D Bg φ → ScalOK D Bg (fun g => (starRingEnd ℂ) (φ g))
end
end Formalism.FourierDecayAlt.P.CutMP.JA


