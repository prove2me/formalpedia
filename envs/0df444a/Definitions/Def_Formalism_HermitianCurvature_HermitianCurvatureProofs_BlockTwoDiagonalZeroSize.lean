-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:55.491608+00:00
-- url     : https://prove2.me/theorems/095fabe3-43e1-40c4-9d37-3024fda3bdfa
-- title:
--   Block Two Diagonal Zero Size
-- statement:
--   Definitions and structural lemmas for Block Two Diagonal Zero Size, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
abbrev AB (p : ℕ) : Type := (Fin 1 → Fin p → ℂ) × (Fin p → Fin 1 → ℂ)
def gI (β c : ℂ) {p : ℕ} (Ψ : G.Mat (p + 1) → V) (H : G.Mat p) (y : AB p) : V :=
  G.psi β (cornerA y.1 + cornerB y.2) • Ψ (Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c))
def Psc (β c : ℂ) {p : ℕ} (Ψ : G.Mat (p + 1) → V) (H : G.Mat p) : V := ∫ y, gI β c Ψ H y
end Formalism.FourierDecayAlt.P.PBJ.Frz
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
instance sfAB (p : ℕ) : SigmaFinite (volume : Measure (AB p)) := by
  have h1 : SigmaFinite (volume : Measure (Fin 1 → Fin p → ℂ)) := inferInstance
  have h2 : SigmaFinite (volume : Measure (Fin p → Fin 1 → ℂ)) := inferInstance
  rw [Measure.volume_eq_prod]; exact Measure.prod.instSigmaFinite
instance sfVU {p : ℕ} (σ : Equiv.Perm (Fin p)) : SigmaFinite (volume : Measure ((LW σ → ℂ) × (G.UT p → ℂ))) := by
  have h1 : SigmaFinite (volume : Measure (LW σ → ℂ)) := inferInstance
  have h2 : SigmaFinite (volume : Measure (G.UT p → ℂ)) := inferInstance
  rw [Measure.volume_eq_prod]; exact Measure.prod.instSigmaFinite
end Formalism.FourierDecayAlt.P.PBJ.Frz
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def Sset (p : ℕ) (R δ' : ℝ) : Set (G.Mat p) := {H | ‖H‖ ≤ R ∧ δ' ≤ ‖G.detM H‖}
end Formalism.FourierDecayAlt.P.PBJ.Frz
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end Formalism.FourierDecayAlt.P.PBJ.Frz
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped Convolution
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
instance haar1 (p : ℕ) : (volume : Measure (Fin 1 → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin 1 => (volume : Measure (Fin p → ℂ)))
instance haar2 (p : ℕ) : (volume : Measure (Fin p → Fin 1 → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin p => (volume : Measure (Fin 1 → ℂ)))
instance haarAB (p : ℕ) : (volume : Measure (AB p)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
instance lfAB (p : ℕ) : IsLocallyFiniteMeasure (volume : Measure (AB p)) :=
  isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
end Formalism.FourierDecayAlt.P.PBJ.Frz
namespace Formalism.FourierDecayAlt.P.PBJ
end Formalism.FourierDecayAlt.P.PBJ


