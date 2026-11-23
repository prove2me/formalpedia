-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:35.343851+00:00
-- url     : https://prove2.me/theorems/29330c55-001d-444e-8c5d-225e88db708b
-- title:
--   Continuous Matrix Entry Abs Sum
-- statement:
--   Definitions and structural lemmas for Continuous Matrix Entry Abs Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompactDualQuot
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal
variable {P Q P' Q' : ℕ}
def sg {P Q : ℕ} : Fin P ⊕ Fin Q → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
def SignCompat (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Prop :=
  ∀ i, sg (e (some i)) = sg i
def l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : ℝ := ∑ i, ∑ j, ‖Z i j‖
def gauge (g : UpqT P Q) : ℝ := l1 (UpqT.mat g - 1)
def baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Sp P Q := Pi.single (e none) 1
def ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ + 2 * ∑ i, ‖y (e (some i))‖
def tanGauge (t : ℝ × Sp P' Q') : ℝ := |t.1| + 2 * ∑ i, ‖t.2 i‖
def polarPt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim
    ((Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I)) t.2
def IsBlockEmb (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  ∀ g, UpqT.mat (j g) (e none) (e none) = 1 ∧ (∀ b, UpqT.mat (j g) (e none) (e (some b)) = 0) ∧
    (∀ a, UpqT.mat (j g) (e (some a)) (e none) = 0) ∧
    ∀ a b, UpqT.mat (j g) (e (some a)) (e (some b)) = UpqT.mat g a b
def expBall (P Q : ℕ) (r : ℝ) : Set (UpqT P Q) :=
  {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
    NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}
end GlobalTheory.CompactDualQuot


