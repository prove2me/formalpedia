-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:38.021794+00:00
-- url     : https://prove2.me/theorems/9cad7990-efaa-49e1-bc68-4128373409f7
-- title:
--   Continuous On Tens Op
-- statement:
--   Definitions and structural lemmas for Continuous On Tens Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/ContinuousOnTensOp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Module
namespace PI.ScPiBuildW.Tens
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Idx (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)] : Type :=
  ∀ i, Fin (finrank ℂ (Vl i))
abbrev TV (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)] : Type :=
  EuclideanSpace ℂ (Idx Vl)
variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]
def bas (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
    [∀ i, FiniteDimensional ℂ (Vl i)] (i : ι) : OrthonormalBasis (Fin (finrank ℂ (Vl i))) ℂ (Vl i) :=
  stdOrthonormalBasis ℂ (Vl i)
def tensU (x : ∀ i, Vl i) : TV Vl :=
  WithLp.toLp 2 (fun p : Idx Vl => ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ)
def opMat (A : ∀ i, Vl i →L[ℂ] Vl i) : Matrix (Idx Vl) (Idx Vl) ℂ :=
  fun p q => ∏ i, ⟪bas Vl i (p i), A i (bas Vl i (q i))⟫_ℂ
def tensOp (A : ∀ i, Vl i →L[ℂ] Vl i) : TV Vl →L[ℂ] TV Vl :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (opMat A))
end PI.ScPiBuildW.Tens


