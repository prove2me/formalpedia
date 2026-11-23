-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:12.74162+00:00
-- url     : https://prove2.me/theorems/35b784fd-f1b7-45fc-9f57-a3d52a12f889
-- title:
--   Hecke LSeries Eq Sum Principal Partial Series
-- statement:
--   Definitions and structural lemmas for Hecke LSeries Eq Sum Principal Partial Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
def classUnitPart (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (α : 𝓞 K) : ℂ :=
  open Classical in if m = ⊤ then 1 else X (Ideal.span {α}) * (wt φ n (α : K))⁻¹
def classPartFun (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (b : Ideal (𝓞 K))
    (α : 𝓞 K) : ℂ :=
  open Classical in if α ∈ b then classUnitPart φ n m X α else 0
section
variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}
end
end GlobalTheory.HeckeStrip


