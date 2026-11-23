-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:49.381795+00:00
-- url     : https://prove2.me/theorems/52aa7f33-6b5c-48e3-9249-71f0dc09f114
-- title:
--   Localize A
-- statement:
--   Definitions and structural lemmas for Localize A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
def locG {M : Type*} {n : ℕ} (η : M → ℝ) (G : M → V n) : M → V n :=
  fun x => (η x : ℂ) • G x
def locD {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (G : M → V n)
    (D : M → ℂ) : M → ℂ :=
  fun x => (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j
def locS {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (G : M → V n)
    (S : M → Fin n → Fin n → ℂ) : M → Fin n → Fin n → ℂ :=
  fun x j k => (η x : ℂ) * S x j k +
    wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k
end
end ReciprocityTheory.L2DbarEstimates.F


