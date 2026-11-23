-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:50.479116+00:00
-- url     : https://prove2.me/theorems/5319b632-524a-435e-8d5c-e293cf6cbb2d
-- title:
--   Exists Norm Tensor
-- statement:
--   Definitions and structural lemmas for Exists Norm Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/ExistsNormTensor.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Published
def HasseNormSt : Prop := (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2)
namespace HasseNormSt
open scoped TensorProduct
end HasseNormSt
end GlobalTheory.Published


