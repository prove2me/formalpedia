-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:41.640823+00:00
-- url     : https://prove2.me/theorems/cfb1e49b-e8d1-4ade-ba42-c12fe4a5c084
-- title:
--   Mul Stable Integral
-- statement:
--   Definitions and structural lemmas for Mul Stable Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace Ker
def mulEnd (L : PeriodPair) (α : ℂ) (h : MulStable L α) : L.lattice →ₗ[ℤ] L.lattice where
  toFun x := ⟨α * x, h _ x.2⟩
  map_add' x y := by ext; simp [mul_add]
  map_smul' n x := by ext; simp; ring
end Ker
open Ker
end Formalism.L2.Th1.F


