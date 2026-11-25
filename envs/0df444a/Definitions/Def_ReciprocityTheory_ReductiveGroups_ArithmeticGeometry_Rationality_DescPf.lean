-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:16:53.17781+00:00
-- url     : https://prove2.me/theorems/cd552e39-ff60-48b6-a30e-2aab696bd7dc
-- title:
--   Desc Pf
-- statement:
--   Definitions and structural lemmas for Desc Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
namespace DescPf
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]
noncomputable def trT [FiniteDimensional K K₂] : K₂ ⊗[K] V →ₗ[K] V :=
  TensorProduct.lid K V ∘ₗ LinearMap.rTensor V (Algebra.trace K K₂)
end DescPf
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


