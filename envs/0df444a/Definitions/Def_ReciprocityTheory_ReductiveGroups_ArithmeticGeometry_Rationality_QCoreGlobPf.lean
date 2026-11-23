-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:44.473647+00:00
-- url     : https://prove2.me/theorems/1b0e6495-d4d2-45d9-8e02-4e77814fcdaf
-- title:
--   QCore Glob Pf
-- statement:
--   Definitions and structural lemmas for QCore Glob Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
section Mean
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
end Mean
section Regroup
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
noncomputable def under (w : HeightOneSpectrum (𝓞 K₁)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
end Regroup
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


