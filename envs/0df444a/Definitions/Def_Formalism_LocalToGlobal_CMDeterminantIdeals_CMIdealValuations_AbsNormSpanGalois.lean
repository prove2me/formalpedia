-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:58.705494+00:00
-- url     : https://prove2.me/theorems/f062dd6c-2af6-4aec-bd26-6bd369234a39
-- title:
--   Abs Norm Span Galois
-- statement:
--   Definitions and structural lemmas for Abs Norm Span Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
section cauchy
end cauchy
section loc
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
end loc
section galois
variable {K : Type} [Field K] [NumberField K]
def compEquiv (γ : K ≃+* K) : (K →+* ℂ) ≃ (K →+* ℂ) where
  toFun σ := σ.comp (γ : K →+* K)
  invFun σ := σ.comp (γ.symm : K →+* K)
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp
end galois
end Formalism.L2.LamCM


