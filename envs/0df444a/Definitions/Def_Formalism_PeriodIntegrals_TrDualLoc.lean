-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_TrDualLoc
-- name    : Formalism_PeriodIntegrals_TrDualLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:04.592806+00:00
-- url     : https://prove2.me/theorems/a9b921b2-aa34-4226-8b3f-85ccebd09214
-- title:
--   Tr Dual Loc
-- statement:
--   Definitions and structural lemmas for Tr Dual Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/TrDualLoc.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField
namespace PI.TrDualLoc
def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.MainNotions.S.Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) →
    ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp (c * ι t)‖ ≤ 1
end PI.TrDualLoc


