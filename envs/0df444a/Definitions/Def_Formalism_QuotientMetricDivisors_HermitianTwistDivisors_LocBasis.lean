-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:31.297563+00:00
-- url     : https://prove2.me/theorems/47f2b0a6-5fa0-4fcd-9c5c-f1b7b13c7d75
-- title:
--   Loc Basis
-- statement:
--   Definitions and structural lemmas for Loc Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.DivisionValues
namespace SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
lemma hcompl_le (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ nonZeroDivisors (𝓞 K) := by
  apply Submonoid.closure_le.mpr
  intro s hs
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hs.1 w.asIdeal.zero_mem
abbrev A (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (hcompl_le w)
end SemilocalBasisHermitianTwistDivisors
end Formalism.DivisionValues


