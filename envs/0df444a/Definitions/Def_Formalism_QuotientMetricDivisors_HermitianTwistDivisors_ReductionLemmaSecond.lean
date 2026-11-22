-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:32.450748+00:00
-- url     : https://prove2.me/theorems/d75c1068-b8af-4ad4-9a22-2fd108311b85
-- title:
--   Reduction Lemma Second
-- statement:
--   Definitions and structural lemmas for Reduction Lemma Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaSecond.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace Rb
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def tw (σ : K →+* ℂ) : K →+* ℂ := (starRingEnd ℂ).comp (σ.comp (starRingEnd K))
def plc (v : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (tw v.embedding)
def Qd {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) (φ : K →+* ℂ) : ℂ :=
  ((P.map φ) * (H.map φ)⁻¹ * (P.map φ)ᴴ).det
end Rb
end Formalism.DivisionValues


