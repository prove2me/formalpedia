-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:12:18.274931+00:00
-- url     : https://prove2.me/theorems/38ac5143-1964-4509-b3b9-2e0fe2bfa8e0
-- title:
--   Aemeasurable Finsum Section
-- statement:
--   Definitions and structural lemmas for Aemeasurable Finsum Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
namespace SectionSum
open MvPolynomial MeasureTheory
noncomputable def liftS {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x)) :
    FractionRing (MvPolynomial (TVar D N) K) →+* OmS Ω D N :=
  IsFractionRing.lift (A := MvPolynomial (TVar D N) K)
    (g := (sHom (K := K) (D := D) j₀ x).toRingHom) h
end SectionSum
end GlobalTheory


