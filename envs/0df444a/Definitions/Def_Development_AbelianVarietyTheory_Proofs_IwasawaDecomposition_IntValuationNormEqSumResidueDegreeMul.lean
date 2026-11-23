-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:50.276811+00:00
-- url     : https://prove2.me/theorems/6a441b0f-3740-465d-930e-80bc4cf718a9
-- title:
--   Int Valuation Norm Eq Sum Residue Degree Mul
-- statement:
--   Definitions and structural lemmas for Int Valuation Norm Eq Sum Residue Degree Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
namespace GlobalTheory.NormValuation
def exponent {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (I : Ideal R) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk I).factors
section
variable {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R)
end
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
end GlobalTheory.NormValuation
namespace GlobalTheory.NormValuation
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
end GlobalTheory.NormValuation


