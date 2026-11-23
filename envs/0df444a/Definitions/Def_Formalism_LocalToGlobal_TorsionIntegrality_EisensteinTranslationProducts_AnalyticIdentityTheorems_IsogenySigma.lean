-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:36.566656+00:00
-- url     : https://prove2.me/theorems/78079630-8c11-45e7-8e3c-98a4d0c8e6bf
-- title:
--   Isogeny Sigma
-- statement:
--   Definitions and structural lemmas for Isogeny Sigma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean

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
open Filter Topology
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace IsogenySigmaQuotient
variable (L : PeriodPair)
open Classical in

def ind (x : ℂ) : WithTop ℤ := if x ∈ L.lattice then 1 else 0
variable (α : ℂ) (S : Finset ℂ)
def num (z : ℂ) : ℂ := sgStar L (α * z) ^ 2
def fac (P z : ℂ) : ℂ := (-(sgStar L P ^ 2)⁻¹) * (sgStar L (z + P) * sgStar L (z - P))
def den (z : ℂ) : ℂ := α ^ 2 * sgStar L z ^ 2 * ∏ P ∈ S, fac L P z
def mlt (ω z : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
end IsogenySigmaQuotient
end Formalism.L2.Th1.F


