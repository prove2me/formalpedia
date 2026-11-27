-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-27T05:26:48.962807+00:00
-- url     : https://prove2.me/theorems/eaae9e79-e751-45f9-afbb-2b955944a105
-- title:
--   Hups Tw Coeff Coeff
-- statement:
--   Definitions and structural lemmas for Hups Tw Coeff Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open Polynomial in

noncomputable def hupsTw {σ R : Type*} [CommRing R] (w : σ → ℕ) :
    MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  MvPolynomial.aeval fun v => Polynomial.C (MvPolynomial.X v) * Polynomial.X ^ (w v)
def hupsWt {σ : Type*} (w : σ → ℕ) (s : σ →₀ ℕ) : ℕ := s.sum fun v k => k * w v
end ReciprocityTheory.ChartRestriction.G.T0


