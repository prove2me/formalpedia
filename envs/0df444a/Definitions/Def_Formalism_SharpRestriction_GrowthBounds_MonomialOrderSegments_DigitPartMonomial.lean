-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:32.667987+00:00
-- url     : https://prove2.me/theorems/5fb22562-d37b-4c69-adc7-4a8018371549
-- title:
--   Digit Part Monomial
-- statement:
--   Definitions and structural lemmas for Digit Part Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
def lsup {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) : MvPolynomial σ K →ₗ[K] MvPolynomial τ K :=
  (basisMonomials σ K).constr K φ
def ddivL {σ : Type} (M : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  lsup fun α => if M ≤ α then monomial (α - M) (α.prod fun x k => (k.choose (M x) : K)) else 0
namespace TwistData
variable (D : TwistData K)
def digitPartL (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) :
    MvPolynomial (D.OL × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun α => if D.InClass p ρ α then monomial (D.liftE p α) 1 else 0
end TwistData
end Formalism.MainNotions.PlaneGram


