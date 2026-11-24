-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:10.018813+00:00
-- url     : https://prove2.me/theorems/35ee676a-df2c-4607-8dd3-0bad76a2482d
-- title:
--   Alt Coeff
-- statement:
--   Definitions and structural lemmas for Alt Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
abbrev ex (v : Fin m → ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm v
def cf (v : Fin m → ℕ) (P : MvPolynomial (Fin m) ℚ) : ℚ := coeff (ex v) P
def alt (v : Fin m → ℕ) : MvPolynomial (Fin m) ℚ :=
  (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) ℚ) ^ v j).det
def IsAlt (P : MvPolynomial (Fin m) ℚ) : Prop :=
  ∀ σ : Perm (Fin m), rename σ P = (Perm.sign σ : ℤ) • P
def stair (m : ℕ) : Fin m → ℕ := fun j => m - 1 - (j : ℕ)
end
end GroundTheory.Heights₂.Heights.RestTerms.Comb


