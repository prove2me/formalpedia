-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
-- name    : Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:36.837436+00:00
-- url     : https://prove2.me/theorems/a39868a5-f9f7-4d24-8d74-d59a5ed32349
-- title:
--   Shear Hypothesis Two
-- statement:
--   Definitions and structural lemmas for Shear Hypothesis Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]
def extW {N N' : ℕ} (v : Fin N → ℕ) : Fin N' → ℕ :=
  fun j => if h : (j : ℕ) < N then v ⟨j, h⟩ else 0
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange


