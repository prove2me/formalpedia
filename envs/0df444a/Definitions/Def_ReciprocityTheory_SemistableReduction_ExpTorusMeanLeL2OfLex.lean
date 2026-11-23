-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- name    : ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:37.08441+00:00
-- url     : https://prove2.me/theorems/6baa597d-d072-4ba6-a061-7f5b6008ca27
-- title:
--   Exp Torus Mean Le L2 Of Lex
-- statement:
--   Definitions and structural lemmas for Exp Torus Mean Le L2 Of Lex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
open Finset
def coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) : MvPolynomial ι ℂ →ₗ[ℂ] EuclideanSpace ℂ T where
  toFun P := WithLp.toLp 2 fun t : T => P.coeff t
  map_add' P Q := by ext t; simp
  map_smul' c P := by ext t; simp
end ReciprocityTheory.MultiplicativeHeights


