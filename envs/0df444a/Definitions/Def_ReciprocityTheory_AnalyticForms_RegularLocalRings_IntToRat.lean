-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:46.380579+00:00
-- url     : https://prove2.me/theorems/d6f6de46-8dca-49ad-a17a-993d105300da
-- title:
--   Int To Rat
-- statement:
--   Definitions and structural lemmas for Int To Rat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial IntegerToRational
variable {σ : Type} [Fintype σ]
noncomputable def extQ (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) :=
  Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P
end ReciprocityTheory.AnForm.R


