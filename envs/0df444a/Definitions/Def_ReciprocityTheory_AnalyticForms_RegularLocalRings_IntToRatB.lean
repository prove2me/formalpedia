-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:21.004321+00:00
-- url     : https://prove2.me/theorems/bd0f28ae-e65a-466a-aa55-9385f88c69d4
-- title:
--   Int To Rat B
-- statement:
--   Definitions and structural lemmas for Int To Rat B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_map_isPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
noncomputable def eQ (x : PrimeSpectrum (MvPolynomial σ ℤ)) (h : ChZero x.asIdeal) :
    PrimeSpectrum (MvPolynomial σ ℚ) :=
  ⟨Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal, map_isPrime x.asIdeal h⟩
end ReciprocityTheory.AnForm.R.IntegerToRational


