-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:52.914945+00:00
-- url     : https://prove2.me/theorems/4a9ed755-ef36-4632-b03e-79267412b552
-- title:
--   Hecke LFunction Ideal Euler Product
-- statement:
--   Definitions and structural lemmas for Hecke LFunction Ideal Euler Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
section A
section General
variable {R : Type} [CommRing R]
end General
section Red
variable (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [CommRing k] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] k] (red : O →+* k)
  (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] k z)
end Red
end A
section Five
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
end Five
def pi0SubstHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] :
    O⟦X⟧ →+* O⟦X⟧ :=
  (substAlgHom (hasSubst_pi0_alt l O) : O⟦X⟧ →ₐ[O] O⟦X⟧).toRingHom
end Formalism.CohomologicalDescent.FrobeniusPeriodChange


