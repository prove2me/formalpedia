-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
-- name    : Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:30.80881+00:00
-- url     : https://prove2.me/theorems/ae673fb8-2d15-4bdf-a79e-f4824254d763
-- title:
--   Almost Everywhere Spherical
-- statement:
--   Definitions and structural lemmas for Almost Everywhere Spherical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/AlmostEverywhereSpherical.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
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
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
open Classical in

def flt_cost {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ S ∧ LL.vec v.1 = b then Nat.castAddMonoidHom ℤ else 0
def flt_compat (e : ℤ) (bm : Bool) : Prop := (e = 1 ∧ bm = false) ∨ (e = -1 ∧ bm = true)
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1


