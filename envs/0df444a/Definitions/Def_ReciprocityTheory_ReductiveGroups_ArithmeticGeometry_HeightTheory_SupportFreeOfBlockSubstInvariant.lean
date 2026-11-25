-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:28:39.737511+00:00
-- url     : https://prove2.me/theorems/cc0ddcd7-79bd-48ad-87ed-8ee3c5ba347e
-- title:
--   Support Free Of Block Subst Invariant
-- statement:
--   Definitions and structural lemmas for Support Free Of Block Subst Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SupportFreeOfBlockSubstInvariant.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Comp
variable {K : Type} [Field K] {D N : ℕ}
def degB (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) : ℕ := ∑ j, s (b, j)
noncomputable def compB (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) :
    MvPolynomial (TVar D N) K :=
  ∑ s ∈ p.support.filter (fun s => degB b s = k), monomial s (coeff s p)
end Comp
section Pres
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
end Pres
end ReciprocityTheory.ChartRestriction.G.T0


