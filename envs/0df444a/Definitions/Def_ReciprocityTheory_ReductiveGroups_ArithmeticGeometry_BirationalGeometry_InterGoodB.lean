-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:10.159128+00:00
-- url     : https://prove2.me/theorems/8e7b32a9-f035-4158-ade9-7a9ca5784dd0
-- title:
--   Inter Good B
-- statement:
--   Definitions and structural lemmas for Inter Good B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}
abbrev qmap : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
def qIdeal (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) := P.map qmap
def ratHom (P : Ideal (MvPolynomial σ ℤ)) :
    MvPolynomial σ ℤ ⧸ P →+* MvPolynomial σ ℚ ⧸ qIdeal P :=
  Ideal.quotientMap (qIdeal P) qmap Ideal.le_comap_map
end
end ReciprocityTheory.ChartRestriction.G.Geo


