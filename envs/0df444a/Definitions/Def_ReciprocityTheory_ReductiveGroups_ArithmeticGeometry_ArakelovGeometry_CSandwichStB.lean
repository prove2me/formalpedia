-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:13.982905+00:00
-- url     : https://prove2.me/theorems/441d6f98-69e4-5b0a-8d74-7018c02d9da2
-- title:
--   CSandwich St B
-- statement:
--   Definitions and structural lemmas for CSandwich St B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
def traceMat {r δ : ℕ} (D N : ℕ) (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ) :
    Matrix (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) (Fin r) ℤ :=
  Matrix.of fun p j => coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N (finProdFinEquiv.symm p).2))
    (g j (finProdFinEquiv.symm p).1)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


