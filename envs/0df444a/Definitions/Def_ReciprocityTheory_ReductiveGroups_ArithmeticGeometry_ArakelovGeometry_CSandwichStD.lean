-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:35:14.479802+00:00
-- url     : https://prove2.me/theorems/a634aa2b-7ce8-5d08-9673-298f5493d48b
-- title:
--   CSandwich St D
-- statement:
--   Definitions and structural lemmas for CSandwich St D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
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
def monoZ {N : ℕ} (a : Fin N → ℕ) : MvPolynomial (Fin N) ℤ :=
  monomial (Finsupp.equivFunOnFinite.symm a) 1
def prodForm (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ) (h : MvPolynomial (Ix κ) ℤ) :
    MvPolynomial (Ix κ) ℤ :=
  rename e (monoZ a) * h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


