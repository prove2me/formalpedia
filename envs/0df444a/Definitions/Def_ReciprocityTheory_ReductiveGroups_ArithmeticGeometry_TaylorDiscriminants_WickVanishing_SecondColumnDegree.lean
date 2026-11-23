-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:40.876392+00:00
-- url     : https://prove2.me/theorems/47df312b-2213-4117-aefc-68eebe5eeb53
-- title:
--   Second Column Degree
-- statement:
--   Definitions and structural lemmas for Second Column Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
section General
variable {σ : Type} [Fintype σ]
end General
section Columns
variable {ι : Type} [Fintype ι] {n : ℕ}
abbrev colE (b : Fin n) : MvPolynomial ι k →ₐ[k] MvPolynomial (ι × Fin n) k := rename fun l => (l, b)
def cB (c : ι → ι → k) (b : Fin n) : ι × Fin n → ι × Fin n → k :=
  fun p q => if p.2 = b ∧ q.2 = b then c p.1 q.1 else 0
end Columns
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree


