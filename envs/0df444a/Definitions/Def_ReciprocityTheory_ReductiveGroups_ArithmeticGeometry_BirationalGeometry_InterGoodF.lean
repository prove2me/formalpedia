-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:07.446916+00:00
-- url     : https://prove2.me/theorems/1283d064-ced5-406c-974f-030cfebd26ba
-- title:
--   Inter Good F
-- statement:
--   Definitions and structural lemmas for Inter Good F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def blkWt : (Σ k, ι k) → (K →₀ ℕ) := fun p => Finsupp.single p.1 1
def oneK : K →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
def segMon (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ := ∏ k, X ⟨k, i k⟩
variable (k0 : K)
def sWt (r : ℕ) : Fin r ⊕ {k // k ≠ k0} → (K →₀ ℕ) :=
  Sum.elim (fun _ => oneK) (fun k' => Finsupp.single k'.1 1)
end
end ReciprocityTheory.ChartRestriction.G.Geo


