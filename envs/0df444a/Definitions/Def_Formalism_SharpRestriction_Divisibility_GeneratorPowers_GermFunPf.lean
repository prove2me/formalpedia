-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:44.825239+00:00
-- url     : https://prove2.me/theorems/76a17265-7c86-481b-a79c-0cc1a307a694
-- title:
--   Germ Fun Pf
-- statement:
--   Definitions and structural lemmas for Germ Fun Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GermFun
def ordGE (R ι : Type) [CommRing R] (n : ℕ) : Ideal (MvPolynomial ι R) where
  carrier := {p | ∀ e ∈ p.support, n ≤ e.degree}
  add_mem' := by
    classical
    intro p q hp hq e he
    rcases Finset.mem_union.1 (MvPolynomial.support_add he) with h | h
    exacts [hp e h, hq e h]
  zero_mem' := by
    intro e he
    simp at he
  smul_mem' := by
    classical
    intro c p hp e he
    rw [smul_eq_mul] at he
    obtain ⟨a, -, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul c p he)
    rw [map_add]
    exact le_add_left (hp b hb)
end GermFun
end Formalism.MainNotions.ModuliIntegralCharts.H1


