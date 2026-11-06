-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:54:30.284055+00:00
-- url     : https://prove2.me/theorems/69c221cb-e4ad-4982-852a-1deb24d5a855
-- title:
--   Direct Chart Common Denominator
-- statement:
--   Definitions and structural lemmas for Direct Chart Common Denominator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/DirectChartCommonDenominator.lean

import Mathlib
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
open scoped BigOperators Polynomial
variable {k F ι : Type*}
def polynomialCoordinateFamily (k : Type*) [Field k] (ι : Type*) :
    Submodule k[X] (ι →₀ RatFunc k) where
  carrier := {c | ∀ j, c j ∈ Set.range (algebraMap k[X] (RatFunc k))}
  zero_mem' := by
    intro j
    exact ⟨0, by simp⟩
  add_mem' := by
    intro c d hc hd j
    rcases hc j with ⟨r, hr⟩
    rcases hd j with ⟨s, hs⟩
    refine ⟨r + s, ?_⟩
    simpa [Finsupp.add_apply, hr, hs]
  smul_mem' := by
    intro r c hc j
    rcases hc j with ⟨s, hs⟩
    refine ⟨r * s, ?_⟩
    simpa [Finsupp.smul_apply, Algebra.smul_def, hs] using
      (algebraMap k[X] (RatFunc k)).map_mul r s
variable [Field k] [Field F]
variable [Algebra (RatFunc k) F] [Algebra (Polynomial k) F]
  [IsScalarTower (Polynomial k) (RatFunc k) F]
noncomputable def directChartSubmodule (b : Module.Basis ι (RatFunc k) F) :
    Submodule (Polynomial k) F :=
  (polynomialCoordinateFamily k ι).comap
    (b.repr.restrictScalars (Polynomial k)).toLinearMap
noncomputable def scaledDirectChartSubmodule (b : Module.Basis ι (RatFunc k) F)
    (a : Polynomial k) :
    Submodule (Polynomial k) F :=
  (directChartSubmodule b).comap (LinearMap.lsmul (Polynomial k) F a)
end QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator


