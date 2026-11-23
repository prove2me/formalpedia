-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:27.867651+00:00
-- url     : https://prove2.me/theorems/02201e16-a4b2-4d47-8951-cd10bc74218b
-- title:
--   Poly Deriv Monomial One
-- statement:
--   Definitions and structural lemmas for Poly Deriv Monomial One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
section ItD
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
def itD (f : W → ℂ) (l : List W) (z : W) : ℂ :=
  iteratedFDeriv ℂ l.length f z (fun j => l.get j)
def colL {n : ℕ} (L : List (Fin n × W)) (k : Fin n) : List W :=
  (L.filter (fun p => p.1 = k)).map Prod.snd
end ItD
section PD
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
def pdTerm (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
    (fun k => u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))
end PD
end
end ReciprocityTheory.ChartRestriction.G.I2


