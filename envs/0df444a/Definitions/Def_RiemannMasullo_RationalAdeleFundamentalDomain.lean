-- Prove2me | Definitions.Def_RiemannMasullo_RationalAdeleFundamentalDomain
-- name    : RiemannMasullo_RationalAdeleFundamentalDomain
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T23:50:25.328037+00:00
-- url     : https://prove2.me/theorems/2815a83d-8227-446e-b426-fc0ae23a569c
-- title:
--   The rational adelic fundamental domain
-- statement:
--   The rational adelic fundamental domain has real coordinate in the half-open unit interval and integral coordinates at every finite place.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L91-L95

import Definitions.Def_RiemannMasullo_AdelicExtensions
import Mathlib
open NumberField InfinitePlace.Completion
open scoped NumberField.AdeleRing
namespace RiemannMasullo
def ratAdeleFundamentalDomain : Set 𝔸[ℚ] :=
  {a | extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace) ∈ Set.Ico 0 1 ∧
    a ∈ integralAdelesOutside ℚ ∅}
end RiemannMasullo


