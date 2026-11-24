-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:51.097621+00:00
-- url     : https://prove2.me/theorems/f2e4b47a-692a-4244-9519-d1a501b28f41
-- title:
--   PMinimal Prime Multi Homog
-- statement:
--   Definitions and structural lemmas for PMinimal Prime Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
section Regrading
variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
end Regrading
section Lex
variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
def lexRelabel (e : K ≃ Fin (Fintype.card K)) : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun j => b (e.symm j))
  map_zero' := rfl
  map_add' _ _ := rfl
variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]
end Lex
end GroundTheory.Heights₂.Heights.NumbersDVR


