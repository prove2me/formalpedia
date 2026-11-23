-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:26.56314+00:00
-- url     : https://prove2.me/theorems/6631a684-93cb-48ad-b704-18aebc4a2abb
-- title:
--   Exists Sq Zero Extend Localization Away Pow
-- statement:
--   Definitions and structural lemmas for Exists Sq Zero Extend Localization Away Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSqZeroExtendLocalizationAwayPow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SecGlue
def sqZeroInterp {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B]
    [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S) (h : ∀ x, β x - α x ∈ J)
    (c : S) : B →ₐ[R] S where
  toFun x := α x + c * (β x - α x)
  map_one' := by simp
  map_mul' x y := by
    have hxy : (β x - α x) * (β y - α y) = 0 := by
      have hm := Ideal.mul_mem_mul (h x) (h y)
      rw [← pow_two, hJ] at hm
      simpa using hm
    simp only [map_mul]
    linear_combination (c - c ^ 2) * hxy
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring
  commutes' r := by simp
end GlobalTheory.SecGlue


