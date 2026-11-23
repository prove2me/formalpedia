-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:32.060046+00:00
-- url     : https://prove2.me/theorems/8778e3d2-313e-4abb-bc08-aff4cebd33ea
-- title:
--   Hermitian Pairing Algebra
-- statement:
--   Definitions and structural lemmas for Hermitian Pairing Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace HermitianPairingAlgebra
lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G (a • x) y = a * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
noncomputable def pairL {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) :
    (Fin r → E) →ₗ[𝓞 E] E where
  toFun y := herm G y ξ
  map_add' x y := herm_add_left G x y ξ
  map_smul' a y := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul E a y, herm_smul_left, Algebra.smul_def]
end HermitianPairingAlgebra
end ReciprocityTheory.ChartRestriction.G.FD


