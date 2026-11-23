-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClass
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:34.597051+00:00
-- url     : https://prove2.me/theorems/9c7d39e7-ed6c-42f5-a578-309666bfcdea
-- title:
--   Lattice Count And Gram Det Sign Norm Class
-- statement:
--   Definitions and structural lemmas for Lattice Count And Gram Det Sign Norm Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountAndGramDetSignNormClass.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.NormClass
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
section Orb
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]
def mulLatEquiv (u : Aˣ) : Submodule O A ≃ Submodule O A where
  toFun := mulLat O (u : A)
  invFun := mulLat O ((u⁻¹ : Aˣ) : A)
  left_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.inv_mul_cancel_left]
  right_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.mul_inv_cancel_left]
end Orb
variable {K : UQ}
end GlobalTheory.UnitLemma.NormClass


