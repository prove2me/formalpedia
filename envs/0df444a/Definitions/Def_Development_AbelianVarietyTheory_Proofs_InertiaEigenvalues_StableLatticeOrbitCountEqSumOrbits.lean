-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbits
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbits
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:31.382698+00:00
-- url     : https://prove2.me/theorems/58fa10ce-7bdb-5c24-869d-5b5ed3996e23
-- title:
--   Stable Lattice Orbit Count Eq Sum Orbits
-- statement:
--   Definitions and structural lemmas for Stable Lattice Orbit Count Eq Sum Orbits, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableLatticeOrbitCountEqSumOrbits.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Theorems.Thm_GlobalTheory_UnitLemma_stLat_smul_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
namespace GlobalTheory.UnitLemma
section Bridge
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
def orbEquiv (g : A) : Orb O (⊤ : Subgroup Aˣ) (stLat O E g) ≃ MulAction.orbitRel.Quotient Aˣ (stLat O E g) where
  toFun := Quot.lift (fun L => (Quotient.mk _ L : MulAction.orbitRel.Quotient Aˣ (stLat O E g)))
    (by
      rintro L M ⟨t, -, h⟩
      exact (Quotient.sound (show M ∈ MulAction.orbit Aˣ L from ⟨t, Subtype.ext (by rw [stLat_smul_val]; exact h.symm)⟩)).symm)
  invFun := Quotient.lift (fun L => (Quot.mk _ L : Orb O (⊤ : Subgroup Aˣ) (stLat O E g)))
    (by
      rintro a b ⟨t, ht⟩
      exact (Quot.sound ⟨t, Subgroup.mem_top t, by rw [← ht, stLat_smul_val]⟩).symm)
  left_inv := by
    intro o
    induction o using Quot.ind
    rfl
  right_inv := by
    intro o
    induction o using Quotient.inductionOn
    rfl
end Bridge
end GlobalTheory.UnitLemma


