-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:32.709498+00:00
-- url     : https://prove2.me/theorems/3ea4692b-90ee-5372-9ec0-aa3124e95c33
-- title:
--   Consequences
-- statement:
--   Definitions and structural lemmas for Consequences, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
noncomputable def casimirGL2 : U 2 :=
  (1 / 2 : ℂ) • ((e (0, 0) - e (1, 1)) * (e (0, 0) - e (1, 1))) + e (0, 1) * e (1, 0) +
    e (1, 0) * e (0, 1)
def conjAlgHom (g : (gl n)ˣ) : gl n →ₐ[ℂ] gl n where
  toFun X := (g : gl n) * X * ↑g⁻¹
  map_one' := by simp
  map_mul' X Y := by
    simp only [mul_assoc]; rw [← mul_assoc (↑g⁻¹ : gl n) (g : gl n), Units.inv_mul, one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      Units.mul_inv]
noncomputable def conjU (g : (gl n)ˣ) : U n →ₐ[ℂ] U n :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (conjAlgHom g).toLieHom)
end GroundTheory.Automorphic.HarishChandra


