-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_IsOpenStabOfMemNhds
-- name    : Development_AutomorphicArithmetic_IntegralCasts_IsOpenStabOfMemNhds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:49:05.568584+00:00
-- url     : https://prove2.me/theorems/9588636a-d29a-42b9-98e0-68afc29caa3e
-- title:
--   Is Open Stab Of Mem Nhds
-- statement:
--   Definitions and structural lemmas for Is Open Stab Of Mem Nhds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/IsOpenStabOfMemNhds.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsOpenStabilizer
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv


set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.CuspRep
abbrev BlockIx (a r : ℕ) := {p : Fin a × Fin a // p.1.val < r ∧ r ≤ p.2.val}
section
variable {a : ℕ} {R : Type} [CommRing R]
def nilM {r : ℕ} (x : BlockIx a r → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if h : i.val < r ∧ r ≤ j.val then x ⟨(i, j), h⟩ else 0
theorem nilM_mul_self {r : ℕ} (x : BlockIx a r → R) : nilM x * nilM x = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]
def unip {r : ℕ} (x : BlockIx a r → R) : GL (Fin a) R where
  val := 1 + nilM x
  inv := 1 - nilM x
  val_inv := by simp [add_mul, mul_sub, nilM_mul_self]
  inv_val := by simp [sub_mul, mul_add, nilM_mul_self]
end
def invT (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R →* GL (Fin a) R :=
  (Reformulated.TransposeInverseTheory.transposeInv : GL (Fin a) R ≃* GL (Fin a) R).toMonoidHom
def twRep {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Representation ℂ G V where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm (χ h : ℂ)]
end GlobalTheory.CuspRep


