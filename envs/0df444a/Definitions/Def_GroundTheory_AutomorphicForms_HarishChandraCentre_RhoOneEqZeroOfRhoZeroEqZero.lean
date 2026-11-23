-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:46.320791+00:00
-- url     : https://prove2.me/theorems/3f3f47b1-8c0b-48c8-ba91-33e20e787ae3
-- title:
--   Rho One Eq Zero Of Rho Zero Eq Zero
-- statement:
--   Definitions and structural lemmas for Rho One Eq Zero Of Rho Zero Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
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
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
noncomputable def rhoDeriv (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) :
    Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ fun a => ∑ i, C (M i a.1) * (X (i, a.2) + C (c i a.2))
theorem rhoDeriv_X (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) (a : Fin n × Fin n) :
    rhoDeriv c M (X a) = ∑ i, C (M i a.1) * (X (i, a.2) + C (c i a.2)) :=
  mkDerivation_X ℂ _ a
theorem rhoDeriv_add (c : Matrix (Fin n) (Fin n) ℂ) (M N : gl n) :
    rhoDeriv c (M + N) = rhoDeriv c M + rhoDeriv c N := by
  apply derivation_ext
  intro a
  simp only [rhoDeriv_X, Derivation.add_apply, Matrix.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]
theorem rhoDeriv_smul (c : Matrix (Fin n) (Fin n) ℂ) (r : ℂ) (M : gl n) :
    rhoDeriv c (r • M) = r • rhoDeriv c M := by
  apply derivation_ext
  intro a
  simp only [rhoDeriv_X, Derivation.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Finset.smul_sum, smul_eq_C_mul, mul_assoc]
theorem rhoDeriv_rhoDeriv_X (c : Matrix (Fin n) (Fin n) ℂ) (P Q : gl n) (a : Fin n × Fin n) :
    rhoDeriv c P (rhoDeriv c Q (X a)) =
      ∑ k, C ((P * Q) k a.1) * (X (k, a.2) + C (c k a.2)) := by
  rw [rhoDeriv_X, map_sum]
  simp only [Derivation.leibniz, Derivation.map_add, derivation_C, smul_zero, add_zero,
    smul_eq_mul, mul_zero, rhoDeriv_X, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  ring
theorem rhoDeriv_lie (c : Matrix (Fin n) (Fin n) ℂ) (M N : gl n) :
    rhoDeriv c ⁅M, N⁆ = ⁅rhoDeriv c M, rhoDeriv c N⁆ := by
  apply derivation_ext
  intro a
  rw [Derivation.commutator_apply, rhoDeriv_rhoDeriv_X, rhoDeriv_rhoDeriv_X, rhoDeriv_X,
    LieRing.of_associative_ring_bracket]
  simp only [Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
noncomputable def rhoLie (c : Matrix (Fin n) (Fin n) ℂ) : gl n →ₗ⁅ℂ⁆ Module.End ℂ (Poly n) where
  toFun M := (rhoDeriv c M : Poly n →ₗ[ℂ] Poly n)
  map_add' M N := by rw [rhoDeriv_add]; rfl
  map_smul' r M := by rw [rhoDeriv_smul]; rfl
  map_lie' {M N} := by
    rw [rhoDeriv_lie, Derivation.commutator_coe_linear_map]
noncomputable def rho (c : Matrix (Fin n) (Fin n) ℂ) : U n →ₐ[ℂ] Module.End ℂ (Poly n) :=
  UniversalEnvelopingAlgebra.lift ℂ (rhoLie c)
noncomputable def rowDeriv (i j : Fin n) : Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ fun a => if a.1 = j then X (i, a.2) else 0
noncomputable def shift : Poly n ≃ₐ[ℂ] Poly n :=
  AlgEquiv.ofAlgHom (aeval fun a => X a + C (if a.1 = a.2 then 1 else 0))
    (aeval fun a => X a - C (if a.1 = a.2 then 1 else 0))
    (by ext a : 1; simp) (by ext a : 1; simp)
def geDeg (t : ℕ) : Submodule ℂ (Poly n) where
  carrier := {f | ∀ s : Fin n × Fin n →₀ ℕ, s.degree < t → coeff s f = 0}
  add_mem' {f g} hf hg s hs := by rw [coeff_add, hf s hs, hg s hs, add_zero]
  zero_mem' s _ := coeff_zero s
  smul_mem' r f hf s hs := by rw [coeff_smul, hf s hs, smul_zero]
noncomputable def iterPd (w : List (Fin n × Fin n)) (f : Poly n) : Poly n :=
  w.foldr (fun a g => pderiv (a.2, a.1) g) f
end GroundTheory.Automorphic.HarishChandra


