-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
-- name    : GroundTheory_AutomorphicForms_AffineBruhat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:12.099971+00:00
-- url     : https://prove2.me/theorems/146f4054-5f0a-49ca-873d-68de0fa91dc1
-- title:
--   Affine Bruhat
-- statement:
--   Definitions and structural lemmas for Affine Bruhat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
namespace GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
section Iwahori
def residueReduction : GL (Fin n) 𝒪[F] →* GL (Fin n) (IsLocalRing.ResidueField 𝒪[F]) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F])
def iwahori : Subgroup (GL (Fin n) F) :=
  ((borel n (IsLocalRing.ResidueField 𝒪[F])).comap (residueReduction F n)).map (integralGLHom F n)
end Iwahori
section AffineWeyl
theorem uniformizer_ne_zero : ϖ ≠ 0 := fun h =>
  (irreducible_uniformizer F).ne_zero (Subtype.ext h)
def diagPow : (Fin n → Multiplicative ℤ) →* GL (Fin n) F where
  toFun a :=
    { val := diagonal fun i => ϖ ^ (a i).toAdd
      inv := diagonal fun i => ϖ ^ (-(a i).toAdd)
      val_inv := by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        rw [← zpow_add₀ (uniformizer_ne_zero F), add_neg_cancel, zpow_zero]
      inv_val := by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        rw [← zpow_add₀ (uniformizer_ne_zero F), neg_add_cancel, zpow_zero] }
  map_one' := by
    refine Units.ext ?_
    change (diagonal fun i => ϖ ^ ((1 : Fin n → Multiplicative ℤ) i).toAdd) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    simp
  map_mul' a b := by
    refine Units.ext ?_
    change (diagonal fun i => ϖ ^ ((a * b) i).toAdd) =
      (diagonal fun i => ϖ ^ (a i).toAdd) * (diagonal fun i => ϖ ^ (b i).toAdd)
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    rw [Pi.mul_apply, toAdd_mul, zpow_add₀ (uniformizer_ne_zero F)]
theorem diagPow_val (a : Fin n → Multiplicative ℤ) :
    (diagPow F n a : Matrix (Fin n) (Fin n) F) = diagonal fun i => ϖ ^ (a i).toAdd :=
  rfl
def permAct : Equiv.Perm (Fin n) →* MulAut (Fin n → Multiplicative ℤ) where
  toFun σ :=
    { toFun := fun a i => a (σ⁻¹ i)
      invFun := fun a i => a (σ i)
      left_inv := fun a => funext fun i => by simp
      right_inv := fun a => funext fun i => by simp
      map_mul' := fun _ _ => rfl }
  map_one' := by
    ext a i
    rfl
  map_mul' σ τ := by
    ext a i
    show a ((σ * τ)⁻¹ i) = a (τ⁻¹ (σ⁻¹ i))
    rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply]
theorem permAct_apply (σ : Equiv.Perm (Fin n)) (a : Fin n → Multiplicative ℤ) (i : Fin n) :
    permAct n σ a i = a (σ⁻¹ i) :=
  rfl
abbrev ExtendedAffineWeyl := (Fin n → Multiplicative ℤ) ⋊[permAct n] Equiv.Perm (Fin n)
theorem permGL_mul_diagPow_mul_inv (σ : Equiv.Perm (Fin n)) (a : Fin n → Multiplicative ℤ) :
    permGL F σ * diagPow F n a * (permGL F σ)⁻¹ = diagPow F n (permAct n σ a) := by
  refine Units.ext ?_
  ext i j
  rw [← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply, diagPow_val,
    diagPow_val, diagonal_apply, diagonal_apply]
  simp only [permAct_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij, if_neg]
    intro h
    exact hij (σ⁻¹.injective h)
def affineWeylGL : ExtendedAffineWeyl n →* GL (Fin n) F :=
  SemidirectProduct.lift (diagPow F n) (permGL F) fun σ => by
    ext a : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [permGL_mul_diagPow_mul_inv]
end AffineWeyl
section Existence
variable {F n} in

def RowsReducedOn (M : Matrix (Fin n) (Fin n) F) (R : Finset (Fin n)) : Prop :=
  ∃ p : Fin n → Fin n, ∀ i ∈ R,
    M i (p i) ≠ 0 ∧ (∀ c, c ≠ p i → M i c = 0) ∧ (∀ r, r ≠ i → M r (p i) = 0)
end Existence
section Decomposition
end Decomposition
section Integral
end Integral
end GLnLocal
end GroundTheory.Automorphic


