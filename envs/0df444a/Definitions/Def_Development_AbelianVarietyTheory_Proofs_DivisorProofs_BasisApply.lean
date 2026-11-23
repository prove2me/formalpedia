-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:24.780741+00:00
-- url     : https://prove2.me/theorems/75e89f80-d710-402d-bc37-ea95a286abb4
-- title:
--   Basis Apply
-- statement:
--   Definitions and structural lemmas for Basis Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace GlobalTheory.UnitaryStd
variable {r g : ℕ}
def matAddEnd (V : Type) [AddCommGroup V] (r : ℕ) : Matrix (Fin r) (Fin r) ℤ →+* AddMonoid.End (Fin r → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp [smul_add, Finset.sum_add_distrib] }
  map_one' := AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) i j • x j = x i
    simp [Matrix.one_apply, ite_smul]
  map_mul' := fun M N => AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (M * N) i j • x j = ∑ k, M i k • ∑ j, N k j • x j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (0 : Matrix (Fin r) (Fin r) ℤ) i j • x j = 0
    simp
  map_add' := fun M N => AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (M + N) i j • x j = ∑ j, M i j • x j + ∑ j, N i j • x j
    simp [add_smul, Finset.sum_add_distrib]
@[nolint unusedArguments]
def Lat {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) : Type :=
  Fin r → (Fin g → ℤ) × (Fin g → ℤ)
variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
instance : AddCommGroup (Lat ρ g) := inferInstanceAs (AddCommGroup (Fin r → (Fin g → ℤ) × (Fin g → ℤ)))
instance : Module (𝓞 E) (Lat ρ g) :=
  Module.compHom (Fin r → (Fin g → ℤ) × (Fin g → ℤ)) ((matAddEnd ((Fin g → ℤ) × (Fin g → ℤ)) r).comp ρ)
variable {ρ g}
theorem add_apply (x y : Lat ρ g) (i : Fin r) : (x + y) i = x i + y i := rfl
theorem zsmul_apply (n : ℤ) (x : Lat ρ g) (i : Fin r) : (n • x) i = n • x i := rfl
@[ext] theorem ext {x y : Lat ρ g} (h : ∀ i, x i = y i) : x = y := funext h
variable (ρ g)
def coordEquiv : Lat ρ g ≃ₗ[ℤ] (Fin r × (Fin g ⊕ Fin g) → ℤ) where
  toFun x := fun p => Sum.elim (x p.1).1 (x p.1).2 p.2
  invFun c := fun i => (fun k => c (i, Sum.inl k), fun k => c (i, Sum.inr k))
  left_inv x := by ext i <;> rfl
  right_inv c := by ext ⟨i, k | k⟩ <;> rfl
  map_add' x y := by ext ⟨i, k | k⟩ <;> rfl
  map_smul' n x := by ext ⟨i, k | k⟩ <;> rfl
def basis : Module.Basis (Fin r × (Fin g ⊕ Fin g)) ℤ (Lat ρ g) := Module.Basis.ofEquivFun (coordEquiv ρ g)
instance : Module.Free ℤ (Lat ρ g) := Module.Free.of_basis (basis ρ g)
instance : Module.Finite ℤ (Lat ρ g) := Module.Finite.of_basis (basis ρ g)
def form (S : Matrix (Fin r) (Fin r) ℤ) : LinearMap.BilinForm ℤ (Lat ρ g) :=
  LinearMap.mk₂ ℤ (fun x y => ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1))
    (fun x y z => by
      simp only [add_apply, Prod.fst_add, Prod.snd_add, add_dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun n x y => by
      simp only [zsmul_apply, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y z => by
      simp only [add_apply, Prod.fst_add, Prod.snd_add, dotProduct_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun n x y => by
      simp only [zsmul_apply, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
def cx : Lat ρ g →ₗ[ℤ] Lat ρ g where
  toFun x := fun i => ((x i).2, -(x i).1)
  map_add' x y := by
    funext i
    refine Prod.ext (funext fun k => rfl) (funext fun k => ?_)
    show -((x i).1 k + (y i).1 k) = -(x i).1 k + -(y i).1 k
    ring
  map_smul' n x := by
    funext i
    refine Prod.ext (funext fun k => rfl) (funext fun k => ?_)
    show -(n * (x i).1 k) = n * -(x i).1 k
    ring
def act (a : 𝓞 E) : Lat ρ g →ₗ[ℤ] Lat ρ g := (DistribMulAction.toAddMonoidHom (Lat ρ g) a).toIntLinearMap
end GlobalTheory.UnitaryStd


