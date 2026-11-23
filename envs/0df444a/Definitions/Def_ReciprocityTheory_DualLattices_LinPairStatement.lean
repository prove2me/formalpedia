-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
-- name    : ReciprocityTheory_DualLattices_LinPairStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:54.515736+00:00
-- url     : https://prove2.me/theorems/f4794ef8-4d1a-425c-8278-00a14405f4c9
-- title:
--   Lin Pair Statement
-- statement:
--   Definitions and structural lemmas for Lin Pair Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LinPairStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
structure OEnd (B : BX R₀) (O : LAlg R₀) where
  f : ∀ {R : LAlg R₀}, LHom O R → B.G R →+ B.G R
  nat : ∀ {R S : LAlg R₀} (s : LHom O R) (g : LHom R S) (x : B.G R),
    f (g.comp s) (B.map g x) = B.map g (f s x)
structure OAdj (B : BX R₀) (O : LAlg R₀) where
  a : OEnd B O
  ab : OEnd B O
  e : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R), B.P R (a.f s x) z ≃ B.P R x (ab.f s z)
  e_smul : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R) (l : (R : Type u)ˣ) (u : B.P R (a.f s x) z),
    e s x z (B.smul l u) = B.smul l (e s x z u)
  equiv_addFst : ∀ {R : LAlg R₀} (s : LHom O R) (x x' z : B.G R) (u : B.P R (a.f s x) z)
    (u' : B.P R (a.f s x') z),
    e s (x + x') z (B.tr1 (map_add (a.f s) x x').symm (B.add1 u u')) =
      B.add1 (e s x z u) (e s x' z u')
  equiv_addSnd : ∀ {R : LAlg R₀} (s : LHom O R) (x z z' : B.G R) (u : B.P R (a.f s x) z)
    (w : B.P R (a.f s x) z'),
    e s x (z + z') (B.add2 u w) =
      B.tr2 (map_add (ab.f s) z z').symm (B.add2 (e s x z u) (e s x z' w))
namespace DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
lemma ση_mem (r : (R : Type u)) : Dp.σ.1 r * Dp.η ∈ Dp.π.ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Dp.ker_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
def ηmap : (R : Type u) →ₗ[R₀] Dp.π.ker where
  toFun r := ⟨Dp.σ.1 r * Dp.η, Dp.ση_mem r⟩
  map_add' r r' := Subtype.ext (by simp [add_mul])
  map_smul' c r := Subtype.ext (by simp [Algebra.smul_def, mul_assoc])
end DualPair
def hext (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) : B.gg ⊗[R₀] (R : Type u) →ₗ[R₀] (R : Type u) :=
  LinearMap.mul' R₀ (R : Type u) ∘ₗ TensorProduct.map h LinearMap.id
def LinPairStatement (B : BX R₀) (O : LAlg R₀) : Prop :=
  ∀ (A : OAdj B O) (R : LAlg R₀) (s : LHom O R) (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ),
    N • x = 0 → N • z = 0 →
    (B.IsPairing N (A.a.f s x) z w ↔ B.IsPairing N x (A.ab.f s z) w)
def LinHtStatement (B : BX R₀) (O : LAlg R₀) : Prop :=
  ∀ (A : OAdj B O) (R : LAlg R₀) (s : LHom O R) (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)),
    N • y = 0 → B.IsHeight Dp N y h →
    (∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) →
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ)
def OEnd.idE (B : BX R₀) (O : LAlg R₀) : OEnd B O where
  f _ := AddMonoidHom.id _
  nat _ _ _ := rfl
def OAdj.idA (B : BX R₀) (O : LAlg R₀) : OAdj B O where
  a := OEnd.idE B O
  ab := OEnd.idE B O
  e _ _ _ := Equiv.refl _
  e_smul _ _ _ _ _ := rfl
  equiv_addFst _ _ _ _ _ _ := rfl
  equiv_addSnd _ _ _ _ _ _ := rfl
end ReciprocityTheory.PGsh


