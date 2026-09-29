-- Prove2me | solution 1 for Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1266ba35-3494-566a-8333-891b3344cfae

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v w

noncomputable section

namespace HochschildSplitSol

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

structure Cocycle (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] where

  ψ : S →ₗ[R] S →ₗ[R] M
  symm : ∀ x y, ψ x y = ψ y x
  one : ∀ y, ψ 1 y = 0
  coc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0

structure Ext (c : Cocycle R S M) where

  fst : S

  snd : M

namespace Ext

variable (c : Cocycle R S M)

@[scoped ext] theorem ext {a b : Ext c} (h1 : a.fst = b.fst) (h2 : a.snd = b.snd) : a = b := by
  cases a; cases b; congr

def equiv : Ext c ≃ S × M where
  toFun a := (a.fst, a.snd)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

scoped instance : AddCommGroup (Ext c) := (equiv c).addCommGroup

scoped instance instModule : Module R (Ext c) := (equiv c).module R

@[scoped simp] theorem fst_add (a b : Ext c) : (a + b).fst = a.fst + b.fst := rfl
@[scoped simp] theorem snd_add (a b : Ext c) : (a + b).snd = a.snd + b.snd := rfl
@[scoped simp] theorem fst_zero : (0 : Ext c).fst = 0 := rfl
@[scoped simp] theorem snd_zero : (0 : Ext c).snd = 0 := rfl
@[scoped simp] theorem fst_neg (a : Ext c) : (-a).fst = -a.fst := rfl
@[scoped simp] theorem snd_neg (a : Ext c) : (-a).snd = -a.snd := rfl
@[scoped simp] theorem fst_smul (r : R) (a : Ext c) : (r • a).fst = r • a.fst := rfl
@[scoped simp] theorem snd_smul (r : R) (a : Ext c) : (r • a).snd = r • a.snd := rfl
@[scoped simp] theorem fst_mk (x : S) (u : M) : (Ext.mk x u : Ext c).fst = x := rfl
@[scoped simp] theorem snd_mk (x : S) (u : M) : (Ext.mk x u : Ext c).snd = u := rfl

scoped instance : Mul (Ext c) :=
  ⟨fun a b => ⟨a.fst * b.fst, a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst⟩⟩

scoped instance : One (Ext c) := ⟨⟨1, 0⟩⟩

@[scoped simp] theorem fst_mul (a b : Ext c) : (a * b).fst = a.fst * b.fst := rfl
@[scoped simp] theorem snd_mul (a b : Ext c) :
    (a * b).snd = a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst := rfl
@[scoped simp] theorem fst_one : (1 : Ext c).fst = 1 := rfl
@[scoped simp] theorem snd_one : (1 : Ext c).snd = 0 := rfl

theorem mul_comm' (a b : Ext c) : a * b = b * a := by
  ext
  · simp only [fst_mul, mul_comm]
  · simp only [snd_mul, c.symm a.fst b.fst]
    abel

theorem mul_assoc' (a b d : Ext c) : a * b * d = a * (b * d) := by
  ext
  · simp only [fst_mul, mul_assoc]
  · simp only [snd_mul, fst_mul, smul_add]
    rw [← sub_eq_zero]
    have h := c.coc a.fst b.fst d.fst
    calc _ = -(a.fst • c.ψ b.fst d.fst - c.ψ (a.fst * b.fst) d.fst +
          c.ψ a.fst (b.fst * d.fst) - d.fst • c.ψ a.fst b.fst) := by
          simp only [smul_smul]
          module
      _ = 0 := by rw [h, neg_zero]

theorem one_mul' (a : Ext c) : 1 * a = a := by
  ext
  · simp only [fst_mul, fst_one, one_mul]
  · simp only [snd_mul, fst_one, snd_one, one_smul, smul_zero, add_zero, c.one]

scoped instance instCommRing : CommRing (Ext c) where
  __ := (inferInstance : AddCommGroup (Ext c))
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc' c
  one_mul := one_mul' c
  mul_one a := by rw [mul_comm']; exact one_mul' c a
  zero_mul a := by
    ext
    · simp only [fst_mul, fst_zero, zero_mul]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero,
        LinearMap.zero_apply, add_zero]
  mul_zero a := by
    ext
    · simp only [fst_mul, fst_zero, mul_zero]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero, add_zero]
  left_distrib a b d := by
    ext
    · simp only [fst_mul, fst_add, mul_add]
    · simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add]
      abel
  right_distrib a b d := by
    ext
    · simp only [fst_mul, fst_add, add_mul]
    · simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add, LinearMap.add_apply]
      abel
  mul_comm := mul_comm' c

theorem smul_mul_assoc' (r : R) (a b : Ext c) : (r • a) * b = r • (a * b) := by
  ext
  · simp only [fst_mul, fst_smul, smul_mul_assoc]
  · simp only [snd_mul, fst_smul, snd_smul, smul_add, LinearMap.map_smul₂, smul_assoc]
    rw [smul_comm b.fst r a.snd]

scoped instance instAlgebra : Algebra R (Ext c) :=
  Algebra.ofModule (smul_mul_assoc' c) fun r a b => by
    rw [mul_comm', smul_mul_assoc', mul_comm']

def fstHom : Ext c →ₐ[R] S where
  toFun := Ext.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, fst_smul, fst_one, Algebra.algebraMap_eq_smul_one]

theorem fstHom_apply (a : Ext c) : fstHom c a = a.fst := rfl

theorem fstHom_surjective : Function.Surjective (fstHom c) := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem fst_eq_zero_of_mem_ker {a : Ext c} (ha : a ∈ RingHom.ker (fstHom c : Ext c →+* S)) :
    a.fst = 0 := ha

theorem ker_sq_eq_bot : RingHom.ker (fstHom c : Ext c →+* S) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have ha' := fst_eq_zero_of_mem_ker c ha
  have hb' := fst_eq_zero_of_mem_ker c hb
  ext
  · simp only [fst_mul, ha', zero_mul, fst_zero]
  · simp only [snd_mul, ha', hb', zero_smul, map_zero, add_zero, snd_zero]

theorem isNilpotent_ker : IsNilpotent (RingHom.ker (fstHom c : Ext c →+* S)) :=
  ⟨2, ker_sq_eq_bot c⟩

variable [Algebra.FormallySmooth R S]

def sect : S →ₐ[R] Ext c :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) (fstHom c) (fstHom_surjective c)
    (isNilpotent_ker c)

theorem fst_sect (x : S) : (sect c x).fst = x := by
  have h := Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R S) (fstHom c)
    (fstHom_surjective c) (isNilpotent_ker c) x
  exact h

def ell : S →ₗ[R] M where
  toFun x := (sect c x).snd
  map_add' x y := by rw [map_add, snd_add]
  map_smul' r x := by rw [map_smul, snd_smul, RingHom.id_apply]

theorem ell_apply (x : S) : ell c x = (sect c x).snd := rfl

theorem ell_one : ell c 1 = 0 := by rw [ell_apply, map_one, snd_one]

theorem ψ_eq (x y : S) : c.ψ x y = ell c (x * y) - x • ell c y - y • ell c x := by
  have h := congrArg Ext.snd (map_mul (sect c) x y)
  rw [snd_mul, fst_sect, fst_sect] at h
  rw [ell_apply, ell_apply, ell_apply, h]
  abel

end Ext
p2m_reactivate "P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.HochschildSplitSol.Ext"

end HochschildSplitSol
p2m_reactivate "P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.HochschildSplitSol.Ext P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.HochschildSplitSol"

end
p2m_reactivate "P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.HochschildSplitSol.Ext P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.HochschildSplitSol"

open HochschildSplitSol in
theorem solution
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (ψ : S →ₗ[R] S →ₗ[R] M)
    (hsymm : ∀ x y, ψ x y = ψ y x)
    (hone : ∀ y, ψ 1 y = 0)
    (hcoc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0) :
    ∃ l : S →ₗ[R] M, l 1 = 0 ∧ ∀ x y, ψ x y = l (x * y) - x • l y - y • l x :=
  let c : Cocycle R S M := ⟨ψ, hsymm, hone, hcoc⟩
  ⟨Ext.ell c, Ext.ell_one c, Ext.ψ_eq c⟩

end S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
end P2MW
export P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle (solution)
