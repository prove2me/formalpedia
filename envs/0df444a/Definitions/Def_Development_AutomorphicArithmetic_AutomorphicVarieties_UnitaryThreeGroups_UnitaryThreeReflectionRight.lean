-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:19.402593+00:00
-- url     : https://prove2.me/theorems/2d3c76d9-0bfb-499b-8763-9d71fecc87da
-- title:
--   Unitary Three Reflection Right
-- statement:
--   Definitions and structural lemmas for Unitary Three Reflection Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/UnitaryThreeReflectionRight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory.V.U3
open Matrix
section Group
variable {n : Type} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S]
def trInv (g : GL n R) : GL n R where
  val := ((g⁻¹ : GL n R) : Matrix n n R)ᵀ
  inv := (g : Matrix n n R)ᵀ
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp
@[simp] theorem trInv_val (g : GL n R) :
    (trInv g : Matrix n n R) = ((g⁻¹ : GL n R) : Matrix n n R)ᵀ := rfl
@[simp] theorem trInv_inv_val (g : GL n R) :
    (((trInv g)⁻¹ : GL n R) : Matrix n n R) = (g : Matrix n n R)ᵀ := rfl
theorem trInv_trInv (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  rw [trInv_val, trInv_inv_val, Matrix.transpose_transpose]
theorem trInv_mul (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  simp only [trInv_val, Units.val_mul, _root_.mul_inv_rev, Matrix.transpose_mul]
theorem map_trInv (f : R →+* S) (g : GL n R) :
    GeneralLinearGroup.map f (trInv g) = trInv (GeneralLinearGroup.map f g) := by
  apply Units.ext
  simp [GeneralLinearGroup.map, Matrix.transpose_map]
end Group
section Twisted
variable {m : ℕ} {R S : Type*} [CommRing R] [CommRing S]
variable (R) in

def Jmat (m : ℕ) : Matrix (Fin m) (Fin m) R := fun i j => if j = i.rev then 1 else 0
theorem Jmat_mul_Jmat (m : ℕ) : Jmat R m * Jmat R m = 1 := by
  ext i j
  simp only [Jmat, Matrix.mul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i.rev]
  · simp [eq_comm, Fin.rev_eq_iff]
  · intro k _ hk
    simp [hk]
  · simp
theorem Jmat_transpose (m : ℕ) : (Jmat R m)ᵀ = Jmat R m := by
  ext i j
  simp only [Jmat, Matrix.transpose_apply]
  congr 1
  exact propext ⟨fun h => by simp [h], fun h => by simp [h]⟩
theorem Jmat_map (f : R →+* S) (m : ℕ) : (Jmat R m).map f = Jmat S m := by
  ext i j
  simp only [Jmat, Matrix.map_apply]
  split_ifs <;> simp
variable (R) in

def Jgl (m : ℕ) : GL (Fin m) R := ⟨Jmat R m, Jmat R m, Jmat_mul_Jmat m, Jmat_mul_Jmat m⟩
theorem Jgl_mul_Jgl : Jgl R m * Jgl R m = 1 := Units.ext (Jmat_mul_Jmat m)
theorem trInv_Jgl : trInv (Jgl R m) = Jgl R m := Units.ext (Jmat_transpose m)
def theta (g : GL (Fin m) R) : GL (Fin m) R := Jgl R m * trInv g * Jgl R m
theorem theta_val (g : GL (Fin m) R) : (theta g : Matrix (Fin m) (Fin m) R) =
    Jmat R m * ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m := rfl
theorem theta_inv_val (g : GL (Fin m) R) :
    (((theta g)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
      Jmat R m * (g : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m := by
  rw [Matrix.mul_assoc]; rfl
theorem theta_theta (g : GL (Fin m) R) : theta (theta g) = g := by
  have hJ : ∀ x : GL (Fin m) R, Jgl R m * (Jgl R m * x) = x := fun x => by
    rw [← mul_assoc, Jgl_mul_Jgl, one_mul]
  simp only [theta, trInv_mul, trInv_Jgl, trInv_trInv, mul_assoc, Jgl_mul_Jgl, mul_one, hJ]
theorem theta_mul (g h : GL (Fin m) R) : theta (g * h) = theta g * theta h := by
  have hJ : ∀ x : GL (Fin m) R, Jgl R m * (Jgl R m * x) = x := fun x => by
    rw [← mul_assoc, Jgl_mul_Jgl, one_mul]
  simp only [theta, trInv_mul, mul_assoc, hJ]
variable (m R) in

def thetaAut : MulAut (GL (Fin m) R) where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul
variable (m R) in

def sgnAct : ℤˣ →* MulAut (GL (Fin m) R) where
  toFun s := if s = 1 then 1 else thetaAut m R
  map_one' := if_pos rfl
  map_mul' s t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
    · simp
    · simp
    · simp
    · have h : ((-1 : ℤˣ) = 1) = False := by decide
      simp only [neg_mul_neg, mul_one, if_true, h, if_false]
      ext1 g
      exact (theta_theta g).symm
@[simp] theorem sgnAct_one (g : GL (Fin m) R) : sgnAct m R 1 g = g := by simp
@[simp] theorem sgnAct_neg_one (g : GL (Fin m) R) : sgnAct m R (-1) g = theta g := by
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  show (if (-1 : ℤˣ) = 1 then 1 else thetaAut m R) g = theta g
  simp only [h, if_false]
  rfl
variable (m R) in

abbrev GG : Type _ := GL (Fin m) R ⋊[sgnAct m R] ℤˣ
def GG.mat (x : GG m R) : Matrix (Fin m) (Fin m) R := (x.left : Matrix (Fin m) (Fin m) R)
abbrev GG.ofGL : GL (Fin m) R →* GG m R := SemidirectProduct.inl
abbrev GG.nu : GG m R →* ℤˣ := SemidirectProduct.rightHom
theorem map_Jgl (f : R →+* S) : GeneralLinearGroup.map f (Jgl R m) = Jgl S m :=
  Units.ext (Jmat_map f m)
theorem map_theta (f : R →+* S) (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (theta g) = theta (GeneralLinearGroup.map f g) := by
  simp only [theta, map_mul, map_trInv, map_Jgl]
def GG.map (f : R →+* S) : GG m R →* GG m S :=
  SemidirectProduct.map (GeneralLinearGroup.map f) (MonoidHom.id ℤˣ) (by
    intro s
    refine MonoidHom.ext fun g => ?_
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · simpa using map_theta f g)
@[simp] theorem GG.map_mat (f : R →+* S) (x : GG m R) : (GG.map f x).mat = x.mat.map f := rfl
@[simp] theorem GG.map_right (f : R →+* S) (x : GG m R) : (GG.map f x).right = x.right := rfl
def thetaLie (X : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  -(Jmat R m * Xᵀ * Jmat R m)
def GG.adFun (x : GG m R) (X : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  x.mat * (if x.right = 1 then X else thetaLie X) *
    ((x.left⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)
theorem jmat_mul_jmat_mul (Y : Matrix (Fin m) (Fin m) R) :
    Jmat R m * (Jmat R m * Y) = Y := by
  rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
theorem thetaLie_thetaLie (X : Matrix (Fin m) (Fin m) R) :
    thetaLie (thetaLie X) = X := by
  simp only [thetaLie, Matrix.transpose_neg, Matrix.transpose_mul, Jmat_transpose,
    Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
    jmat_mul_jmat_mul, Jmat_mul_Jmat, Matrix.mul_one]
theorem theta_conj_thetaLie_eq_thetaLie_conj (b : GL (Fin m) R) (X : Matrix (Fin m) (Fin m) R) :
    (theta b : Matrix (Fin m) (Fin m) R) * (thetaLie X *
        (((theta b)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) =
      thetaLie ((b : Matrix (Fin m) (Fin m) R) * (X * ((b⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R))) := by
  simp only [theta_val, theta_inv_val, thetaLie, Matrix.transpose_mul, Jmat_transpose,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, jmat_mul_jmat_mul]
theorem GG.adFun_mul (x y : GG m R) (X : Matrix (Fin m) (Fin m) R) :
    (x * y).adFun X = x.adFun (y.adFun X) := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  have hn : ((-1 : ℤˣ) = 1) = False := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp only [GG.adFun, GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      sgnAct_one, sgnAct_neg_one, hn, if_true, if_false, mul_one, one_mul, neg_mul_neg,
      Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]
  · rw [← theta_conj_thetaLie_eq_thetaLie_conj]
    simp only [Matrix.mul_assoc]
  · rw [← theta_conj_thetaLie_eq_thetaLie_conj, thetaLie_thetaLie]
    simp only [Matrix.mul_assoc]
variable (m R) in

def GG.ad : Representation R (GG m R) (Matrix (Fin m) (Fin m) R) where
  toFun x :=
    { toFun := x.adFun
      map_add' := fun X Y => by
        unfold GG.adFun thetaLie
        split_ifs <;> simp [Matrix.mul_add, Matrix.add_mul, add_comm]
      map_smul' := fun a X => by
        unfold GG.adFun thetaLie
        split_ifs <;> simp }
  map_one' := by
    ext1 X
    simp [GG.adFun, GG.mat]
  map_mul' x y := by
    ext1 X
    exact GG.adFun_mul x y X
@[simp] theorem GG.ad_apply (x : GG m R) (X : Matrix (Fin m) (Fin m) R) :
    GG.ad m R x X = x.adFun X := rfl
variable {G : Type*} [Group G]
def conjBy (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (GG.ofGL h)).toMonoidHom.comp r
def glPart (η : G →* ℤˣ) (r : G →* GG m R) (hr : ∀ g, (r g).right = η g) :
    η.ker →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g h := by
    have hg : (r g).right = 1 := (hr g).trans g.2
    simp [hg]
def adRep (r : G →* GG m R) : Representation R G (Matrix (Fin m) (Fin m) R) := (GG.ad m R).comp r
end Twisted
section Three
variable {R : Type*} [CommRing R]
def wt1 (i : Fin 3) : ℤ := 1 - (i : ℕ)
def wt (i j : Fin 3) : ℤ := wt1 i - wt1 j
def torGL (t : Rˣ) : GL (Fin 3) R where
  val := Matrix.diagonal fun i => ((t ^ wt1 i : Rˣ) : R)
  inv := Matrix.diagonal fun i => (((t ^ wt1 i)⁻¹ : Rˣ) : R)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.mul_inv]; exact Matrix.diagonal_one
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.inv_mul]; exact Matrix.diagonal_one
variable (R) in

def tor : Rˣ →* GL (Fin 3) R where
  toFun := torGL
  map_one' := by
    apply Units.ext
    simp [torGL]
  map_mul' s t := by
    apply Units.ext
    simp [torGL, mul_zpow, Matrix.diagonal_mul_diagonal]
theorem tor_val (t : Rˣ) : (tor R t : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun i => ((t ^ wt1 i : Rˣ) : R) := rfl
theorem theta_tor (t : Rˣ) : theta (tor R t) = tor R t := by
  apply Units.ext
  rw [theta_val, ← map_inv, tor_val, tor_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, wt1, Matrix.diagonal, Fin.rev]
variable (R) in

def gw (j : ℤ) : Submodule R (Matrix (Fin 3) (Fin 3) R) where
  carrier := {X | ∀ a b, wt a b ≠ j → X a b = 0}
  add_mem' := fun hX hY a b h => by simp [hX a b h, hY a b h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX a b h => by simp [hX a b h]
variable (R) in

def unitaryThreeTorusLieAlgebra : Submodule R (Matrix (Fin 3) (Fin 3) R) :=
  Submodule.span R {Matrix.diagonal fun i => ((wt1 i : ℤ) : R)}
variable {G : Type*} [Group G]
def gstar (c g : G) : G := c * g⁻¹ * c
def zmat (c g₁ : G) (r : G →* GG 3 R) : Matrix (Fin 3) (Fin 3) R :=
  (r g₁).mat - (r (gstar c g₁)).mat
structure Normalised (c g₁ : G) (r : G →* GG 3 R) : Prop where
  atc : (r c).mat = 1
  z12 : zmat c g₁ r 0 1 = 0
  z21 : zmat c g₁ r 1 0 = 0
def r0 (η : G →* ℤˣ) (Ψ : G →* Rˣ) : G →* GG 3 R where
  toFun g := ⟨tor R (Ψ g), η g⟩
  map_one' := by ext1 <;> simp
  map_mul' g h := by
    ext1
    · rcases Int.units_eq_one_or (η g) with hg | hg <;> simp [hg, theta_tor]
    · simp
end Three
end UpperTheory.V.U3


