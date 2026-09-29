-- Prove2me | solution 1 for AlgebraicCurve.exists_bounded_two_cochain_of_local_coboundaries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/fd345c81-31e0-5241-bead-b3b6edc1440e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

universe u

noncomputable section

namespace PatchSol

section TableAlgebra

structure Table (R : Type*) [CommRing R] (N : ℕ) where

  γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R
  unit : ∀ j k, γ 0 j k = if j = k then 1 else 0
  comm : ∀ i j k, γ i j k = γ j i k
  assoc : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m

variable {R : Type*} [CommRing R] {N : ℕ}

def cst (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R) :
    Fin (N + 1) → R :=
  fun m => ∑ i, ∑ j, x i * y j * γ i j m

theorem cst_apply (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R)
    (m : Fin (N + 1)) : cst γ x y m = ∑ i, ∑ j, x i * y j * γ i j m := rfl

theorem sum3_rot (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ t, ∑ q, f q l t := by
  calc ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ q, ∑ t, f q l t := Finset.sum_comm
    _ = ∑ l, ∑ t, ∑ q, f q l t := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem sum4_rot (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l := by
  calc ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ q, ∑ k, ∑ t, ∑ l, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ k, ∑ l, ∑ t, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ q, ∑ l, ∑ t, f q t k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ q, ∑ t, f q t k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem cst_cst_left (γo γi : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γo (cst γi a b) c s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γi k l q * γo q t s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_rot]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_cst_right (γo γi : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γo a (cst γi b c) s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γi l t q * γo k q s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_comm_of (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (hc : ∀ i j k, γ i j k = γ j i k) (a b : Fin (N + 1) → R) : cst γ a b = cst γ b a := by
  funext m
  rw [cst_apply, cst_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hc j i m]; ring

theorem cst_add_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (a a' b : Fin (N + 1) → R) :
    cst γ (a + a') b = cst γ a b + cst γ a' b := by
  funext m
  simp only [cst, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem cst_add_right (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (a b b' : Fin (N + 1) → R) :
    cst γ a (b + b') = cst γ a b + cst γ a b' := by
  funext m
  simp only [cst, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cst_smul_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (z : R)
    (a b : Fin (N + 1) → R) : cst γ (z • a) b = z • cst γ a b := by
  funext m
  simp only [cst, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem cst_zero_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (b : Fin (N + 1) → R) :
    cst γ 0 b = 0 := by
  funext m; simp [cst]

theorem cst_unit_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (h1 : ∀ j k, γ 0 j k = if j = k then 1 else 0) (b : Fin (N + 1) → R) :
    cst γ (Pi.single 0 1) b = b := by
  funext m
  rw [cst_apply, Finset.sum_eq_single 0]
  · simp only [Pi.single_eq_same, one_mul, h1]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ m) h
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin (N + 1))) h

structure TAlg (T : Table R N) where

  coord : Fin (N + 1) → R

namespace TAlg

variable (T : Table R N)

@[scoped ext] theorem ext {x y : TAlg T} (h : x.coord = y.coord) : x = y := by
  cases x; cases y; congr

def equiv : TAlg T ≃ (Fin (N + 1) → R) where
  toFun := coord
  invFun := TAlg.mk
  left_inv _ := rfl
  right_inv _ := rfl

scoped instance : AddCommGroup (TAlg T) := (equiv T).addCommGroup

@[scoped simp] theorem coord_add (x y : TAlg T) : (x + y).coord = x.coord + y.coord := rfl
@[scoped simp] theorem coord_zero : (0 : TAlg T).coord = 0 := rfl
@[scoped simp] theorem coord_neg (x : TAlg T) : (-x).coord = -x.coord := rfl
@[scoped simp] theorem coord_sub (x y : TAlg T) : (x - y).coord = x.coord - y.coord := rfl
@[scoped simp] theorem coord_mk (v : Fin (N + 1) → R) : (TAlg.mk v : TAlg T).coord = v := rfl

scoped instance : Mul (TAlg T) := ⟨fun x y => TAlg.mk (cst T.γ x.coord y.coord)⟩

scoped instance : One (TAlg T) := ⟨TAlg.mk (Pi.single 0 1)⟩

@[scoped simp] theorem coord_mul (x y : TAlg T) : (x * y).coord = cst T.γ x.coord y.coord := rfl
@[scoped simp] theorem coord_one : (1 : TAlg T).coord = Pi.single 0 1 := rfl

theorem mul_comm' (x y : TAlg T) : x * y = y * x := by
  ext1; simp only [coord_mul]; exact cst_comm_of T.γ T.comm _ _

theorem mul_assoc' (x y z : TAlg T) : x * y * z = x * (y * z) := by
  ext1
  simp only [coord_mul]
  funext s
  rw [cst_cst_left, cst_cst_right]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => ?_
  rw [T.assoc k l t s]

theorem one_mul' (x : TAlg T) : 1 * x = x := by
  ext1; simp only [coord_mul, coord_one]; exact cst_unit_left T.γ T.unit _

scoped instance instCommRing : CommRing (TAlg T) where
  __ := (inferInstance : AddCommGroup (TAlg T))
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc' T
  one_mul := one_mul' T
  mul_one x := by rw [mul_comm']; exact one_mul' T x
  zero_mul x := by ext1; simp only [coord_mul, coord_zero]; exact cst_zero_left _ _
  mul_zero x := by rw [mul_comm']; ext1; simp only [coord_mul, coord_zero]; exact cst_zero_left _ _
  left_distrib x y z := by ext1; simp only [coord_mul, coord_add]; exact cst_add_right _ _ _ _
  right_distrib x y z := by ext1; simp only [coord_mul, coord_add]; exact cst_add_left _ _ _ _
  mul_comm := mul_comm' T

def e (i : Fin (N + 1)) : TAlg T := TAlg.mk (Pi.single i 1)

@[scoped simp] theorem coord_e (i : Fin (N + 1)) : (e T i).coord = Pi.single i 1 := rfl

end TAlg
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg"

def D1 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) : R :=
  (∑ k, lam j k * γ i k m) - (∑ k, γ i j k * lam k m) + (∑ k, lam i k * γ k j m)

def D2 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) : R :=
  (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) + (∑ k, γ j l k * φ i k m) -
    (∑ k, φ i j k * γ k l m)

section Semantics

variable (T : Table R N)

def L1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x : TAlg T) : TAlg T :=
  TAlg.mk fun m => ∑ i, x.coord i * lam i m

def L2 (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) : TAlg T :=
  TAlg.mk (cst φ x.coord y.coord)

def hd1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) : TAlg T :=
  x * L1 T lam y - L1 T lam (x * y) + L1 T lam x * y

def hd2 (Φ : TAlg T → TAlg T → TAlg T) (x y z : TAlg T) : TAlg T :=
  x * Φ y z - Φ (x * y) z + Φ x (y * z) - Φ x y * z

theorem coord_mul_L1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (x * L1 T lam y).coord m = ∑ i, ∑ j, x.coord i * y.coord j * ∑ q, lam j q * T.γ i q m := by
  rw [TAlg.coord_mul, cst_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [L1, TAlg.coord_mk, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem coord_L1_mul (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (L1 T lam (x * y)).coord m = ∑ i, ∑ j, x.coord i * y.coord j * ∑ q, T.γ i j q * lam q m := by
  simp only [L1, TAlg.coord_mk, TAlg.coord_mul, cst_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem sum3_rot' (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ j, ∑ i, f q j i = ∑ i, ∑ j, ∑ q, f q j i := by
  calc ∑ q, ∑ j, ∑ i, f q j i = ∑ j, ∑ q, ∑ i, f q j i := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ q, f q j i := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ q, f q j i := Finset.sum_comm

theorem coord_L1_mul' (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (L1 T lam x * y).coord m = ∑ i, ∑ j, x.coord i * y.coord j * ∑ q, lam i q * T.γ q j m := by
  rw [TAlg.coord_mul, cst_apply]
  simp only [L1, TAlg.coord_mk, Finset.sum_mul, Finset.mul_sum]
  rw [sum3_rot']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem coord_hd1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (hd1 T lam x y).coord m = ∑ i, ∑ j, x.coord i * y.coord j * D1 T.γ lam i j m := by
  simp only [hd1, TAlg.coord_add, TAlg.coord_sub, Pi.add_apply, Pi.sub_apply, coord_mul_L1,
    coord_L1_mul, coord_L1_mul', D1, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem coord_hd2 (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y z : TAlg T)
    (s : Fin (N + 1)) :
    (hd2 T (L2 T φ) x y z).coord s =
      ∑ k, ∑ l, ∑ t, x.coord k * y.coord l * z.coord t * D2 T.γ φ k l t s := by
  simp only [hd2, L2, TAlg.coord_add, TAlg.coord_sub, Pi.add_apply, Pi.sub_apply,
    TAlg.coord_mul, cst_cst_left, cst_cst_right, D2, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum3_single (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l : Fin (N + 1)) :
    ∑ k, ∑ q, ∑ t, (Pi.single i 1 : Fin (N + 1) → R) k * (Pi.single j 1 : Fin (N + 1) → R) q *
      (Pi.single l 1 : Fin (N + 1) → R) t * f k q t = f i j l := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Finset.sum_eq_single l]
  · simp
  · intro t _ ht; simp [Pi.single_eq_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ l) h
  · intro q _ hq; simp [Pi.single_eq_of_ne hq]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum2_single (f : Fin (N + 1) → Fin (N + 1) → R) (i j : Fin (N + 1)) :
    ∑ k, ∑ q, (Pi.single i 1 : Fin (N + 1) → R) k * (Pi.single j 1 : Fin (N + 1) → R) q * f k q =
      f i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro q _ hq; simp [Pi.single_eq_of_ne hq]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem L2_D1_eq_hd1 (lam : Fin (N + 1) → Fin (N + 1) → R) (y z : TAlg T) :
    L2 T (D1 T.γ lam) y z = hd1 T lam y z := by
  ext1
  funext m
  rw [coord_hd1]
  rfl

theorem hd2_hd1_eq_zero (lam : Fin (N + 1) → Fin (N + 1) → R) (x y z : TAlg T) :
    hd2 T (hd1 T lam) x y z = 0 := by
  simp only [hd2, hd1, mul_assoc]
  ring

theorem D2_D1 (lam : Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 T.γ (D1 T.γ lam) i j l m = 0 := by
  have h := coord_hd2 T (D1 T.γ lam) (TAlg.e T i) (TAlg.e T j) (TAlg.e T l) m
  rw [TAlg.coord_e, TAlg.coord_e, TAlg.coord_e, sum3_single] at h
  rw [← h]
  have hfun : L2 T (D1 T.γ lam) = hd1 T lam := by
    funext y z; exact L2_D1_eq_hd1 T lam y z
  rw [hfun, hd2_hd1_eq_zero, TAlg.coord_zero, Pi.zero_apply]

end Semantics
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg"

section Linear

variable (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)

theorem D2_add (φ φ' : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 γ (φ + φ') i j l m = D2 γ φ i j l m + D2 γ φ' i j l m := by
  simp only [D2, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring

theorem D2_smul (c : R) (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 γ (c • φ) i j l m = c * D2 γ φ i j l m := by
  simp only [D2, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_sub]
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_ <;>
    exact Finset.sum_congr rfl fun k _ => by ring

theorem D2_zero (i j l m : Fin (N + 1)) :
    D2 γ (0 : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) i j l m = 0 := by
  simp [D2]

theorem D2_sub (φ φ' : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 γ (φ - φ') i j l m = D2 γ φ i j l m - D2 γ φ' i j l m := by
  simp only [D2, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]; ring

theorem D1_add (lam lam' : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (lam + lam') i j m = D1 γ lam i j m + D1 γ lam' i j m := by
  simp only [D1, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring

theorem D1_smul (c : R) (lam : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (c • lam) i j m = c * D1 γ lam i j m := by
  simp only [D1, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_sub]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact Finset.sum_congr rfl fun k _ => by ring

theorem D1_symm (hγc : ∀ i j k, γ i j k = γ j i k) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) : D1 γ lam i j m = D1 γ lam j i m := by
  simp only [D1]
  have h1 : ∑ k, lam j k * γ i k m = ∑ k, lam j k * γ k i m :=
    Finset.sum_congr rfl fun k _ => by rw [hγc i k m]
  have h2 : ∑ k, γ i j k * lam k m = ∑ k, γ j i k * lam k m :=
    Finset.sum_congr rfl fun k _ => by rw [hγc i j k]
  have h3 : ∑ k, lam i k * γ k j m = ∑ k, lam i k * γ j k m :=
    Finset.sum_congr rfl fun k _ => by rw [hγc k j m]
  rw [h1, h2, h3]; ring

theorem D1_norm (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (lam : Fin (N + 1) → Fin (N + 1) → R) (hlam : ∀ m, lam 0 m = 0) (j m : Fin (N + 1)) :
    D1 γ lam 0 j m = 0 := by
  simp only [D1, hlam, zero_mul, Finset.sum_const_zero, add_zero, hγ1]
  rw [Finset.sum_eq_single m, Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ m) h

end Linear
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg"

end TableAlgebra
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg"

section Degrees

variable {K : Type u} [Field K] {n : ℕ} (d : Fin (n + 1) → ℕ)
  (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
  (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
  (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
  (hγc : ∀ i j k, γ i j k = γ j i k)
  (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)

include hd0 hd in
theorem d_le_two (m : Fin (n + 1)) : d m ≤ 2 := by
  by_cases hm : m = 0
  · rw [hm, hd0]; exact Nat.zero_le _
  · rcases hd m hm with h | h <;> omega

include hd in
theorem one_le_d (m : Fin (n + 1)) (hm : m ≠ 0) : 1 ≤ d m := by
  rcases hd m hm with h | h <;> omega

include hγ1 hγc in
theorem natDegree_γ_zero_right (i m : Fin (n + 1)) : (γ i 0 m).natDegree = 0 := by
  rw [hγc, hγ1]; split_ifs <;> simp

include hd0 hd hγ1 hγc hγd in

theorem natDegree_D1_le (E : ℕ) (r : Fin (n + 1) → Fin (n + 1) → K[X]) (hr0 : ∀ m, r 0 m = 0)
    (hr : ∀ i m, r i m = 0 ∨ (r i m).natDegree + 1 ≤ E) (i j m : Fin (n + 1)) (hi : i ≠ 0)
    (hj : j ≠ 0) : (D1 γ r i j m).natDegree ≤ E + d i + d j - d m := by
  have hdm := d_le_two d hd0 hd m
  have hdi := one_le_d d hd i hi
  have hdj := one_le_d d hd j hj
  have hdi2 := d_le_two d hd0 hd i
  have hdj2 := d_le_two d hd0 hd j
  simp only [D1]
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    rcases hr j k with h | h
    · rw [h, zero_mul, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    by_cases hk : k = 0
    · subst hk; rw [natDegree_γ_zero_right γ hγ1 hγc]; omega
    · have := hγd i k m hi hk
      have hdk := d_le_two d hd0 hd k
      omega
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    by_cases hk : k = 0
    · subst hk; rw [hr0, mul_zero, natDegree_zero]; exact Nat.zero_le _
    rcases hr k m with h | h
    · rw [h, mul_zero, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    have := hγd i j k hi hj
    have hdk := one_le_d d hd k hk
    omega
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    rcases hr i k with h | h
    · rw [h, zero_mul, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    by_cases hk : k = 0
    · subst hk
      have h0 : (γ 0 j m).natDegree = 0 := by rw [hγ1]; split_ifs <;> simp
      rw [h0]
      omega
    · have := hγd k j m hk hj
      have hdk := d_le_two d hd0 hd k
      omega

end Degrees
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg"

section Main

variable {K : Type u} [Field K] {n : ℕ}

def multIdeal (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X]) : Ideal K[X] where
  carrier := {s | ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
    (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧ ∀ i j l m, D2 γ φ i j l m = s * a i j l m}
  zero_mem' := ⟨0, fun _ _ => rfl, fun _ _ _ => rfl, fun i j l m => by rw [D2_zero, zero_mul]⟩
  add_mem' := by
    rintro s s' ⟨φ, h1, h2, h3⟩ ⟨φ', h1', h2', h3'⟩
    refine ⟨φ + φ', fun j k => by simp [h1, h1'], fun i j k => by
      simp only [Pi.add_apply, h2 i j k, h2' i j k], fun i j l m => ?_⟩
    rw [D2_add, h3, h3', add_mul]
  smul_mem' := by
    rintro c s ⟨φ, h1, h2, h3⟩
    refine ⟨c • φ, fun j k => by simp [h1], fun i j k => by
      simp only [Pi.smul_apply, h2 i j k], fun i j l m => ?_⟩
    rw [D2_smul, h3, smul_eq_mul, mul_assoc]

theorem mem_multIdeal (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X]) (s : K[X]) :
    s ∈ multIdeal γ a ↔ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, D2 γ φ i j l m = s * a i j l m :=
  Iff.rfl

theorem main (d : Fin (n + 1) → ℕ)
    (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧ s ∈ multIdeal γ a)
    (t : K[X]) (ht : t ≠ 0) (φi : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hφi1 : ∀ j k, φi 0 j k = 0) (hφic : ∀ i j k, φi i j k = φi j i k)
    (hφid : ∀ i j k, i ≠ 0 → j ≠ 0 → (φi i j k).natDegree ≤ t.natDegree + d i + d j - d k)
    (hφia : ∀ i j l m, D2 γ φi i j l m = t * a i j l m)
    (hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) → (∀ i j l m, D2 γ ψ i j l m = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m = D1 γ lam i j m) :
    ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ d i + d j - d k) ∧
      ∀ i j l m, D2 γ φ i j l m = a i j l m := by
  let T : Table K[X] n := ⟨γ, hγ1, hγc, hγa⟩

  have htop : multIdeal γ a = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsP, hs⟩ := hloc P hP
    exact hsP (hle hs)
  have h1 : (1 : K[X]) ∈ multIdeal γ a := by rw [htop]; exact Submodule.mem_top
  obtain ⟨φ₀, hφ₀1, hφ₀c, hφ₀a⟩ := (mem_multIdeal γ a 1).1 h1
  simp only [one_mul] at hφ₀a

  let ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := t • φ₀ - φi
  have hψ1 : ∀ j k, ψ 0 j k = 0 := fun j k => by simp [ψ, hφ₀1, hφi1]
  have hψc : ∀ i j k, ψ i j k = ψ j i k := fun i j k => by
    simp only [ψ, Pi.sub_apply, Pi.smul_apply, hφ₀c i j k, hφic i j k]
  have hψa : ∀ i j l m, D2 γ ψ i j l m = 0 := fun i j l m => by
    change D2 γ (t • φ₀ - φi) i j l m = 0
    rw [D2_sub, D2_smul, hφ₀a, hφia, sub_self]

  obtain ⟨u, hu, lam, hlam0, hlam⟩ := hgen ψ hψ1 hψc hψa
  have hut : u * t ≠ 0 := mul_ne_zero hu ht

  let q : Fin (n + 1) → Fin (n + 1) → K[X] := fun i m => lam i m / (u * t)
  let r : Fin (n + 1) → Fin (n + 1) → K[X] := fun i m => lam i m % (u * t)
  have hqr : ∀ i m, lam i m = (u * t) * q i m + r i m := fun i m =>
    (EuclideanDomain.div_add_mod (lam i m) (u * t)).symm
  have hq0 : ∀ m, q 0 m = 0 := fun m => by simp [q, hlam0]
  have hr0 : ∀ m, r 0 m = 0 := fun m => by simp [r, hlam0]
  have hrdeg : ∀ i m, r i m = 0 ∨ (r i m).natDegree + 1 ≤ (u * t).natDegree := by
    intro i m
    by_cases h : r i m = 0
    · exact Or.inl h
    · right
      have hlt : (r i m).degree < (u * t).degree := EuclideanDomain.mod_lt (lam i m) hut
      have := Polynomial.natDegree_lt_natDegree h hlt
      omega

  let φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => φ₀ i j k - D1 γ q i j k
  have hlamq : lam = (u * t) • q + r := by
    funext i m; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hqr i m

  have hkey : ∀ i j k, (u * t) * φ i j k = u * φi i j k + D1 γ r i j k := by
    intro i j k
    have e1 : u * ψ i j k = D1 γ lam i j k := hlam i j k
    have e2 : D1 γ lam i j k = (u * t) * D1 γ q i j k + D1 γ r i j k := by
      rw [hlamq, D1_add, D1_smul]
    have e3 : u * ψ i j k = u * (t * φ₀ i j k) - u * φi i j k := by
      simp only [ψ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    change (u * t) * (φ₀ i j k - D1 γ q i j k) = u * φi i j k + D1 γ r i j k
    have : (u * t) * φ₀ i j k = u * φi i j k + (u * t) * D1 γ q i j k + D1 γ r i j k := by
      linear_combination e1 + e2 - e3
    rw [mul_sub, this]; ring
  refine ⟨φ, fun j k => ?_, fun i j k => ?_, fun i j k hi hj => ?_, fun i j l m => ?_⟩
  · change φ₀ 0 j k - D1 γ q 0 j k = 0
    rw [hφ₀1, D1_norm γ hγ1 q hq0, sub_zero]
  · change φ₀ i j k - D1 γ q i j k = φ₀ j i k - D1 γ q j i k
    rw [hφ₀c i j k, D1_symm γ hγc q i j k]
  ·
    have hR : ((u * t) * φ i j k).natDegree ≤ (u * t).natDegree + (d i + d j - d k) := by
      rw [hkey]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans ?_
        have := hφid i j k hi hj
        rw [natDegree_mul hu ht]
        omega
      · have := natDegree_D1_le d hd0 hd γ hγ1 hγc hγd (u * t).natDegree r hr0 hrdeg i j k hi hj
        omega
    by_cases hφ0 : φ i j k = 0
    · rw [hφ0, natDegree_zero]; exact Nat.zero_le _
    · rw [natDegree_mul hut hφ0] at hR
      omega
  · change D2 γ (fun i j k => φ₀ i j k - D1 γ q i j k) i j l m = a i j l m
    have : (fun i j k => φ₀ i j k - D1 γ q i j k) = φ₀ - D1 γ q := by
      funext i j k; rfl
    rw [this, D2_sub, hφ₀a, D2_D1 T q, sub_zero]

end Main
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg"

end PatchSol
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol.TAlg P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.PatchSol"

open PatchSol in
theorem solution
    (K : Type u) [Field K] (n : ℕ) (d : Fin (n + 1) → ℕ)
    (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
          (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = s * a i j l m)
    (hinfty : ∃ t : K[X], t ≠ 0 ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
        ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
          (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = t * a i j l m)
    (hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) →
      (∀ i j l m, (∑ k, ψ j l k * γ i k m) - (∑ k, γ i j k * ψ k l m) +
          (∑ k, γ j l k * ψ i k m) - (∑ k, ψ i j k * γ k l m) = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m =
          (∑ k, lam j k * γ i k m) - (∑ k, γ i j k * lam k m) + (∑ k, lam i k * γ k j m)) :
    ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ d i + d j - d k) ∧
      ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
        (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = a i j l m := by
  obtain ⟨t, ht, φi, hφi1, hφic, hφid, hφia⟩ := hinfty
  have hloc' : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧ s ∈ multIdeal γ a := by
    intro P hP
    obtain ⟨s, hs, φ, h1, h2, h3⟩ := hloc P hP
    exact ⟨s, hs, φ, h1, h2, h3⟩
  exact main d hd0 hd γ hγ1 hγc hγa hγd a hloc' t ht φi hφi1 hφic hφid hφia hgen

end S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries
end P2MW
export P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries (solution)
