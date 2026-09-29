-- Prove2me | solution 1 for AlgebraicCurve.exists_wittVector_lift_of_normalFormOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/afb7eaae-4b67-5027-9817-3ac8de3a5a62

import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

universe u v

noncomputable section

namespace WittLiftNF

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

theorem cst_cst_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γ (cst γ a b) c s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γ k l q * γ q t s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_rot]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_cst_right (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γ a (cst γ b c) s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γ l t q * γ k q s := by
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

theorem cst_single_single (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j : Fin (N + 1)) :
    cst γ (Pi.single i 1) (Pi.single j 1) = fun m => γ i j m := by
  funext m
  rw [cst_apply, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

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

scoped instance instModule : Module R (TAlg T) := (equiv T).module R

@[scoped simp] theorem coord_add (x y : TAlg T) : (x + y).coord = x.coord + y.coord := rfl
@[scoped simp] theorem coord_zero : (0 : TAlg T).coord = 0 := rfl
@[scoped simp] theorem coord_neg (x : TAlg T) : (-x).coord = -x.coord := rfl
@[scoped simp] theorem coord_sub (x y : TAlg T) : (x - y).coord = x.coord - y.coord := rfl
@[scoped simp] theorem coord_smul (z : R) (x : TAlg T) : (z • x).coord = z • x.coord := rfl
@[scoped simp] theorem coord_mk (v : Fin (N + 1) → R) : (TAlg.mk v : TAlg T).coord = v := rfl

def linearEquiv : TAlg T ≃ₗ[R] (Fin (N + 1) → R) :=
  { equiv T with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[scoped simp] theorem linearEquiv_apply (x : TAlg T) : linearEquiv T x = x.coord := rfl
@[scoped simp] theorem linearEquiv_symm_apply (v : Fin (N + 1) → R) : (linearEquiv T).symm v = TAlg.mk v :=
  rfl

theorem coord_sum {ι : Type*} (s : Finset ι) (f : ι → TAlg T) :
    (∑ i ∈ s, f i).coord = ∑ i ∈ s, (f i).coord := by
  change linearEquiv T (∑ i ∈ s, f i) = ∑ i ∈ s, linearEquiv T (f i)
  exact map_sum _ _ _

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

theorem smul_mul_assoc' (z : R) (x y : TAlg T) : (z • x) * y = z • (x * y) := by
  ext1; simp only [coord_mul, coord_smul]; exact cst_smul_left _ _ _ _

scoped instance instAlgebra : Algebra R (TAlg T) :=
  Algebra.ofModule (smul_mul_assoc' T) fun z x y => by
    rw [mul_comm', smul_mul_assoc', mul_comm']

def basis : Module.Basis (Fin (N + 1)) R (TAlg T) := Module.Basis.ofEquivFun (linearEquiv T)

theorem basis_apply (i : Fin (N + 1)) : basis T i = TAlg.mk (Pi.single i 1) := by
  rw [basis, Module.Basis.coe_ofEquivFun]; rfl

theorem coord_basis (i : Fin (N + 1)) : (basis T i).coord = Pi.single i 1 := by
  rw [basis_apply]

theorem basis_repr_apply (x : TAlg T) (k : Fin (N + 1)) : (basis T).repr x k = x.coord k := by
  rw [basis, Module.Basis.ofEquivFun_repr_apply]; rfl

theorem basis_zero : basis T 0 = 1 := by
  ext1; rw [coord_basis, coord_one]

theorem basis_mul_basis_coord (i j : Fin (N + 1)) :
    (basis T i * basis T j).coord = fun m => T.γ i j m := by
  rw [coord_mul, coord_basis, coord_basis, cst_single_single]

theorem repr_basis_mul_basis (i j k : Fin (N + 1)) :
    (basis T).repr (basis T i * basis T j) k = T.γ i j k := by
  rw [basis_repr_apply, basis_mul_basis_coord]

theorem algebraMap_coord (f : R) : (algebraMap R (TAlg T) f).coord = Pi.single 0 f := by
  rw [Algebra.algebraMap_eq_smul_one, coord_smul, coord_one, ← Pi.single_smul, smul_eq_mul, mul_one]

theorem eq_sum_coord_smul_basis (x : TAlg T) : x = ∑ i, x.coord i • basis T i := by
  conv_lhs => rw [← (basis T).sum_repr x]
  simp only [basis_repr_apply]

end TAlg
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg"

section OfBasis

variable {C : Type*} [CommRing C] [Algebra R C] (e : Module.Basis (Fin (N + 1)) R C)

theorem repr_mul_unit (he : e 0 = 1) (j k : Fin (N + 1)) :
    e.repr (e 0 * e j) k = if j = k then 1 else 0 := by
  rw [he, one_mul, e.repr_self, Finsupp.single_apply]

theorem repr_mul_comm (i j k : Fin (N + 1)) : e.repr (e i * e j) k = e.repr (e j * e i) k := by
  rw [mul_comm]

theorem repr_mul_expand_left (i j l m : Fin (N + 1)) :
    e.repr (e i * e j * e l) m = ∑ k, e.repr (e i * e j) k * e.repr (e k * e l) m := by
  conv_lhs => rw [← e.sum_repr (e i * e j), Finset.sum_mul, map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mul_expand_right (i j l m : Fin (N + 1)) :
    e.repr (e i * (e j * e l)) m = ∑ k, e.repr (e j * e l) k * e.repr (e i * e k) m := by
  conv_lhs => rw [← e.sum_repr (e j * e l), Finset.mul_sum, map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mul_assoc (i j l m : Fin (N + 1)) :
    ∑ k, e.repr (e i * e j) k * e.repr (e k * e l) m =
      ∑ k, e.repr (e j * e l) k * e.repr (e i * e k) m := by
  rw [← repr_mul_expand_left, ← repr_mul_expand_right, mul_assoc]

def tableOfBasis (he : e 0 = 1) : Table R N where
  γ i j k := e.repr (e i * e j) k
  unit := repr_mul_unit e he
  comm := repr_mul_comm e
  assoc := repr_mul_assoc e

@[scoped simp] theorem tableOfBasis_γ (he : e 0 = 1) (i j k : Fin (N + 1)) :
    (tableOfBasis e he).γ i j k = e.repr (e i * e j) k := rfl

end OfBasis
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg"

def Table.map {R' : Type*} [CommRing R'] (T : Table R N) (f : R →+* R') : Table R' N where
  γ i j k := f (T.γ i j k)
  unit j k := by rw [T.unit]; split_ifs <;> simp
  comm i j k := by rw [T.comm]
  assoc i j l m := by
    have h := congrArg f (T.assoc i j l m)
    simpa only [map_sum, map_mul] using h

@[scoped simp] theorem Table.map_γ {R' : Type*} [CommRing R'] (T : Table R N) (f : R →+* R')
    (i j k : Fin (N + 1)) : (T.map f).γ i j k = f (T.γ i j k) := rfl

p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.Table"
end TableAlgebra
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.Table"

section Witt

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectRing K p]

local notation "𝕎" => WittVector p

def rho (m : ℕ) : TruncatedWittVector p (m + 1) K →+* K :=
  RingHom.liftOfRightInverse (WittVector.truncate (m + 1)) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨WittVector.constantCoeff, by
      intro x hx
      rw [WittVector.mem_ker_truncate] at hx
      rw [RingHom.mem_ker, WittVector.constantCoeff_apply]
      exact hx 0 (Nat.succ_pos m)⟩

theorem rho_truncate (m : ℕ) (x : 𝕎 K) :
    rho p K m (WittVector.truncate (m + 1) x) = x.coeff 0 :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem rho_apply (m : ℕ) (x : TruncatedWittVector p (m + 1) K) : rho p K m x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 1) K x
  rw [rho_truncate, WittVector.coeff_truncate]
  rfl

theorem rho_surjective (m : ℕ) : Function.Surjective (rho p K m) := fun x =>
  ⟨WittVector.truncate (m + 1) (WittVector.teichmuller p x), by
    rw [rho_truncate, WittVector.teichmuller_coeff_zero]⟩

theorem rho_zero_injective : Function.Injective (rho p K 0) := by
  intro x y h
  rw [rho_apply, rho_apply] at h
  ext i
  have hi : i = 0 := Fin.ext (by have := i.2; simp only [Fin.val_zero]; omega)
  subst hi
  exact h

def rhoZeroEquiv : TruncatedWittVector p 1 K ≃+* K :=
  RingEquiv.ofBijective (rho p K 0) ⟨rho_zero_injective p K, rho_surjective p K 0⟩

theorem rhoZeroEquiv_apply (x : TruncatedWittVector p 1 K) : rhoZeroEquiv p K x = rho p K 0 x := rfl

abbrev piT (m : ℕ) : TruncatedWittVector p (m + 2) K →+* TruncatedWittVector p (m + 1) K :=
  TruncatedWittVector.truncate (Nat.le_succ (m + 1))

theorem piT_surjective (m : ℕ) : Function.Surjective (piT p K m) :=
  TruncatedWittVector.truncate_surjective _

theorem rho_piT (m : ℕ) (a : TruncatedWittVector p (m + 2) K) :
    rho p K m (piT p K m a) = rho p K (m + 1) a := by
  rw [rho_apply, rho_apply, TruncatedWittVector.coeff_truncate]
  rfl

theorem truncate_p_pow_mul_eq_zero (m : ℕ) (D : 𝕎 K) :
    WittVector.truncate (m + 2) ((p : 𝕎 K) ^ (m + 2) * D) = 0 := by
  rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 2)).1
    (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))

theorem piT_eq_zero_iff (m : ℕ) (a : TruncatedWittVector p (m + 2) K) :
    piT p K m a = 0 ↔ ((p : TruncatedWittVector p (m + 2) K) ^ (m + 1)) ∣ a := by
  obtain ⟨A, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 2) K a
  rw [TruncatedWittVector.truncate_wittVector_truncate, ← RingHom.mem_ker,
    WittVector.mem_ker_truncate]
  constructor
  · intro h
    have hA : A ∈ Ideal.span {(p : 𝕎 K) ^ (m + 1)} :=
      (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero A (m + 1)).2 h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hA
    refine ⟨WittVector.truncate (m + 2) c, ?_⟩
    rw [hc, map_mul, map_pow, map_natCast]
  · rintro ⟨c, hc⟩
    obtain ⟨C, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 2) K c
    have hEq : WittVector.truncate (m + 2) A =
        WittVector.truncate (m + 2) ((p : 𝕎 K) ^ (m + 1) * C) := by
      rw [hc, map_mul, map_pow, map_natCast]
    have hk : A - (p : 𝕎 K) ^ (m + 1) * C ∈
        RingHom.ker (WittVector.truncate (p := p) (R := K) (m + 2)) := by
      rw [RingHom.mem_ker, map_sub, hEq, sub_self]
    rw [WittVector.mem_ker_truncate] at hk
    have hk' : ∀ i < m + 1, (A - (p : 𝕎 K) ^ (m + 1) * C).coeff i = 0 :=
      fun i hi => hk i (by omega)
    rw [← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero] at hk'
    intro i hi
    rw [hk' i hi]
    exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).1
      (Ideal.mem_span_singleton.2 (dvd_mul_right _ _)) i hi

theorem exists_eq_p_mul_of_rho_piT_eq_zero (m : ℕ) (a : TruncatedWittVector p (m + 2) K)
    (h : rho p K m (piT p K m a) = 0) :
    ∃ D : 𝕎 K, a = WittVector.truncate (m + 2) ((p : 𝕎 K) * D) := by
  obtain ⟨A, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 2) K a
  rw [rho_piT, rho_truncate] at h
  have hA : A ∈ Ideal.span {(p : 𝕎 K)} :=
    (WittVector.mem_span_p_iff_coeff_zero_eq_zero A).2 h
  obtain ⟨D, hD⟩ := Ideal.mem_span_singleton.1 hA
  exact ⟨D, by rw [hD]⟩

theorem p_pow_mul_eq_zero_of_rho_piT_eq_zero (m : ℕ) (a : TruncatedWittVector p (m + 2) K)
    (h : rho p K m (piT p K m a) = 0) :
    (p : TruncatedWittVector p (m + 2) K) ^ (m + 1) * a = 0 := by
  obtain ⟨D, rfl⟩ := exists_eq_p_mul_of_rho_piT_eq_zero p K m a h
  have : (p : TruncatedWittVector p (m + 2) K) ^ (m + 1) =
      WittVector.truncate (m + 2) ((p : 𝕎 K) ^ (m + 1)) := by
    rw [map_pow, map_natCast]
  rw [this, ← map_mul, ← mul_assoc, ← pow_succ]
  exact truncate_p_pow_mul_eq_zero p K m D

theorem isNilpotent_of_rho_piT_eq_zero (m : ℕ) (a : TruncatedWittVector p (m + 2) K)
    (h : rho p K m (piT p K m a) = 0) : IsNilpotent a := by
  obtain ⟨D, rfl⟩ := exists_eq_p_mul_of_rho_piT_eq_zero p K m a h
  refine ⟨m + 2, ?_⟩
  rw [← map_pow, mul_pow]
  exact truncate_p_pow_mul_eq_zero p K m _

theorem truncate_le_refl {m : ℕ} (x : TruncatedWittVector p m K) :
    TruncatedWittVector.truncate (le_refl m) x = x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) m K x
  rw [TruncatedWittVector.truncate_wittVector_truncate]

theorem eq_of_forall_map_truncate {P Q : (𝕎 K)[X]}
    (h : ∀ m : ℕ, P.map (WittVector.truncate (m + 1)) = Q.map (WittVector.truncate (m + 1))) :
    P = Q := by
  ext t c
  have h1 := congrArg (fun F : (TruncatedWittVector p (c + 1) K)[X] => (F.coeff t).coeff (Fin.last c))
    (h c)
  simpa only [Polynomial.coeff_map, WittVector.coeff_truncate, Fin.val_last] using h1

theorem constantCoeff_eq_rho_comp_truncate :
    (WittVector.constantCoeff : 𝕎 K →+* K) = (rho p K 0).comp (WittVector.truncate (0 + 1)) := by
  ext x
  rw [RingHom.comp_apply, rho_truncate, WittVector.constantCoeff_apply]

end Witt
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.Table"

section Tower

variable {p : ℕ} [hp : Fact p.Prime] {K : Type u} [Field K] [IsAlgClosed K] [CharP K p]
  {n : ℕ} {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra K[X] B]

local notation "𝕎" => WittVector p

structure Datum (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B] where

  b : Module.Basis (Fin (n + 1)) K[X] B

  d : Fin (n + 1) → ℕ
  hb0 : b 0 = 1
  hd0 : d 0 = 0
  hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2
  hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k
  hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧ (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k

variable (p) (D : Datum K n B)

structure Good (m : ℕ)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 1) K)[X]) :
    Prop where
  unit : ∀ j k, γ 0 j k = if j = k then 1 else 0
  comm : ∀ i j k, γ i j k = γ j i k
  assoc : ∀ i j l m', ∑ k, γ i j k * γ k l m' = ∑ k, γ j l k * γ i k m'
  deg : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ D.d i + D.d j - D.d k
  red : ∀ i j k, (γ i j k).map (rho p K m) = D.b.repr (D.b i * D.b j) k

def table0 : Table ((TruncatedWittVector p 1 K)[X]) n :=
  (tableOfBasis D.b D.hb0).map
    (Polynomial.mapRingHom ((rhoZeroEquiv p K).symm : K ≃+* TruncatedWittVector p 1 K).toRingHom)

theorem table0_γ (i j k : Fin (n + 1)) :
    (table0 p D).γ i j k =
      (D.b.repr (D.b i * D.b j) k).map
        ((rhoZeroEquiv p K).symm : K ≃+* TruncatedWittVector p 1 K).toRingHom := rfl

theorem good_table0 : Good p D 0 (table0 p D).γ where
  unit := (table0 p D).unit
  comm := (table0 p D).comm
  assoc := (table0 p D).assoc
  deg i j k hi hj := by
    rw [table0_γ, Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective _)]
    exact D.hdeg i j k hi hj
  red i j k := by
    rw [table0_γ, Polynomial.map_map]
    have : (rho p K 0).comp
        ((rhoZeroEquiv p K).symm : K ≃+* TruncatedWittVector p 1 K).toRingHom = RingHom.id K := by
      ext x
      change rhoZeroEquiv p K ((rhoZeroEquiv p K).symm x) = x
      exact RingEquiv.apply_symm_apply _ _
    rw [this, Polynomial.map_id]

theorem exists_step (m : ℕ)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 1) K)[X])
    (hγ : Good p D m γ) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 2) K)[X],
      Good p D (m + 1) γ' ∧ ∀ i j k, (γ' i j k).map (piT p K m) = γ i j k := by
  obtain ⟨γ', h1, hc, ha, hdg, hred⟩ :=
    AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension K n B D.b D.d
      D.hb0 D.hd0 D.hd D.hdeg D.hinf
      (TruncatedWittVector p (m + 2) K) (TruncatedWittVector p (m + 1) K) (piT p K m)
      (piT_surjective p K m) ((p : TruncatedWittVector p (m + 2) K) ^ (m + 1))
      (piT_eq_zero_iff p K m) (rho p K m) (rho_surjective p K m)
      (p_pow_mul_eq_zero_of_rho_piT_eq_zero p K m) (isNilpotent_of_rho_piT_eq_zero p K m)
      γ hγ.unit hγ.comm hγ.assoc hγ.deg hγ.red
  have hcomp : (rho p K m).comp (piT p K m) = rho p K (m + 1) := by
    ext a; exact rho_piT p K m a
  refine ⟨γ', ⟨h1, hc, ha, hdg, fun i j k => ?_⟩, hred⟩
  rw [← hγ.red i j k, ← hred i j k, Polynomial.map_map, hcomp]

def stage : (m : ℕ) →
    {γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 1) K)[X] //
      Good p D m γ}
  | 0 => ⟨(table0 p D).γ, good_table0 p D⟩
  | m + 1 => ⟨(exists_step p D m (stage m).1 (stage m).2).choose,
      (exists_step p D m (stage m).1 (stage m).2).choose_spec.1⟩

theorem stage_succ_map (m : ℕ) (i j k : Fin (n + 1)) :
    ((stage p D (m + 1)).1 i j k).map (piT p K m) = (stage p D m).1 i j k :=
  (exists_step p D m (stage p D m).1 (stage p D m).2).choose_spec.2 i j k

theorem stage_compat (c : ℕ) : ∀ (e : ℕ) (i j k : Fin (n + 1)),
    ((stage p D (c + e)).1 i j k).map
        (TruncatedWittVector.truncate (by omega : c + 1 ≤ c + e + 1)) = (stage p D c).1 i j k
  | 0, i, j, k => by
    have : TruncatedWittVector.truncate (p := p) (R := K) (le_refl (c + 1)) = RingHom.id _ := by
      ext1 x; exact truncate_le_refl p K x
    change ((stage p D c).1 i j k).map (TruncatedWittVector.truncate (le_refl (c + 1))) = _
    rw [this, Polynomial.map_id]
  | e + 1, i, j, k => by
    have h1 : c + 1 ≤ c + e + 1 := by omega
    have h2 : c + e + 1 ≤ c + e + 2 := by omega
    change ((stage p D (c + e + 1)).1 i j k).map (TruncatedWittVector.truncate (h1.trans h2)) = _
    rw [← TruncatedWittVector.truncate_comp h1 h2, ← Polynomial.map_map]
    have h3 : ((stage p D (c + e + 1)).1 i j k).map (TruncatedWittVector.truncate h2) =
        (stage p D (c + e)).1 i j k := stage_succ_map p D (c + e) i j k
    rw [h3]
    exact stage_compat c e i j k

def wlim (i j k : Fin (n + 1)) (t : ℕ) : 𝕎 K :=
  WittVector.mk p fun m => TruncatedWittVector.coeff (Fin.last m) (((stage p D m).1 i j k).coeff t)

theorem coeff_stage_eq (c e : ℕ) (i j k : Fin (n + 1)) (t : ℕ) :
    TruncatedWittVector.coeff ⟨c, by omega⟩ (((stage p D (c + e)).1 i j k).coeff t) =
      TruncatedWittVector.coeff (Fin.last c) (((stage p D c).1 i j k).coeff t) := by
  have h := congrArg (fun P : (TruncatedWittVector p (c + 1) K)[X] =>
    TruncatedWittVector.coeff (Fin.last c) (P.coeff t)) (stage_compat p D c e i j k)
  simp only [Polynomial.coeff_map, TruncatedWittVector.coeff_truncate] at h
  exact h

theorem truncate_wlim (m : ℕ) (i j k : Fin (n + 1)) (t : ℕ) :
    WittVector.truncate (m + 1) (wlim p D i j k t) = ((stage p D m).1 i j k).coeff t := by
  ext ⟨c, hc⟩
  rw [WittVector.coeff_truncate, wlim, WittVector.coeff_mk]
  obtain ⟨e, rfl⟩ : ∃ e, m = c + e := ⟨m - c, by omega⟩
  exact (coeff_stage_eq p D c e i j k t).symm

def Γlim (i j k : Fin (n + 1)) : (𝕎 K)[X] :=
  ∑ t ∈ Finset.range 5, C (wlim p D i j k t) * X ^ t

theorem coeff_Γlim (i j k : Fin (n + 1)) (t : ℕ) :
    (Γlim p D i j k).coeff t = if t < 5 then wlim p D i j k t else 0 := by
  rw [Γlim, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with ht
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro s _ hs; rw [if_neg (Ne.symm hs)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hs)

theorem natDegree_stage_le (m : ℕ) (i j k : Fin (n + 1)) :
    ((stage p D m).1 i j k).natDegree ≤ 4 := by
  have hG := (stage p D m).2
  by_cases hi : i = 0
  · subst hi; rw [hG.unit]; split_ifs <;> simp
  by_cases hj : j = 0
  · subst hj; rw [hG.comm, hG.unit]; split_ifs <;> simp
  refine (hG.deg i j k hi hj).trans ?_
  have h1 := D.hd i hi
  have h2 := D.hd j hj
  omega

theorem map_truncate_Γlim (m : ℕ) (i j k : Fin (n + 1)) :
    (Γlim p D i j k).map (WittVector.truncate (m + 1)) = (stage p D m).1 i j k := by
  ext t : 1
  rw [Polynomial.coeff_map, coeff_Γlim]
  split_ifs with ht
  · exact truncate_wlim p D m i j k t
  · rw [map_zero]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := natDegree_stage_le p D m i j k
    omega

def tableLim : Table ((𝕎 K)[X]) n where
  γ := Γlim p D
  unit j k := by
    apply eq_of_forall_map_truncate p K
    intro m
    rw [map_truncate_Γlim, (stage p D m).2.unit]
    split_ifs <;> simp
  comm i j k := by
    apply eq_of_forall_map_truncate p K
    intro m
    rw [map_truncate_Γlim, map_truncate_Γlim, (stage p D m).2.comm]
  assoc i j l m' := by
    apply eq_of_forall_map_truncate p K
    intro m
    simp only [Polynomial.map_sum, Polynomial.map_mul, map_truncate_Γlim]
    exact (stage p D m).2.assoc i j l m'

theorem tableLim_γ (i j k : Fin (n + 1)) : (tableLim p D).γ i j k = Γlim p D i j k := rfl

theorem natDegree_Γlim_le (i j k : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) :
    (Γlim p D i j k).natDegree ≤ D.d i + D.d j - D.d k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_Γlim]
  split_ifs with h5
  · ext m
    rw [wlim, WittVector.coeff_mk, WittVector.zero_coeff]
    have hlt : ((stage p D m).1 i j k).natDegree < t :=
      lt_of_le_of_lt ((stage p D m).2.deg i j k hi hj) (by exact_mod_cast ht)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact TruncatedWittVector.coeff_zero (p := p) _ _ _
  · rfl

theorem map_constantCoeff_Γlim (i j k : Fin (n + 1)) :
    (Γlim p D i j k).map (WittVector.constantCoeff : 𝕎 K →+* K) = D.b.repr (D.b i * D.b j) k := by
  rw [constantCoeff_eq_rho_comp_truncate p K, ← Polynomial.map_map, map_truncate_Γlim]
  exact (stage p D 0).2.red i j k

private abbrev _root_.WittLiftNF.red : (𝕎 K)[X] →+* K[X] := Polynomial.mapRingHom (WittVector.constantCoeff : 𝕎 K →+* K)

p2m_export "WittLiftNF" "red"
theorem red_apply (f : (𝕎 K)[X]) : red p f = f.map (WittVector.constantCoeff : 𝕎 K →+* K) := rfl

theorem red_Γlim (i j k : Fin (n + 1)) :
    red p ((tableLim p D).γ i j k) = D.b.repr (D.b i * D.b j) k :=
  map_constantCoeff_Γlim p D i j k

def piFun (x : TAlg (tableLim p D)) : B := ∑ i, red p (x.coord i) • D.b i

theorem piFun_add (x y : TAlg (tableLim p D)) : piFun p D (x + y) = piFun p D x + piFun p D y := by
  simp only [piFun, TAlg.coord_add, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem piFun_single (i : Fin (n + 1)) (f : (𝕎 K)[X]) :
    piFun p D (TAlg.mk (Pi.single i f)) = red p f • D.b i := by
  rw [piFun, TAlg.coord_mk, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem piFun_one : piFun p D 1 = 1 := by
  have : (1 : TAlg (tableLim p D)) = TAlg.mk (Pi.single 0 1) := rfl
  rw [this, piFun_single, map_one, one_smul, D.hb0]

theorem b_mul_b (i j : Fin (n + 1)) :
    D.b i * D.b j = ∑ m, D.b.repr (D.b i * D.b j) m • D.b m :=
  (D.b.sum_repr (D.b i * D.b j)).symm

theorem piFun_mul (x y : TAlg (tableLim p D)) :
    piFun p D (x * y) = piFun p D x * piFun p D y := by
  have hL : piFun p D (x * y) =
      ∑ m, ∑ i, ∑ j, (red p (x.coord i) * red p (y.coord j) * D.b.repr (D.b i * D.b j) m) •
        D.b m := by
    rw [piFun]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TAlg.coord_mul, cst_apply, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, red_Γlim]
  have hR : piFun p D x * piFun p D y =
      ∑ i, ∑ j, ∑ m, (red p (x.coord i) * red p (y.coord j) * D.b.repr (D.b i * D.b j) m) •
        D.b m := by
    rw [piFun, piFun, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
    conv_lhs => rw [b_mul_b D i j]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  rw [hL, hR]
  exact sum3_rot _

def piB : TAlg (tableLim p D) →+* B where
  toFun := piFun p D
  map_one' := piFun_one p D
  map_mul' := piFun_mul p D
  map_zero' := by simp [piFun]
  map_add' := piFun_add p D

theorem piB_apply (x : TAlg (tableLim p D)) : piB p D x = ∑ i, red p (x.coord i) • D.b i := rfl

theorem piB_algebraMap (f : (𝕎 K)[X]) :
    piB p D (algebraMap (𝕎 K)[X] (TAlg (tableLim p D)) f) =
      algebraMap K[X] B (f.map (WittVector.constantCoeff : 𝕎 K →+* K)) := by
  have : algebraMap (𝕎 K)[X] (TAlg (tableLim p D)) f = TAlg.mk (Pi.single 0 f) := by
    ext1; rw [TAlg.algebraMap_coord, TAlg.coord_mk]
  rw [this]
  change piFun p D _ = _
  rw [piFun_single, D.hb0, Algebra.algebraMap_eq_smul_one]
  rfl

theorem piB_basis (i : Fin (n + 1)) : piB p D (TAlg.basis (tableLim p D) i) = D.b i := by
  rw [TAlg.basis_apply]
  change piFun p D _ = _
  rw [piFun_single, map_one, one_smul]

theorem natDegree_repr_basis_mul (i j k : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) :
    ((TAlg.basis (tableLim p D)).repr
        (TAlg.basis (tableLim p D) i * TAlg.basis (tableLim p D) j) k).natDegree ≤
      D.d i + D.d j - D.d k := by
  rw [TAlg.repr_basis_mul_basis, tableLim_γ]
  exact natDegree_Γlim_le p D i j k hi hj

end Tower
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.Table"

end WittLiftNF
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.Table P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.TAlg P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF.Table P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.WittLiftNF"

open WittLiftNF in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    ∃ (Bt : Type u) (_ : CommRing Bt) (_ : Algebra (WittVector p K)[X] Bt)
      (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (π : Bt →+* B),
      bt 0 = 1 ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k) ∧
      (∀ f : (WittVector p K)[X],
        π (algebraMap (WittVector p K)[X] Bt f) =
          algebraMap K[X] B (f.map (WittVector.constantCoeff : WittVector p K →+* K))) ∧
      (∀ i, π (bt i) = b i) := by
  let D : Datum K n B := ⟨b, d, hb0, hd0, hd, hdeg, hinf⟩
  exact ⟨TAlg (tableLim p D), inferInstance, inferInstance, TAlg.basis (tableLim p D), piB p D,
    TAlg.basis_zero _, natDegree_repr_basis_mul p D, piB_algebraMap p D, piB_basis p D⟩

end S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder
end P2MW
export P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder (solution)
