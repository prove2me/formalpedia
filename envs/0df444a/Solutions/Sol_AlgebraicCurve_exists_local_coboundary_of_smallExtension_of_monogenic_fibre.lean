-- Prove2me | solution 1 for AlgebraicCurve.exists_local_coboundary_of_smallExtension_of_monogenic_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4b52a498-b5df-5144-8058-25dfa614dcd1

import Mathlib
import Theorems.Thm_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

universe u v w w'

noncomputable section

namespace LocCobSol

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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg"

def Table.map {R' : Type*} [CommRing R'] (T : Table R N) (f : R →+* R') : Table R' N where
  γ i j k := f (T.γ i j k)
  unit j k := by rw [T.unit]; split_ifs <;> simp
  comm i j k := by rw [T.comm]
  assoc i j l m := by
    have h := congrArg f (T.assoc i j l m)
    simpa only [map_sum, map_mul] using h

@[scoped simp] theorem Table.map_γ {R' : Type*} [CommRing R'] (T : Table R N) (f : R →+* R')
    (i j k : Fin (N + 1)) : (T.map f).γ i j k = f (T.γ i j k) := rfl

p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table"
end TableAlgebra
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table"

section Homs

variable {R : Type*} [CommRing R] {N : ℕ}

theorem cst_map {R₂ : Type*} [CommRing R₂] (f : R →+* R₂)
    (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R) (m : Fin (N + 1)) :
    f (cst γ x y m) = cst (fun i j k => f (γ i j k)) (fun i => f (x i)) (fun j => f (y j)) m := by
  simp only [cst_apply, map_sum, map_mul]

def TAlg.mapHom (T₁ : Table R N) {R₂ : Type*} [CommRing R₂] (T₂ : Table R₂ N) (f : R →+* R₂)
    (hf : ∀ i j k, f (T₁.γ i j k) = T₂.γ i j k) : TAlg T₁ →+* TAlg T₂ where
  toFun x := TAlg.mk fun k => f (x.coord k)
  map_one' := by
    ext1; funext k
    simp only [TAlg.coord_mk, TAlg.coord_one, Pi.single_apply]
    split_ifs <;> simp
  map_mul' x y := by
    ext1; funext m
    simp only [TAlg.coord_mk, TAlg.coord_mul]
    rw [cst_map]
    simp only [hf]
  map_zero' := by ext1; funext k; simp
  map_add' x y := by ext1; funext k; simp

@[scoped simp] theorem TAlg.mapHom_coord (T₁ : Table R N) {R₂ : Type*} [CommRing R₂] (T₂ : Table R₂ N)
    (f : R →+* R₂) (hf : ∀ i j k, f (T₁.γ i j k) = T₂.γ i j k) (x : TAlg T₁) (k : Fin (N + 1)) :
    (TAlg.mapHom T₁ T₂ f hf x).coord k = f (x.coord k) := rfl

p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table"
variable {C : Type*} [CommRing C] [Algebra R C] (e : Module.Basis (Fin (N + 1)) R C)

theorem repr_mul_eq_cst (x y : C) (m : Fin (N + 1)) :
    e.repr (x * y) m = cst (fun i j k => e.repr (e i * e j) k) (fun i => e.repr x i)
      (fun j => e.repr y j) m := by
  have hx : x = ∑ i, e.repr x i • e i := (e.sum_repr x).symm
  have hy : y = ∑ j, e.repr y j • e j := (e.sum_repr y).symm
  conv_lhs => rw [hx, hy, Finset.sum_mul_sum]
  rw [map_sum, Finsupp.finsetSum_apply, cst_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_sum_smul (c : Fin (N + 1) → R) (m : Fin (N + 1)) :
    e.repr (∑ k, c k • e k) m = c m := by
  rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single m]
  · rw [map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply, if_pos rfl, smul_eq_mul,
      mul_one]
  · intro k _ hk
    rw [map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply, if_neg hk, smul_zero]
  · intro h; exact absurd (Finset.mem_univ m) h

def basedHom (he : e 0 = 1) {R₂ : Type*} [CommRing R₂] (T : Table R₂ N) (f : R →+* R₂)
    (hf : ∀ i j k, f (e.repr (e i * e j) k) = T.γ i j k) : C →+* TAlg T where
  toFun x := TAlg.mk fun k => f (e.repr x k)
  map_one' := by
    ext1; funext k
    simp only [TAlg.coord_mk, TAlg.coord_one, Pi.single_apply, ← he, e.repr_self,
      Finsupp.single_apply]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero]
  map_mul' x y := by
    ext1; funext m
    simp only [TAlg.coord_mk, TAlg.coord_mul]
    rw [repr_mul_eq_cst, cst_map]
    simp only [hf]
  map_zero' := by ext1; funext k; simp
  map_add' x y := by ext1; funext k; simp

@[scoped simp] theorem basedHom_coord (he : e 0 = 1) {R₂ : Type*} [CommRing R₂] (T : Table R₂ N)
    (f : R →+* R₂) (hf : ∀ i j k, f (e.repr (e i * e j) k) = T.γ i j k) (x : C) (k : Fin (N + 1)) :
    (basedHom e he T f hf x).coord k = f (e.repr x k) := rfl

end Homs
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table"

section PolyKer

variable {S T : Type*} [CommRing S] [CommRing T]

open Classical in

def divε (ε c : S) : S :=
  if c = 0 then 0 else if h : ε ∣ c then Classical.choose h else 0

open Classical in
theorem divε_zero (ε : S) : divε ε 0 = 0 := by simp [divε]

open Classical in
theorem mul_divε (ε c : S) (h : ε ∣ c) : ε * divε ε c = c := by
  by_cases hc : c = 0
  · simp [divε, hc]
  · rw [divε, if_neg hc, dif_pos h]
    exact (Classical.choose_spec h).symm

theorem exists_eq_C_mul_of_map_eq_zero (π : S →+* T) (ε : S) (hker : ∀ a : S, π a = 0 ↔ ε ∣ a)
    (f : S[X]) (hf : f.map π = 0) : ∃ g : S[X], f = C ε * g := by
  refine ⟨∑ t ∈ Finset.range (f.natDegree + 1), C (divε ε (f.coeff t)) * X ^ t, ?_⟩
  ext t
  rw [coeff_C_mul, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  have hdiv : ε ∣ f.coeff t := by
    rw [← hker]
    have := congrArg (fun F : T[X] => F.coeff t) hf
    simpa only [coeff_map, coeff_zero] using this
  by_cases ht : t < f.natDegree + 1
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl, mul_divε ε _ hdiv]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · rw [Finset.sum_eq_zero, mul_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
    intro b hb
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hb)

end PolyKer
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table"

section Main

variable {K : Type u} [Field K] {n : ℕ} {B : Type v} [CommRing B] [Algebra K[X] B]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main
    (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (P : Ideal K[X]) (hP : P.IsMaximal)
    (hmono : ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X],
      z - aeval y q ∈ P • (⊤ : Submodule K[X] B)) :
    ∃ s : K[X], s ∉ P ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        s * (ac i j l m).map (ρ.comp π) := by
  classical

  let θ : A' →+* K := ρ.comp π
  let πX : A'[X] →+* A[X] := mapRingHom π
  let ρX : A[X] →+* K[X] := mapRingHom ρ
  let θX : A'[X] →+* K[X] := mapRingHom θ
  have hθX : ∀ f : A'[X], θX f = ρX (πX f) := fun f => by
    change f.map θ = (f.map π).map ρ
    rw [Polynomial.map_map]
  have hπXs : Function.Surjective πX := Polynomial.map_surjective π hπ
  have hρXs : Function.Surjective ρX := Polynomial.map_surjective ρ hρ
  have hπε : π ε = 0 := (hker ε).2 (dvd_refl ε)
  have hθε : θX (C ε) = 0 := by
    change (C ε).map θ = 0
    rw [map_C]; change C (ρ (π ε)) = 0; rw [hπε, map_zero, C_0]

  have hannX : ∀ W : A'[X], C ε * W = 0 → θX W = 0 := by
    intro W hW
    ext t
    rw [coeff_zero]
    change (W.map θ).coeff t = 0
    rw [coeff_map]
    exact hann _ (by simpa only [coeff_C_mul, coeff_zero] using congrArg (fun F => coeff F t) hW)
  haveI hPmax : P.IsMaximal := hP
  let Q : Ideal A[X] := P.comap ρX
  haveI hQmax : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective ρX hρXs
  haveI hQprime : Q.IsPrime := hQmax.isPrime
  let Q' : Ideal A'[X] := Q.comap πX
  haveI hQ'max : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective πX hπXs
  haveI hQ'prime : Q'.IsPrime := hQ'max.isPrime
  have hmemQ' : ∀ f : A'[X], f ∈ Q' ↔ θX f ∈ P := fun f => by
    rw [hθX]; rfl
  let Rl := Localization.AtPrime Q
  let R'l := Localization.AtPrime Q'
  let πl : R'l →+* Rl := Localization.localRingHom Q' Q πX rfl
  have hπl_alg : ∀ x : A'[X], πl (algebraMap A'[X] R'l x) = algebraMap A[X] Rl (πX x) :=
    fun x => Localization.localRingHom_to_map Q' Q πX rfl x

  have hπls : Function.Surjective πl := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨a', ha'⟩ := hπXs a
    obtain ⟨s', hs'⟩ := hπXs s
    have hs'Q : s' ∈ Q'.primeCompl := by
      intro h
      apply s.2
      change πX s' ∈ Q at h
      rwa [hs'] at h
    refine ⟨IsLocalization.mk' R'l a' ⟨s', hs'Q⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    change IsLocalization.mk' Rl (πX a') _ = IsLocalization.mk' Rl a s
    congr 1
    exact Subtype.ext hs'

  let εl : R'l := algebraMap A'[X] R'l (C ε)
  have hkerl : ∀ x : R'l, πl x = 0 → ∃ z : R'l, x = εl * z := by
    intro x hx
    obtain ⟨⟨a', s'⟩, rfl⟩ := IsLocalization.mk'_surjective Q'.primeCompl x
    change πl (IsLocalization.mk' R'l a' s') = 0 at hx
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hπXs m
    have hm'Q : m' ∈ Q'.primeCompl := by
      intro h; apply m.2; change πX m' ∈ Q at h; rwa [hm'] at h
    have h0 : πX (m' * a') = 0 := by rw [map_mul, hm']; exact hm
    have h0' : (m' * a').map π = 0 := h0
    obtain ⟨g, hg⟩ := exists_eq_C_mul_of_map_eq_zero π ε hker (m' * a') h0'
    refine ⟨IsLocalization.mk' R'l g (⟨m', hm'Q⟩ * s'), ?_⟩
    change IsLocalization.mk' R'l a' s' = algebraMap A'[X] R'l (C ε) * IsLocalization.mk' R'l g _
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, ← hg, IsLocalization.mk'_mul,
      IsLocalization.mk'_self R'l hm'Q, one_mul]

  have hannl : ∀ W : A'[X], algebraMap A'[X] R'l (C ε * W) = 0 → θX W = 0 := by
    intro W hW
    rw [IsLocalization.map_eq_zero_iff Q'.primeCompl] at hW
    obtain ⟨v, hv⟩ := hW
    have h1 : θX (v * W) = 0 := hannX _ (by rw [← hv]; ring)
    rw [map_mul] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso; apply v.2
      change (v : A'[X]) ∈ Q'
      rw [hmemQ', h]; exact P.zero_mem
    · exact h

  let κ := K[X] ⧸ P
  letI : Field κ := Ideal.Quotient.field P
  let mkP : K[X] →+* κ := Ideal.Quotient.mk P
  have hunit : ∀ s : Q.primeCompl, IsUnit ((mkP.comp ρX) s) := by
    intro s
    rw [isUnit_iff_ne_zero]
    intro h
    apply s.2
    change ρX s ∈ P
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  let lam : Rl →+* κ := IsLocalization.lift (M := Q.primeCompl) (S := Rl) hunit
  have hlam_alg : ∀ x : A[X], lam (algebraMap A[X] Rl x) = mkP (ρX x) := fun x =>
    IsLocalization.lift_eq hunit x
  have hlams : Function.Surjective lam := by
    intro c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨g, rfl⟩ := hρXs f
    exact ⟨algebraMap A[X] Rl g, hlam_alg g⟩
  have hlamker : ∀ x : Rl, lam x = 0 → x ∈ IsLocalRing.maximalIdeal Rl := by
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    change IsLocalization.mk' Rl a s ∈ _
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff Rl Q a s]
    have h1 := IsLocalization.mk'_spec Rl a s
    have h2 := congrArg lam h1
    change lam (IsLocalization.mk' Rl a s) = 0 at hx
    rw [map_mul, hx, zero_mul, hlam_alg] at h2
    change a ∈ P.comap ρX
    rw [Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

  let TA : Table A[X] n := ⟨γ, hγ1, hγc, hγa⟩
  let Tl : Table Rl n := TA.map (algebraMap A[X] Rl)
  let TB : Table K[X] n := tableOfBasis b hb0
  let Tκ : Table κ n := TB.map mkP
  let Cl := TAlg Tl
  let e : Module.Basis (Fin (n + 1)) Rl Cl := TAlg.basis Tl
  have he0 : e 0 = 1 := TAlg.basis_zero Tl
  have hlamγ : ∀ i j k, lam (Tl.γ i j k) = Tκ.γ i j k := by
    intro i j k
    change lam (algebraMap A[X] Rl (γ i j k)) = mkP (b.repr (b i * b j) k)
    rw [hlam_alg, ← hγB]; rfl
  let redC : Cl →+* TAlg Tκ := TAlg.mapHom Tl Tκ lam hlamγ
  let redB : B →+* TAlg Tκ := basedHom b hb0 Tκ mkP (fun i j k => rfl)

  have hredB_P : ∀ z : B, z ∈ P • (⊤ : Submodule K[X] B) → redB z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun p hp w _ => ?_) (fun x y hx hy => ?_)
    · ext1; funext k
      rw [basedHom_coord, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
      rfl
    · rw [map_add, hx, hy, add_zero]

  have hredB_alg : ∀ f : K[X], redB (algebraMap K[X] B f) = algebraMap κ (TAlg Tκ) (mkP f) := by
    intro f
    ext1; funext k
    rw [basedHom_coord, TAlg.algebraMap_coord, Algebra.algebraMap_eq_smul_one, ← hb0, map_smul,
      b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, Pi.single_apply, smul_eq_mul]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero, map_zero]
  have hredC_alg : ∀ r : Rl, redC (algebraMap Rl Cl r) = algebraMap κ (TAlg Tκ) (lam r) := by
    intro r
    ext1; funext k
    rw [TAlg.mapHom_coord, TAlg.algebraMap_coord, TAlg.algebraMap_coord, Pi.single_apply,
      Pi.single_apply]
    split_ifs <;> simp

  have hlift : ∀ w : Cl, ∃ z : B, redB z = redC w := by
    intro w
    have hc : ∀ k, ∃ f : K[X], mkP f = lam (w.coord k) := fun k =>
      Ideal.Quotient.mk_surjective (lam (w.coord k))
    choose f hf using hc
    refine ⟨∑ k, f k • b k, ?_⟩
    ext1; funext k
    rw [basedHom_coord, repr_sum_smul, TAlg.mapHom_coord, hf]

  obtain ⟨yB, hyB⟩ := hmono
  have hyc : ∀ k, ∃ r : Rl, lam r = (redB yB).coord k := fun k => hlams _
  choose ry hry using hyc
  let yC : Cl := TAlg.mk ry
  have hyC : redC yC = redB yB := by
    ext1; funext k; rw [TAlg.mapHom_coord]; exact hry k
  have hmonoC : ∀ w : Cl, ∃ q : Polynomial Rl,
      w - aeval yC q ∈ (IsLocalRing.maximalIdeal Rl) • (⊤ : Submodule Rl Cl) := by
    intro w
    obtain ⟨z, hz⟩ := hlift w
    obtain ⟨q₀, hq₀⟩ := hyB z
    obtain ⟨q, hq⟩ := Polynomial.map_surjective lam hlams (q₀.map mkP)
    refine ⟨q, ?_⟩

    have h1 : redB (aeval yB q₀) = (q₀.map mkP).eval₂ (algebraMap κ (TAlg Tκ)) (redB yB) := by
      rw [aeval_def, hom_eval₂, eval₂_map]
      congr 1
      exact RingHom.ext fun f => hredB_alg f
    have h2 : redC (aeval yC q) = (q₀.map mkP).eval₂ (algebraMap κ (TAlg Tκ)) (redB yB) := by
      rw [aeval_def, hom_eval₂, ← hq, eval₂_map, hyC]
      congr 1
      exact RingHom.ext fun r => hredC_alg r
    have h3 : redB (z - aeval yB q₀) = 0 := hredB_P _ hq₀
    have h4 : redC (w - aeval yC q) = 0 := by
      rw [map_sub, ← hz, h2, ← h1, ← map_sub, h3]

    have h5 : ∀ k, (w - aeval yC q).coord k ∈ IsLocalRing.maximalIdeal Rl := by
      intro k
      apply hlamker
      have := congrArg (fun x : TAlg Tκ => x.coord k) h4
      simp only [TAlg.mapHom_coord, TAlg.coord_zero, Pi.zero_apply] at this
      exact this
    rw [TAlg.eq_sum_coord_smul_basis Tl (w - aeval yC q)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (h5 k) Submodule.mem_top

  obtain ⟨C', instC', instAlg, e', σ, he'0, hσalg, hσe⟩ :=
    Algebra.exists_lift_basis_of_surjective_of_monogenic_specialFibre R'l Rl πl hπls Cl
      (Fin (n + 1)) e 0 he0 ⟨yC, hmonoC⟩

  let T'' : Table R'l n := tableOfBasis e' he'0
  have hT''γ : ∀ i j k, T''.γ i j k = e'.repr (e' i * e' j) k := fun i j k => rfl
  have hσ_smul : ∀ (r : R'l) (x : C'), σ (r • x) = πl r • σ x := fun r x => by
    rw [Algebra.smul_def, map_mul, hσalg, ← Algebra.smul_def]

  have hπγ'' : ∀ i j k, πl (T''.γ i j k) = Tl.γ i j k := by
    intro i j k
    have h1 : e' i * e' j = ∑ m, T''.γ i j m • e' m := by
      conv_lhs => rw [← e'.sum_repr (e' i * e' j)]
      rfl
    have h2 : e i * e j = ∑ m, Tl.γ i j m • e m := by
      have := TAlg.eq_sum_coord_smul_basis Tl (e i * e j)
      rw [this]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [TAlg.basis_mul_basis_coord]
    have h3 : σ (e' i * e' j) = ∑ m, πl (T''.γ i j m) • e m := by
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [hσ_smul, hσe]
    rw [map_mul, hσe, hσe, h2] at h3
    have := congrArg (fun x => e.repr x k) h3
    simp only [repr_sum_smul] at this
    exact this.symm

  let γ'l : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → R'l := fun i j k =>
    algebraMap A'[X] R'l (γ' i j k)
  have hδ : ∀ i j k, ∃ z : R'l, T''.γ i j k - γ'l i j k = εl * z := by
    intro i j k
    apply hkerl
    rw [map_sub, hπγ'', hπl_alg]
    change algebraMap A[X] Rl (γ i j k) - algebraMap A[X] Rl ((γ' i j k).map π) = 0
    rw [hγ'π, sub_self]
  choose zδ hzδ using hδ
  let φl : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → R'l := fun i j k =>
    if i = 0 ∨ j = 0 then 0 else if i ≤ j then zδ i j k else zδ j i k
  have hγ'l1 : ∀ j k, γ'l 0 j k = if j = k then 1 else 0 := fun j k => by
    change algebraMap A'[X] R'l (γ' 0 j k) = _
    rw [hγ'1]; split_ifs <;> simp
  have hδ0 : ∀ j k, T''.γ 0 j k - γ'l 0 j k = 0 := fun j k => by
    rw [T''.unit, hγ'l1, sub_self]
  have hφl : ∀ i j k, T''.γ i j k - γ'l i j k = εl * φl i j k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · simp only [φl, if_pos h, mul_zero]
      rcases h with rfl | rfl
      · exact hδ0 j k
      · rw [T''.comm, show γ'l i 0 k = γ'l 0 i k from by
          change algebraMap A'[X] R'l (γ' i 0 k) = algebraMap A'[X] R'l (γ' 0 i k)
          rw [hγ'c]]
        exact hδ0 i k
    · simp only [φl, if_neg h]
      split_ifs with hij
      · exact hzδ i j k
      · rw [T''.comm, show γ'l i j k = γ'l j i k from by
          change algebraMap A'[X] R'l (γ' i j k) = algebraMap A'[X] R'l (γ' j i k)
          rw [hγ'c]]
        exact hzδ j i k
  have hφl0 : ∀ j k, φl 0 j k = 0 := fun j k => by simp [φl]
  have hφlc : ∀ i j k, φl i j k = φl j i k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · have h' : j = 0 ∨ i = 0 := h.symm
      simp only [φl, if_pos h, if_pos h']
    · have h' : ¬(j = 0 ∨ i = 0) := fun h' => h h'.symm
      simp only [φl, if_neg h, if_neg h']
      by_cases hij : i ≤ j
      · by_cases hji : j ≤ i
        · have : i = j := le_antisymm hij hji
          subst this; rfl
        · rw [if_pos hij, if_neg hji]
      · have hji : j ≤ i := le_of_not_ge hij
        rw [if_neg hij, if_pos hji]

  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite Q'.primeCompl
    (fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) => φl p.1 p.2.1 p.2.2)
  choose hint hhint using fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) => hu p
  let g : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    if i = 0 ∨ j = 0 then 0 else if i ≤ j then hint (i, j, k) else hint (j, i, k)
  have hg : ∀ i j k, algebraMap A'[X] R'l (g i j k) = algebraMap A'[X] R'l u * φl i j k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · simp only [g, φl, if_pos h, map_zero, mul_zero]
    · simp only [g, if_neg h]
      split_ifs with hij
      · rw [hhint (i, j, k), Algebra.smul_def]
      · rw [hhint (j, i, k), Algebra.smul_def, hφlc i j k]
  have hg0 : ∀ j k, g 0 j k = 0 := fun j k => by simp [g]
  have hgc : ∀ i j k, g i j k = g j i k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · have h' : j = 0 ∨ i = 0 := h.symm
      simp only [g, if_pos h, if_pos h']
    · have h' : ¬(j = 0 ∨ i = 0) := fun h' => h h'.symm
      simp only [g, if_neg h, if_neg h']
      by_cases hij : i ≤ j
      · by_cases hji : j ≤ i
        · have : i = j := le_antisymm hij hji
          subst this; rfl
        · rw [if_pos hij, if_neg hji]
      · have hji : j ≤ i := le_of_not_ge hij
        rw [if_neg hij, if_pos hji]

  let Γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    (u : A'[X]) * γ' i j k + C ε * g i j k
  have hΓ : ∀ i j k, algebraMap A'[X] R'l (Γ i j k) = algebraMap A'[X] R'l u * T''.γ i j k := by
    intro i j k
    have h1 : T''.γ i j k = γ'l i j k + εl * φl i j k := by rw [← hφl]; ring
    change algebraMap A'[X] R'l ((u : A'[X]) * γ' i j k + C ε * g i j k) = _
    rw [h1, map_add, map_mul, map_mul, hg]
    ring

  have hassocΓ : ∀ i j l m, algebraMap A'[X] R'l
      ((∑ k, Γ i j k * Γ k l m) - ∑ k, Γ j l k * Γ i k m) = 0 := by
    intro i j l m
    simp only [map_sub, map_sum, map_mul, hΓ]
    have := T''.assoc i j l m
    have e1 : ∑ k, algebraMap A'[X] R'l ↑u * T''.γ i j k * (algebraMap A'[X] R'l ↑u * T''.γ k l m) =
        (algebraMap A'[X] R'l ↑u) ^ 2 * ∑ k, T''.γ i j k * T''.γ k l m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, algebraMap A'[X] R'l ↑u * T''.γ j l k * (algebraMap A'[X] R'l ↑u * T''.γ i k m) =
        (algebraMap A'[X] R'l ↑u) ^ 2 * ∑ k, T''.γ j l k * T''.γ i k m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2, this, sub_self]

  let E : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    ((∑ k, γ' i j k * g k l m) + ∑ k, g i j k * γ' k l m) -
      ((∑ k, γ' j l k * g i k m) + ∑ k, g j l k * γ' i k m)
  let F : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    (∑ k, g i j k * g k l m) - ∑ k, g j l k * g i k m
  have hexp : ∀ i j l m, (∑ k, Γ i j k * Γ k l m) - (∑ k, Γ j l k * Γ i k m) =
      C ε * ((u : A'[X]) ^ 2 * ac i j l m + (u : A'[X]) * E i j l m + C ε * F i j l m) := by
    intro i j l m
    have hprod : ∀ x y z t : A'[X], ((u : A'[X]) * x + C ε * y) * ((u : A'[X]) * z + C ε * t) =
        (u : A'[X]) ^ 2 * (x * z) + C ε * ((u : A'[X]) * (x * t + y * z) + C ε * (y * t)) := by
      intro x y z t; ring
    have e1 : ∑ k, Γ i j k * Γ k l m = (u : A'[X]) ^ 2 * ∑ k, γ' i j k * γ' k l m +
        C ε * ((u : A'[X]) * ((∑ k, γ' i j k * g k l m) + ∑ k, g i j k * γ' k l m) +
          C ε * ∑ k, g i j k * g k l m) := by
      simp only [Γ, hprod, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    have e2 : ∑ k, Γ j l k * Γ i k m = (u : A'[X]) ^ 2 * ∑ k, γ' j l k * γ' i k m +
        C ε * ((u : A'[X]) * ((∑ k, γ' j l k * g i k m) + ∑ k, g j l k * γ' i k m) +
          C ε * ∑ k, g j l k * g i k m) := by
      simp only [Γ, hprod, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    rw [e1, e2]
    have h3 := hac i j l m
    simp only [E, F]
    linear_combination (u : A'[X]) ^ 2 * h3

  have hW : ∀ i j l m, θX ((u : A'[X]) ^ 2 * ac i j l m + (u : A'[X]) * E i j l m +
      C ε * F i j l m) = 0 := by
    intro i j l m
    apply hannl
    rw [← hexp]
    exact hassocΓ i j l m

  let su : K[X] := θX u
  let gb : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => θX (g i j k)
  have hsu : su ∉ P := by
    intro h
    apply u.2
    change (u : A'[X]) ∈ Q'
    rw [hmemQ']; exact h
  have hsu0 : su ≠ 0 := fun h => hsu (by rw [h]; exact P.zero_mem)
  have hθγ' : ∀ i j k, θX (γ' i j k) = b.repr (b i * b j) k := fun i j k => by
    rw [hθX]; change ((γ' i j k).map π).map ρ = _; rw [hγ'π, hγB]
  refine ⟨su, hsu, gb, fun j k => ?_, fun i j k => ?_, fun i j l m => ?_⟩
  · change θX (g 0 j k) = 0; rw [hg0, map_zero]
  · change θX (g i j k) = θX (g j i k); rw [hgc]
  · have h := hW i j l m
    simp only [map_add, map_mul, map_pow, map_sub, map_sum, hθε, zero_mul, add_zero, hθγ', E]
      at h
    change (∑ k, gb j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * gb k l m) +
        (∑ k, b.repr (b j * b l) k * gb i k m) - (∑ k, gb i j k * b.repr (b k * b l) m) =
      su * (ac i j l m).map (ρ.comp π)
    have ha : (ac i j l m).map (ρ.comp π) = θX (ac i j l m) := rfl
    rw [ha]
    apply mul_left_cancel₀ hsu0
    have h' : su * (su * θX (ac i j l m)) = -(su * (((∑ k, b.repr (b i * b j) k * gb k l m) +
        ∑ k, gb i j k * b.repr (b k * b l) m) - ((∑ k, b.repr (b j * b l) k * gb i k m) +
          ∑ k, gb j l k * b.repr (b i * b k) m))) := by
      have : su ^ 2 * θX (ac i j l m) + su * (((∑ k, b.repr (b i * b j) k * gb k l m) +
        ∑ k, gb i j k * b.repr (b k * b l) m) - ((∑ k, b.repr (b j * b l) k * gb i k m) +
          ∑ k, gb j l k * b.repr (b i * b k) m)) = 0 := h
      linear_combination this
    rw [h']
    ring

end Main
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table"

end LocCobSol
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.TAlg P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol.Table P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.LocCobSol"

theorem solution
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (P : Ideal K[X]) (hP : P.IsMaximal)
    (hmono : ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X],
      z - aeval y q ∈ P • (⊤ : Submodule K[X] B)) :
    ∃ s : K[X], s ∉ P ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        s * (ac i j l m).map (ρ.comp π) :=
  LocCobSol.main b hb0 A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa hγB γ' hγ'1 hγ'c hγ'π ac hac P hP
    hmono

end S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre
end P2MW
export P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre (solution)
