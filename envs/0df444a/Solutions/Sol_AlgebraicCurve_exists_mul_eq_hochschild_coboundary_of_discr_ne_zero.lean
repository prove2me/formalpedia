-- Prove2me | solution 1 for AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b50999bd-a15d-54b8-9b24-e6d38c0f148b

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open scoped nonZeroDivisors

universe u v

noncomputable section

namespace GenH2Sol

section Coord

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

theorem cst_single_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i : Fin (N + 1))
    (y : Fin (N + 1) → R) (m : Fin (N + 1)) :
    cst γ (Pi.single i 1) y m = ∑ q, y q * γ i q m := by
  rw [cst_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cst_single_single (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j : Fin (N + 1)) :
    cst γ (Pi.single i 1) (Pi.single j 1) = fun m => γ i j m := by
  funext m
  rw [cst_single_left, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

def D1 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) : R :=
  (∑ k, lam j k * γ i k m) - (∑ k, γ i j k * lam k m) + (∑ k, lam i k * γ k j m)

def D2 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) : R :=
  (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) + (∑ k, γ j l k * φ i k m) -
    (∑ k, φ i j k * γ k l m)

theorem D1_smul (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (c : R)
    (lam : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (c • lam) i j m = c * D1 γ lam i j m := by
  simp only [D1, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_sub]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact Finset.sum_congr rfl fun k _ => by ring

theorem D1_neg (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (lam : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (-lam) i j m = -D1 γ lam i j m := by
  have := D1_smul γ (-1) lam i j m
  simpa using this

theorem D1_map {R' : Type*} [CommRing R'] (f : R →+* R')
    (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) :
    f (D1 γ lam i j m) = D1 (fun i j k => f (γ i j k)) (fun i m => f (lam i m)) i j m := by
  simp only [D1, map_add, map_sub, map_sum, map_mul]

theorem D2_map {R' : Type*} [CommRing R'] (f : R →+* R')
    (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    f (D2 γ φ i j l m) = D2 (fun i j k => f (γ i j k)) (fun i j k => f (φ i j k)) i j l m := by
  simp only [D2, map_add, map_sub, map_sum, map_mul]

theorem hd2_expand (γ φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (X Y Z : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γ X (cst φ Y Z) s - cst φ (cst γ X Y) Z s + cst φ X (cst γ Y Z) s -
        cst γ (cst φ X Y) Z s =
      ∑ k, ∑ l, ∑ t, X k * Y l * Z t * D2 γ φ k l t s := by
  simp only [cst_cst_left, cst_cst_right, D2, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

end Coord

section Based

variable {L : Type*} [Field L] {F : Type*} [CommRing F] [Algebra L F] {N : ℕ}
  (bF : Module.Basis (Fin (N + 1)) L F)
  (γL : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → L)
  (hγL : ∀ i j m, bF.repr (bF i * bF j) m = γL i j m)

theorem repr_sum_smul (c : Fin (N + 1) → L) (m : Fin (N + 1)) :
    bF.repr (∑ k, c k • bF k) m = c m := by
  rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single m]
  · rw [map_smul, Finsupp.smul_apply, bF.repr_self, Finsupp.single_apply, if_pos rfl, smul_eq_mul,
      mul_one]
  · intro k _ hk
    rw [map_smul, Finsupp.smul_apply, bF.repr_self, Finsupp.single_apply, if_neg hk, smul_zero]
  · intro h; exact absurd (Finset.mem_univ m) h

theorem repr_basis_eq_single (i : Fin (N + 1)) :
    (fun k => bF.repr (bF i) k) = (Pi.single i 1 : Fin (N + 1) → L) := by
  funext k
  rw [bF.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : k = i
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

include hγL in
theorem repr_mul (x y : F) (m : Fin (N + 1)) :
    bF.repr (x * y) m = cst γL (fun i => bF.repr x i) (fun j => bF.repr y j) m := by
  have hx : x = ∑ i, bF.repr x i • bF i := (bF.sum_repr x).symm
  have hy : y = ∑ j, bF.repr y j • bF j := (bF.sum_repr y).symm
  conv_lhs => rw [hx, hy, Finset.sum_mul_sum]
  rw [map_sum, Finsupp.finsetSum_apply, cst_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, hγL, smul_eq_mul]

def Ψf (ψL : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → L) (x y : F) : F :=
  ∑ m, cst ψL (fun i => bF.repr x i) (fun j => bF.repr y j) m • bF m

variable (ψL : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → L)

theorem Ψf_repr (x y : F) (m : Fin (N + 1)) :
    bF.repr (Ψf bF ψL x y) m = cst ψL (fun i => bF.repr x i) (fun j => bF.repr y j) m :=
  repr_sum_smul bF _ m

theorem Ψf_add_left (x₁ x₂ y : F) : Ψf bF ψL (x₁ + x₂) y = Ψf bF ψL x₁ y + Ψf bF ψL x₂ y := by
  unfold Ψf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← add_smul]
  congr 1
  simp only [cst_apply, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem Ψf_smul_left (c : L) (x y : F) : Ψf bF ψL (c • x) y = c • Ψf bF ψL x y := by
  unfold Ψf
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul]
  congr 1
  simp only [cst_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem Ψf_symm (hψLc : ∀ i j k, ψL i j k = ψL j i k) (x y : F) :
    Ψf bF ψL x y = Ψf bF ψL y x := by
  unfold Ψf
  rw [cst_comm_of ψL hψLc (fun i => bF.repr x i) (fun j => bF.repr y j)]

def ΨL (hψLc : ∀ i j k, ψL i j k = ψL j i k) : F →ₗ[L] F →ₗ[L] F :=
  LinearMap.mk₂ L (Ψf bF ψL) (Ψf_add_left bF ψL) (Ψf_smul_left bF ψL)
    (fun x y₁ y₂ => by
      rw [Ψf_symm bF ψL hψLc, Ψf_add_left, Ψf_symm bF ψL hψLc y₁, Ψf_symm bF ψL hψLc y₂])
    (fun c x y => by rw [Ψf_symm bF ψL hψLc, Ψf_smul_left, Ψf_symm bF ψL hψLc])

theorem ΨL_apply (hψLc : ∀ i j k, ψL i j k = ψL j i k) (x y : F) :
    ΨL bF ψL hψLc x y = Ψf bF ψL x y := rfl

theorem ΨL_one (hψLc : ∀ i j k, ψL i j k = ψL j i k) (hone : bF 0 = 1)
    (hψL1 : ∀ j k, ψL 0 j k = 0) (y : F) : ΨL bF ψL hψLc 1 y = 0 := by
  apply bF.repr.injective
  ext m
  rw [ΨL_apply, Ψf_repr, map_zero, Finsupp.zero_apply, ← hone, repr_basis_eq_single,
    cst_single_left]
  exact Finset.sum_eq_zero fun q _ => by rw [hψL1, mul_zero]

include hγL in
theorem ΨL_coc (hψLc : ∀ i j k, ψL i j k = ψL j i k) (hγLc : ∀ i j k, γL i j k = γL j i k)
    (hD2 : ∀ i j l m, D2 γL ψL i j l m = 0) (x y z : F) :
    x • ΨL bF ψL hψLc y z - ΨL bF ψL hψLc (x * y) z + ΨL bF ψL hψLc x (y * z) -
      z • ΨL bF ψL hψLc x y = 0 := by
  apply bF.repr.injective
  ext s
  simp only [smul_eq_mul, map_sub, map_add, map_zero, Finsupp.sub_apply, Finsupp.add_apply,
    Finsupp.zero_apply, ΨL_apply]
  rw [repr_mul bF γL hγL, repr_mul bF γL hγL, Ψf_repr, Ψf_repr]
  have e1 : (fun j => bF.repr (Ψf bF ψL y z) j) =
      cst ψL (fun i => bF.repr y i) (fun j => bF.repr z j) := funext fun j => Ψf_repr bF ψL y z j
  have e2 : (fun i => bF.repr (x * y) i) = cst γL (fun i => bF.repr x i) (fun j => bF.repr y j) :=
    funext fun j => repr_mul bF γL hγL x y j
  have e3 : (fun j => bF.repr (y * z) j) = cst γL (fun i => bF.repr y i) (fun j => bF.repr z j) :=
    funext fun j => repr_mul bF γL hγL y z j
  have e4 : (fun j => bF.repr (Ψf bF ψL x y) j) =
      cst ψL (fun i => bF.repr x i) (fun j => bF.repr y j) := funext fun j => Ψf_repr bF ψL x y j
  rw [e1, e2, e3, e4, cst_comm_of γL hγLc (fun i => bF.repr z i), hd2_expand]
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ =>
    Finset.sum_eq_zero fun t _ => by rw [hD2, mul_zero]

include hγL in

theorem key (hψLc : ∀ i j k, ψL i j k = ψL j i k) (hγLc : ∀ i j k, γL i j k = γL j i k)
    (l : F →ₗ[L] F)
    (hl : ∀ x y, ΨL bF ψL hψLc x y = l (x * y) - x • l y - y • l x) (i j m : Fin (N + 1)) :
    ψL i j m = -D1 γL (fun i m => bF.repr (l (bF i)) m) i j m := by
  have h := congrArg (fun w => bF.repr w m) (hl (bF i) (bF j))
  have lhs : bF.repr (ΨL bF ψL hψLc (bF i) (bF j)) m = ψL i j m := by
    rw [ΨL_apply, Ψf_repr, repr_basis_eq_single, repr_basis_eq_single, cst_single_single]
  have hbb : bF i * bF j = ∑ k, γL i j k • bF k := by
    conv_lhs => rw [← bF.sum_repr (bF i * bF j)]
    exact Finset.sum_congr rfl fun k _ => by rw [hγL]
  have t1 : bF.repr (l (bF i * bF j)) m = ∑ k, γL i j k * bF.repr (l (bF k)) m := by
    rw [hbb, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have t2 : bF.repr (bF i • l (bF j)) m = ∑ q, bF.repr (l (bF j)) q * γL i q m := by
    rw [smul_eq_mul, repr_mul bF γL hγL, repr_basis_eq_single, cst_single_left]
  have t3 : bF.repr (bF j • l (bF i)) m = ∑ q, bF.repr (l (bF i)) q * γL q j m := by
    rw [smul_eq_mul, repr_mul bF γL hγL, repr_basis_eq_single, cst_single_left]
    exact Finset.sum_congr rfl fun q _ => by rw [hγLc]
  simp only [map_sub, Finsupp.sub_apply] at h
  rw [lhs, t1, t2, t3] at h
  rw [h, D1]
  ring

end Based

section Main

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {K : Type u} [Field K] {n : ℕ} {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Algebra K[X] B]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (hdisc : Algebra.discr K[X] b ≠ 0)
    (ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hψ1 : ∀ j k, ψ 0 j k = 0) (hψc : ∀ i j k, ψ i j k = ψ j i k)
    (hψa : ∀ i j l m, D2 (fun i j k => b.repr (b i * b j) k) ψ i j l m = 0) :
    ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
      ∀ i j m, u * ψ i j m = D1 (fun i j k => b.repr (b i * b j) k) lam i j m := by
  classical

  let L := FractionRing K[X]
  let F := FractionRing B
  haveI : Module.Finite K[X] B := Module.Finite.of_basis b
  haveI : Module.Free K[X] B := Module.Free.of_basis b
  have hinjB : Function.Injective (algebraMap K[X] B) := by
    intro f g hfg
    have h1 : ∀ f : K[X], b.repr (algebraMap K[X] B f) 0 = f := fun f => by
      rw [Algebra.algebraMap_eq_smul_one, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rw [← h1 f, ← h1 g, hfg]
  haveI : FaithfulSMul K[X] B := (faithfulSMul_iff_algebraMap_injective K[X] B).2 hinjB
  haveI : Algebra.IsIntegral K[X] B := inferInstance
  haveI : IsIntegralClosure B K[X] F := IsIntegralClosure.of_isIntegrallyClosed B K[X] F
  haveI : Algebra.IsAlgebraic L F := isAlgebraic_of_isFractionRing (R := K[X]) (S := B) L F
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid B K[X]⁰) F :=
    IsIntegralClosure.isLocalization K[X] L F B
  let bF : Module.Basis (Fin (n + 1)) L F := b.localizationLocalization L K[X]⁰ F
  have hbF : ∀ i, bF i = algebraMap B F (b i) := fun i =>
    Module.Basis.localizationLocalization_apply L K[X]⁰ F b i
  have hbFrepr : ∀ (x : B) (i : Fin (n + 1)), bF.repr (algebraMap B F x) i =
      algebraMap K[X] L (b.repr x i) := fun x i =>
    Module.Basis.localizationLocalization_repr_algebraMap L K[X]⁰ F b x i
  haveI : FiniteDimensional L F := Module.Finite.of_basis bF

  have hdiscL : Algebra.discr L bF ≠ 0 := by
    rw [Algebra.discr_localizationLocalization K[X] K[X]⁰ F b]
    exact fun h => hdisc ((IsFractionRing.injective K[X] L) (by rw [h, map_zero]))
  have hnondeg : (Algebra.traceForm L F).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (Algebra.traceForm L F) bF
    rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
    exact hdiscL
  haveI : Algebra.IsSeparable L F := ((traceForm_nondegenerate_tfae L F).out 0 2).2 hnondeg
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable L F

  let γL : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L := fun i j k =>
    algebraMap K[X] L (b.repr (b i * b j) k)
  let ψL : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L := fun i j k => algebraMap K[X] L (ψ i j k)
  have hγL : ∀ i j m, bF.repr (bF i * bF j) m = γL i j m := fun i j m => by
    rw [hbF, hbF, ← map_mul, hbFrepr]
  have hγLc : ∀ i j k, γL i j k = γL j i k := fun i j k => by
    change algebraMap K[X] L (b.repr (b i * b j) k) = algebraMap K[X] L (b.repr (b j * b i) k)
    rw [mul_comm]
  have hψLc : ∀ i j k, ψL i j k = ψL j i k := fun i j k => by
    change algebraMap K[X] L (ψ i j k) = algebraMap K[X] L (ψ j i k)
    rw [hψc]
  have hψL1 : ∀ j k, ψL 0 j k = 0 := fun j k => by
    change algebraMap K[X] L (ψ 0 j k) = 0
    rw [hψ1, map_zero]
  have hD2L : ∀ i j l m, D2 γL ψL i j l m = 0 := fun i j l m => by
    have := congrArg (algebraMap K[X] L) (hψa i j l m)
    rw [D2_map, map_zero] at this
    exact this
  have hbF0 : bF 0 = 1 := by rw [hbF, hb0, map_one]

  obtain ⟨l, hl1, hl⟩ :=
    Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle L F F
      (ΨL bF ψL hψLc) (fun x y => by rw [ΨL_apply, ΨL_apply, Ψf_symm bF ψL hψLc])
      (ΨL_one bF ψL hψLc hbF0 hψL1) (ΨL_coc bF γL hγL ψL hψLc hγLc hD2L)
  have hkey := key bF γL hγL ψL hψLc hγLc l hl
  set lamL : Fin (n + 1) → Fin (n + 1) → L := fun i m => bF.repr (l (bF i)) m with hlamLdef
  have hlamL0 : ∀ m, lamL 0 m = 0 := fun m => by
    change bF.repr (l (bF 0)) m = 0
    rw [hbF0, hl1, map_zero, Finsupp.zero_apply]

  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite K[X]⁰
    (fun p : Fin (n + 1) × Fin (n + 1) => -lamL p.1 p.2)
  choose lamf hlamf using fun p : Fin (n + 1) × Fin (n + 1) => hu p
  let lam : Fin (n + 1) → Fin (n + 1) → K[X] := fun i m => lamf (i, m)
  have hlam : ∀ i m, algebraMap K[X] L (lam i m) = (u : K[X]) • (-lamL i m) := fun i m =>
    hlamf (i, m)
  have hu0 : (u : K[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero u
  refine ⟨u, hu0, lam, fun m => ?_, fun i j m => ?_⟩
  · apply IsFractionRing.injective K[X] L
    rw [hlam, hlamL0, neg_zero, smul_zero, map_zero]
  · apply IsFractionRing.injective K[X] L
    rw [map_mul, D1_map]
    have hlam' : (fun i m => algebraMap K[X] L (lam i m)) = ((algebraMap K[X] L u) • (-lamL)) := by
      funext i m
      rw [hlam, Pi.smul_apply, Pi.smul_apply, Pi.neg_apply, Pi.neg_apply, Algebra.smul_def,
        smul_eq_mul]
    rw [hlam', D1_smul, D1_neg]
    change algebraMap K[X] L u * ψL i j m = _
    rw [hkey i j m]

end Main

end GenH2Sol

end

theorem solution
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (hdisc : Algebra.discr K[X] b ≠ 0)
    (ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hψ1 : ∀ j k, ψ 0 j k = 0) (hψc : ∀ i j k, ψ i j k = ψ j i k)
    (hψa : ∀ i j l m, (∑ k, ψ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * ψ k l m) +
        (∑ k, b.repr (b j * b l) k * ψ i k m) - (∑ k, ψ i j k * b.repr (b k * b l) m) = 0) :
    ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
      ∀ i j m, u * ψ i j m = (∑ k, lam j k * b.repr (b i * b k) m) -
        (∑ k, b.repr (b i * b j) k * lam k m) + (∑ k, lam i k * b.repr (b k * b j) m) :=
  GenH2Sol.main b hb0 hdisc ψ hψ1 hψc hψa

end S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero (solution)
