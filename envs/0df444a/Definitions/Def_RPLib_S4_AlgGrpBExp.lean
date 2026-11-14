-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBExp
-- name    : RPLib_S4_AlgGrpBExp
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:39:43.368081+00:00
-- url     : https://prove2.me/theorems/238c36b8-1e72-4824-9da4-140df1bf6be2
-- title:
--   Larsen's alternative library: unipotent one-parameter subgroups, first half)
-- statement:
--   Char 0. If `H ⊆ GL_n(K)` is a subgroup, `N ∈ Lie H` and `N * N = 0`, then `1 + t N` lies in the
--   Zariski closure of `H` for every `t : K` (`unip_mem_closure`), hence in `H` when `H` is closed
--   (`unip_mem`).
--
--   Proof: the left-invariant derivation `derN N` (`f ↦ d/ds f(g (1 + s N))` at `s = 0`) preserves the
--   ideal `vanI H` (`derN_mem_vanI`, via `K[ε]`-points of left translates); along the curve
--   `t ↦ 1 + t N` it is `d/dt` (`derivative_aeval_curve`); so every Taylor coefficient at `0` of
--   `t ↦ f(1 + t N)` vanishes for `f ∈ vanI H`, and in char 0 that polynomial is `0`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBFin

/-!
# S4-AlgGrpB, file Exp: unipotent one-parameter subgroups (spike API (A4), first half)

Char 0. If `H ⊆ GL_n(K)` is a subgroup, `N ∈ Lie H` and `N * N = 0`, then `1 + t N` lies in the
Zariski closure of `H` for every `t : K` (`unip_mem_closure`), hence in `H` when `H` is closed
(`unip_mem`).

Proof: the left-invariant derivation `derN N` (`f ↦ d/ds f(g (1 + s N))` at `s = 0`) preserves the
ideal `vanI H` (`derN_mem_vanI`, via `K[ε]`-points of left translates); along the curve
`t ↦ 1 + t N` it is `d/dt` (`derivative_aeval_curve`); so every Taylor coefficient at `0` of
`t ↦ f(1 + t N)` vanishes for `f ∈ vanI H`, and in char 0 that polynomial is `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Coordinates of the left-invariant vector field `g ↦ g N` (in the coordinates `(g, g⁻¹)`). -/
def dN (N : Matrix n n K) : Var n → MvPolynomial (Var n) K :=
  Sum.elim (fun ij => ∑ k, X (Sum.inl (ij.1, k)) * C (N k ij.2))
    (fun ij => ∑ k, C ((-N) ij.1 k) * X (Sum.inr (k, ij.2)))

/-- The left-invariant derivation `f ↦ Σ_v ∂_v f · dN v`. -/
def derN (N : Matrix n n K) (f : MvPolynomial (Var n) K) : MvPolynomial (Var n) K :=
  ∑ v, pderiv v f * dN N v

/-- Polynomials giving the coordinates of `h g` in terms of those of `g`. -/
def leftPoly (h : Matrix.GeneralLinearGroup n K) : Var n → MvPolynomial (Var n) K :=
  Sum.elim (fun ij => ∑ k, C ((h : Matrix n n K) ij.1 k) * X (Sum.inl (k, ij.2)))
    (fun ij => ∑ k, C (((h⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) k ij.2) *
      X (Sum.inr (ij.1, k)))

theorem eval_leftPoly (h g : Matrix.GeneralLinearGroup n K) (v : Var n) :
    eval (crd g) (leftPoly h v) = crd (h * g) v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp [leftPoly, Matrix.mul_apply]
  · simp [leftPoly, Matrix.mul_apply, mul_inv_rev, mul_comm]

theorem eval_derN (N : Matrix n n K) (h : Matrix.GeneralLinearGroup n K)
    (f : MvPolynomial (Var n) K) :
    eval (crd h) (derN N f) = dirDeriv (crd h) (fun v => eval (crd h) (dN N v)) f := by
  simp [derN, dirDeriv]

theorem aeval_ptD_leftPoly (N : Matrix n n K) (h : Matrix.GeneralLinearGroup n K) (v : Var n) :
    aeval (ptD N) (leftPoly h v) = dpt (crd h) (fun v => eval (crd h) (dN N v)) v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · ext
    · simp [leftPoly, aeval_C_mul_X, TrivSqZeroExt.fst_sum, ptD, dpt, Matrix.one_apply]
    · simp [leftPoly, dN, aeval_C_mul_X, TrivSqZeroExt.snd_sum, ptD, dpt]
  · ext
    · simp [leftPoly, aeval_C_mul_X, TrivSqZeroExt.fst_sum, ptD, dpt, Matrix.one_apply]
    · simp [leftPoly, dN, TrivSqZeroExt.snd_sum, ptD, dpt, TrivSqZeroExt.algebraMap_eq_inl,
        Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The left-invariant derivation along `N ∈ Lie H` preserves the ideal of `H`. -/
theorem derN_mem_vanI {H : Subgroup (Matrix.GeneralLinearGroup n K)} {N : Matrix n n K}
    (hN : N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) {f : MvPolynomial (Var n) K}
    (hf : f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K))) :
    derN N f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K)) := by
  refine mem_vanI.2 fun h hh => ?_
  have hb : bind₁ (leftPoly h) f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K)) := by
    refine mem_vanI.2 fun g hg => ?_
    rw [eval_bind₁']
    have : (fun v => eval (crd g) (leftPoly h v)) = crd (h * g) := funext (eval_leftPoly h g)
    rw [this]
    exact mem_vanI.1 hf _ (H.mul_mem hh hg)
  have h2 := hN _ hb
  rw [← snd_aeval_ptD, aeval_bind₁] at h2
  have : (fun v => aeval (ptD N) (leftPoly h v)) = dpt (crd h) (fun v => eval (crd h) (dN N v)) :=
    funext (aeval_ptD_leftPoly N h)
  rw [this, snd_aeval_dpt] at h2
  rw [eval_derN]
  exact h2

theorem derN_iterate_mem_vanI {H : Subgroup (Matrix.GeneralLinearGroup n K)} {N : Matrix n n K}
    (hN : N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) {f : MvPolynomial (Var n) K}
    (hf : f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K))) (k : ℕ) :
    (derN N)^[k] f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K)) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact derN_mem_vanI hN ih

theorem derN_add (N : Matrix n n K) (p q : MvPolynomial (Var n) K) :
    derN N (p + q) = derN N p + derN N q := by
  simp [derN, add_mul, Finset.sum_add_distrib]

theorem derN_C (N : Matrix n n K) (a : K) : derN N (C a) = 0 := by
  simp [derN]

theorem derN_mul_X (N : Matrix n n K) (p : MvPolynomial (Var n) K) (v : Var n) :
    derN N (p * X v) = derN N p * X v + p * dN N v := by
  have key : ∀ u, pderiv u (p * X v) * dN N u =
      pderiv u p * dN N u * X v + (if u = v then p * dN N v else 0) := by
    intro u
    rw [Derivation.leibniz, pderiv_X]
    by_cases h : u = v
    · subst h
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
      ring
    · rw [Pi.single_eq_of_ne (Ne.symm h)]
      simp only [smul_eq_mul, h, if_false]
      ring
  simp only [derN, key, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The curve `t ↦ 1 + t N` in coordinates, as polynomials in `t`. -/
def curvePt (N : Matrix n n K) : Var n → Polynomial K :=
  fun v => Polynomial.C (crd 1 v) + Polynomial.X * Polynomial.C (dvec N v)

theorem aeval_curve_dN (N : Matrix n n K) (hN : N * N = 0) (v : Var n) :
    aeval (curvePt N) (dN N v) = Polynomial.C (dvec N v) := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · have e : ∑ k, (Polynomial.C ((1 : Matrix n n K) i k) + Polynomial.X * Polynomial.C (N i k)) *
        Polynomial.C (N k j) =
        Polynomial.C (((1 : Matrix n n K) * N) i j) + Polynomial.X * Polynomial.C ((N * N) i j) := by
      simp only [Matrix.mul_apply, map_sum, Polynomial.C_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [dN, Sum.elim_inl, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq,
      curvePt, crd_inl, Units.val_one, dvec_inl]
    rw [e, hN, Matrix.one_mul, Matrix.zero_apply, map_zero, mul_zero, add_zero]
  · have e : ∑ k, Polynomial.C ((-N) i k) * (Polynomial.C ((1 : Matrix n n K) k j) +
        Polynomial.X * Polynomial.C ((-N) k j)) =
        Polynomial.C ((-N * (1 : Matrix n n K)) i j) +
          Polynomial.X * Polynomial.C ((-N * -N : Matrix n n K) i j) := by
      simp only [Matrix.mul_apply, map_sum, Polynomial.C_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [dN, Sum.elim_inr, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq,
      curvePt, crd_inr, inv_one, Units.val_one, dvec_inr]
    have e2 : ∀ k, -N k j = (-N) k j := fun k => (Matrix.neg_apply N k j).symm
    simp only [e2]
    rw [e, neg_mul_neg, hN, Matrix.mul_one, Matrix.zero_apply, map_zero, mul_zero, add_zero,
      Matrix.neg_apply]

theorem derivative_aeval_curve (N : Matrix n n K) (hN : N * N = 0) (f : MvPolynomial (Var n) K) :
    Polynomial.derivative (aeval (curvePt N) f) = aeval (curvePt N) (derN N f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [derN_C]
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, hp, hq, derN_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, derN_mul_X, map_add, map_mul, map_mul, aeval_X,
      aeval_curve_dN N hN]
    simp [curvePt]

theorem iterate_derivative_aeval_curve (N : Matrix n n K) (hN : N * N = 0)
    (f : MvPolynomial (Var n) K) (k : ℕ) :
    Polynomial.derivative^[k] (aeval (curvePt N) f) = aeval (curvePt N) ((derN N)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_aeval_curve N hN,
      ← Function.iterate_succ_apply' (derN N)]

theorem eval_aeval_curve (N : Matrix n n K) (t : K) (f : MvPolynomial (Var n) K) :
    Polynomial.eval t (aeval (curvePt N) f) = eval (fun v => crd 1 v + t * dvec N v) f := by
  rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
  have : (fun v => Polynomial.aeval t (curvePt N v)) = fun v => crd 1 v + t * dvec N v :=
    funext fun v => by
      simp [curvePt]
      ring
  rw [this]
  rfl

/-- `1 + t N` as an element of `GL_n(K)` when `N * N = 0` (inverse `1 - t N`). -/
def unip (N : Matrix n n K) (hN : N * N = 0) (t : K) : Matrix.GeneralLinearGroup n K where
  val := 1 + t • N
  inv := 1 - t • N
  val_inv := by
    simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero]
    abel

theorem val_unip (N : Matrix n n K) (hN : N * N = 0) (t : K) :
    ((unip N hN t : Matrix.GeneralLinearGroup n K) : Matrix n n K) = 1 + t • N := rfl

theorem crd_unip (N : Matrix n n K) (hN : N * N = 0) (t : K) :
    crd (unip N hN t) = fun v => crd 1 v + t * dvec N v := by
  funext v
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp [unip]
  · change (1 - t • N) i j = _
    simp [sub_eq_add_neg]

attribute [local instance] zarTop in
/-- `(A4)`, unipotent step (char 0): `N ∈ Lie H` with `N² = 0` gives `1 + t N ∈ closure H`. -/
theorem unip_mem_closure [CharZero K] {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    {N : Matrix n n K} (hNN : N * N = 0) (hN : N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (t : K) : unip N hNN t ∈ closure (H : Set (Matrix.GeneralLinearGroup n K)) := by
  rw [closure_eq_zeroS_vanI]
  refine mem_zeroS.2 fun f hf => ?_
  have hzero : aeval (curvePt N) f = 0 := by
    ext k
    have h1 := congrArg (fun p => Polynomial.coeff p 0)
      (iterate_derivative_aeval_curve N hNN f k)
    rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_zero_eq_eval_zero,
      eval_aeval_curve] at h1
    have h2 : eval (fun v => crd 1 v + 0 * dvec N v) ((derN N)^[k] f) = 0 := by
      simp only [zero_mul, add_zero]
      exact mem_vanI.1 (derN_iterate_mem_vanI hN hf k) 1 H.one_mem
    rw [h2, zero_add, Nat.descFactorial_self, nsmul_eq_mul, mul_eq_zero] at h1
    rw [Polynomial.coeff_zero]
    rcases h1 with h1 | h1
    · exact absurd h1 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))
    · exact h1
  rw [crd_unip, ← eval_aeval_curve N t f, hzero, Polynomial.eval_zero]

attribute [local instance] zarTop in
/-- `(A4)`, unipotent step for a Zariski-closed subgroup: `1 + t N ∈ H`. -/
theorem unip_mem [CharZero K] {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K))) {N : Matrix n n K}
    (hNN : N * N = 0) (hN : N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) (t : K) :
    unip N hNN t ∈ H := by
  have := unip_mem_closure hNN hN t
  rwa [hH.closure_eq] at this

end RamanujanPetersson.AlgGrpB


