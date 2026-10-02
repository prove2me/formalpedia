-- Prove2me | Definitions.Def_ChapterWeylSL2Unipotent
-- name    : ChapterWeylSL2Unipotent
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:28:17.669619+00:00
-- url     : https://prove2.me/theorems/5eb49e8d-ec44-4123-a11e-b52f575dd764
-- title:
--   Chapter WeylSL2Unipotent
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWeylSL2Unipotent.lean`): generated def bundle for ChapterWeylSL2Unipotent. See BookProof/ChapterWeylSL2Unipotent.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeylSL2Unipotent.lean

import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterWeylSL2Group
import Mathlib


/-!
# The `sl₂`-triple of a unipotent representation of `SL(2,ℂ)`

`BookProof.ChapterWeylSL2Group` proves Weyl's complete reducibility theorem for
representations of `SL(2,ℂ)` which act on the two unipotent one-parameter subgroups by the
exponential series of an **`sl₂`-triple** `(E, F, H)`.  That hypothesis assumed the
commutation relations.  This file removes the assumption: only the *unipotence* of the two
one-parameter subgroups is assumed,

`rho (uPlus t) = ∑_{k<N} (tᵏ/k!) • Eᵏ`,  `rho (uMinus t) = ∑_{k<N} (tᵏ/k!) • Fᵏ`,
`E^N = 0`, `F^N = 0`,

with **no relation whatsoever** between `E` and `F`, and the `sl₂` relations

`[H, E] = 2E`,  `[H, F] = -2F` with `H = [E, F]`

are *derived* from the group law of `SL(2,ℂ)`.

## The argument

Write `d(a) = diag(a, a⁻¹)`.  The Bruhat-type identity
`d(a) = u₊(a) u₋(-a⁻¹) u₊(a) w₁⁻¹` shows that `a^(N-1) • rho (d a)` is the value at `a` of
an honest polynomial `dPoly` with coefficients in `End V` (`evalA_dPoly`).  Two families of
identities in `SL(2,ℂ)` are then turned into identities of polynomials, using that a
polynomial over `End V` is determined by its values at the nonzero complex numbers
(`ext_of_evalA_eq`):

* `d(a) u₊(t) = u₊(a²t) d(a)` gives `dPoly * C E = C E * dPoly * X²`, and differentiating
  this identity at `a = 1` gives `[H₀, E] = 2E` for `H₀ := (derivative dPoly).eval 1`
  (`cartan_commutator_E`); likewise `[H₀, F] = -2F`;
* the big-cell identity `u₋(s) u₊(s) = u₊(sc) d(c) u₋(sc)` with `c = (1+s²)⁻¹`, compared in
  the coefficient of `s²`, gives `H₀ = EF - FE + (N-1)` (`cartan_eq_commutator`).

Hence `(E, F, EF - FE)` is an `sl₂`-triple (`sl2Rep_of_unipotent`), and Weyl's theorem for
the group follows (`weyl_complete_reducibility_SL2_unipotent`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterWeylSL2Unipotent

open BookProof.ChapterWeylSl2 BookProof.ChapterWeylSL2Group
open Polynomial

universe u

/-! ## Coefficients of a polynomial curve in a complex vector space -/

section Extraction

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A polynomial curve in a complex vector space which vanishes at every nonzero complex
number has vanishing coefficients. -/
theorem eq_zero_of_curve_eq_zero {N : ℕ} {c : ℕ → M} {S : Set ℂ} (hS : S.Finite)
    (h : ∀ t : ℂ, t ∉ S → ∑ k ∈ Finset.range N, t ^ k • c k = 0) {k : ℕ} (hk : k < N) :
    c k = 0 := by
  by_contra hcon
  obtain ⟨mu, hmu⟩ := Module.Projective.exists_dual_eq_one ℂ hcon
  set P : Polynomial ℂ := ∑ j ∈ Finset.range N, Polynomial.C (mu (c j)) * Polynomial.X ^ j
    with hP
  have hroot : ∀ t : ℂ, t ∉ S → P.eval t = 0 := by
    intro t ht
    have h1 : P.eval t = ∑ j ∈ Finset.range N, mu (c j) * t ^ j := by
      rw [hP, Polynomial.eval_finset_sum]
      exact Finset.sum_congr rfl fun j _ => by simp
    have h2 : ∑ j ∈ Finset.range N, mu (c j) * t ^ j
        = mu (∑ j ∈ Finset.range N, t ^ j • c j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
    rw [h1, h2, h t ht, map_zero]
  have hinf : {x : ℂ | P.IsRoot x}.Infinite := by
    refine Set.Infinite.mono (s := (S : Set ℂ)ᶜ) ?_ ?_
    · intro x hx
      exact hroot x hx
    · exact hS.infinite_compl
  have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
  have hcoeff : P.coeff k = mu (c k) := by
    rw [hP, Polynomial.finset_sum_coeff, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Polynomial.coeff_X_pow, Ne.symm hj]
    · intro hk'
      exact absurd (Finset.mem_range.mpr hk) hk'
  rw [hP0, Polynomial.coeff_zero, hmu] at hcoeff
  exact zero_ne_one hcoeff

/-- Two polynomial curves in a complex vector space which agree at every nonzero complex
number have the same coefficients. -/
theorem curve_coeff_eq {N : ℕ} {c d : ℕ → M} {S : Set ℂ} (hS : S.Finite)
    (h : ∀ t : ℂ, t ∉ S → ∑ k ∈ Finset.range N, t ^ k • c k
      = ∑ k ∈ Finset.range N, t ^ k • d k) {k : ℕ} (hk : k < N) : c k = d k := by
  have h0 : ∀ t : ℂ, t ∉ S → ∑ k ∈ Finset.range N, t ^ k • (c k - d k) = 0 := by
    intro t ht
    have : ∑ k ∈ Finset.range N, t ^ k • (c k - d k)
        = (∑ k ∈ Finset.range N, t ^ k • c k) - ∑ k ∈ Finset.range N, t ^ k • d k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_sub]
    rw [this, h t ht, sub_self]
  have := eq_zero_of_curve_eq_zero hS h0 hk
  rwa [sub_eq_zero] at this

end Extraction

/-! ## Polynomials with operator coefficients, evaluated at scalars -/

section EvalA

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Evaluation of a polynomial with operator coefficients at the scalar `t`. -/
noncomputable def evalA (t : ℂ) (p : Polynomial (Module.End ℂ V)) : Module.End ℂ V :=
  p.eval (t • (1 : Module.End ℂ V))

theorem smul_one_pow (t : ℂ) (k : ℕ) :
    (t • (1 : Module.End ℂ V)) ^ k = t ^ k • (1 : Module.End ℂ V) := by
  rw [_root_.smul_pow, one_pow]

@[simp] theorem evalA_monomial (t : ℂ) (k : ℕ) (a : Module.End ℂ V) :
    evalA t (monomial k a) = t ^ k • a := by
  rw [evalA, Polynomial.eval_monomial, smul_one_pow, mul_smul_comm, mul_one]

@[simp] theorem evalA_C (t : ℂ) (a : Module.End ℂ V) : evalA t (C a) = a := by
  simp [evalA]

@[simp] theorem evalA_X_pow (t : ℂ) (k : ℕ) :
    evalA t ((X : Polynomial (Module.End ℂ V)) ^ k) = t ^ k • 1 := by
  rw [Polynomial.X_pow_eq_monomial, evalA_monomial]

@[simp] theorem evalA_one (t : ℂ) : evalA t (1 : Polynomial (Module.End ℂ V)) = 1 := by
  simp [evalA]

@[simp] theorem evalA_add (t : ℂ) (p q : Polynomial (Module.End ℂ V)) :
    evalA t (p + q) = evalA t p + evalA t q := by
  simp [evalA]

theorem evalA_mul (t : ℂ) (p q : Polynomial (Module.End ℂ V)) :
    evalA t (p * q) = evalA t p * evalA t q := by
  refine Polynomial.eval₂_mul_noncomm (RingHom.id _) _ fun k => ?_
  exact (Algebra.commutes t (q.coeff k)).symm.trans (by simp [Algebra.smul_def])

theorem evalA_pow (t : ℂ) (p : Polynomial (Module.End ℂ V)) (m : ℕ) :
    evalA t (p ^ m) = (evalA t p) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, evalA_mul, ih, pow_succ]

theorem evalA_finset_sum {ι : Type*} (t : ℂ) (s : Finset ι)
    (g : ι → Polynomial (Module.End ℂ V)) :
    evalA t (∑ i ∈ s, g i) = ∑ i ∈ s, evalA t (g i) := by
  simp [evalA, Polynomial.eval_finset_sum]

theorem evalA_eq_sum_range {p : Polynomial (Module.End ℂ V)} {n : ℕ} (hn : p.natDegree < n)
    (t : ℂ) : evalA t p = ∑ j ∈ Finset.range n, t ^ j • p.coeff j := by
  rw [evalA, Polynomial.eval_eq_sum_range' hn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_one_pow, mul_smul_comm, mul_one]

/-- A polynomial with operator coefficients is determined by its values at the nonzero
complex numbers. -/
theorem ext_of_evalA_eq {p q : Polynomial (Module.End ℂ V)} {S : Set ℂ} (hS : S.Finite)
    (h : ∀ t : ℂ, t ∉ S → evalA t p = evalA t q) : p = q := by
  set n := max p.natDegree q.natDegree + 1 with hn
  have hp : p.natDegree < n := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hq : q.natDegree < n := lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)
  have hcurve : ∀ t : ℂ, t ∉ S → ∑ k ∈ Finset.range n, t ^ k • p.coeff k
      = ∑ k ∈ Finset.range n, t ^ k • q.coeff k := by
    intro t ht
    rw [← evalA_eq_sum_range hp t, ← evalA_eq_sum_range hq t]
    exact h t ht
  refine Polynomial.ext fun k => ?_
  by_cases hk : k < n
  · exact curve_coeff_eq hS hcurve hk
  · push_neg at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq hk)]

/-! ### The first three coefficients -/

theorem coeff_mul_zero (p q : Polynomial (Module.End ℂ V)) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  simp [Polynomial.coeff_mul]

theorem coeff_mul_one (p q : Polynomial (Module.End ℂ V)) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  simp [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

theorem coeff_mul_two (p q : Polynomial (Module.End ℂ V)) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  simp [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

/-- The clearing factor `(1 + X²)ᵐ`. -/
noncomputable def sqFactor (m : ℕ) : Polynomial (Module.End ℂ V) := (1 + X ^ 2) ^ m

@[simp] theorem coeff_sqFactor_zero (m : ℕ) : (sqFactor (V := V) m).coeff 0 = 1 := by
  induction m with
  | zero => simp [sqFactor, Polynomial.coeff_one]
  | succ m ih =>
      rw [sqFactor, pow_succ, ← sqFactor, coeff_mul_zero, ih]
      simp

@[simp] theorem coeff_sqFactor_one (m : ℕ) : (sqFactor (V := V) m).coeff 1 = 0 := by
  induction m with
  | zero => simp [sqFactor, Polynomial.coeff_one]
  | succ m ih =>
      rw [sqFactor, pow_succ, ← sqFactor, coeff_mul_one, ih, coeff_sqFactor_zero]
      simp [Polynomial.coeff_one]

@[simp] theorem coeff_sqFactor_two (m : ℕ) : (sqFactor (V := V) m).coeff 2 = (m : ℂ) • 1 := by
  induction m with
  | zero => simp [sqFactor, Polynomial.coeff_one]
  | succ m ih =>
      rw [sqFactor, pow_succ, ← sqFactor, coeff_mul_two, ih, coeff_sqFactor_zero,
        coeff_sqFactor_one]
      simp [Polynomial.coeff_one, Polynomial.coeff_X_pow, add_smul, add_comm]

theorem evalA_sqFactor (t : ℂ) (m : ℕ) :
    evalA t (sqFactor (V := V) m) = ((1 + t ^ 2) ^ m) • 1 := by
  rw [sqFactor, evalA_pow]
  have : evalA t ((1 : Polynomial (Module.End ℂ V)) + X ^ 2) = (1 + t ^ 2) • 1 := by
    rw [evalA_add, evalA_one, evalA_X_pow, add_smul, one_smul]
  rw [this, _root_.smul_pow, one_pow]

end EvalA


/-! ## The diagonal torus of `SL(2,ℂ)` and the identities we need -/

section Matrices

/-- The diagonal matrix `diag(a, a⁻¹)` (the identity when `a = 0`, a value never used). -/
noncomputable def dMat (a : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  if h : a = 0 then 1 else ⟨!![a, 0; 0, a⁻¹], by
    rw [Matrix.det_fin_two_of, mul_inv_cancel₀ h]
    ring⟩

theorem dMat_coe {a : ℂ} (ha : a ≠ 0) :
    (dMat a : Matrix (Fin 2) (Fin 2) ℂ) = !![a, 0; 0, a⁻¹] := by
  have h1 : dMat a
      = (⟨!![a, 0; 0, a⁻¹], by rw [Matrix.det_fin_two_of, mul_inv_cancel₀ ha]; ring⟩
        : Matrix.SpecialLinearGroup (Fin 2) ℂ) := by
    simp only [dMat]
    exact dif_neg ha
  simp only [h1]

/-- The Weyl element `w₁ = u₊(1) u₋(-1) u₊(1)`. -/
noncomputable def wOne : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  uPlus 1 * uMinus (-1) * uPlus 1

/-- The diagonal torus is a product of unipotent matrices and the fixed Weyl element. -/
theorem dMat_factor {a : ℂ} (ha : a ≠ 0) :
    dMat a = uPlus a * uMinus (-a⁻¹) * uPlus a * wOne⁻¹ := by
  refine eq_mul_inv_of_mul_eq ?_
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [show wOne = uPlus 1 * uMinus (-1) * uPlus 1 from rfl]
  all_goals repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  all_goals simp [dMat_coe ha, uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two,
    mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

/-- Conjugating the upper unipotent subgroup by the torus squares the parameter. -/
theorem dMat_mul_uPlus {a : ℂ} (ha : a ≠ 0) (t : ℂ) :
    dMat a * uPlus t = uPlus (a ^ 2 * t) * dMat a := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  all_goals simp [dMat_coe ha, uPlus, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [ha]

/-- Conjugating the lower unipotent subgroup by the torus inverts the square. -/
theorem dMat_mul_uMinus {a : ℂ} (ha : a ≠ 0) (t : ℂ) :
    dMat a * uMinus t = uMinus ((a ^ 2)⁻¹ * t) * dMat a := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  all_goals simp [dMat_coe ha, uMinus, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [ha]

/-- The big-cell (Bruhat) identity on the diagonal `s = t`. -/
theorem bruhat {s : ℂ} (hs : 1 + s ^ 2 ≠ 0) :
    uMinus s * uPlus s
      = uPlus (s * (1 + s ^ 2)⁻¹) * dMat ((1 + s ^ 2)⁻¹) * uMinus (s * (1 + s ^ 2)⁻¹) := by
  have hc : (1 + s ^ 2)⁻¹ ≠ 0 := inv_ne_zero hs
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  all_goals simp [dMat_coe hc, uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hs]
  all_goals ring

end Matrices


/-! ## Unipotent representations -/

section Unipotent

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The truncated exponential series `∑_{k<n} (tᵏ/k!) • Aᵏ`. -/
noncomputable def expSum (A : Module.End ℂ V) (n : ℕ) (t : ℂ) : Module.End ℂ V :=
  ∑ k ∈ Finset.range n, (t ^ k / (Nat.factorial k : ℂ)) • A ^ k

/-- A representation of `SL(2,ℂ)` is **unipotent of order `N`** when the two unipotent
one-parameter subgroups act by the exponential series of two nilpotent operators `E` and
`F`.  No relation between `E` and `F` is assumed; the `sl₂` relations are derived. -/
structure IsUnipotentExp (rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (E F : Module.End ℂ V) (N : ℕ) : Prop where
  /-- Two terms of the exponential series are needed to see the generators. -/
  two_le : 2 ≤ N
  /-- `E` is nilpotent of order at most `N`. -/
  nilpotent_E : E ^ N = 0
  /-- `F` is nilpotent of order at most `N`. -/
  nilpotent_F : F ^ N = 0
  /-- The upper unipotent subgroup acts by `exp (t E)`. -/
  expE : ∀ t : ℂ, rho (uPlus t) = expSum E N t
  /-- The lower unipotent subgroup acts by `exp (t F)`. -/
  expF : ∀ t : ℂ, rho (uMinus t) = expSum F N t

/-- A nilpotent operator's exponential series may be summed over any longer range. -/
theorem expSum_extend {A : Module.End ℂ V} {N m : ℕ} (hnil : A ^ N = 0) (hNm : N ≤ m) (t : ℂ) :
    expSum A N t = expSum A m t := by
  have hsub : Finset.range N ⊆ Finset.range m := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNm)
  refine Finset.sum_subset hsub ?_
  intro k hk hkN
  rw [Finset.mem_range] at hk
  rw [Finset.mem_range, not_lt] at hkN
  have : A ^ k = 0 := by
    rw [show k = N + (k - N) by omega, pow_add, hnil, zero_mul]
  rw [this, smul_zero]



/-! ### The polynomials -/

/-- The polynomial whose value at `t` is the truncated exponential series. -/
noncomputable def expPoly (A : Module.End ℂ V) (n : ℕ) : Polynomial (Module.End ℂ V) :=
  ∑ k ∈ Finset.range n, C (((Nat.factorial k : ℂ))⁻¹ • A ^ k) * X ^ k

/-- The polynomial whose value at `a ≠ 0` is `a^(n-1) • exp (-a⁻¹ A)`. -/
noncomputable def expInvPoly (A : Module.End ℂ V) (n : ℕ) : Polynomial (Module.End ℂ V) :=
  ∑ k ∈ Finset.range n,
    C ((((-1 : ℂ) ^ k) * ((Nat.factorial k : ℂ))⁻¹) • A ^ k) * X ^ (n - 1 - k)

/-- The polynomial whose value at `a ≠ 0` is `a^(n-1)` times the action of the torus
element `diag (a, a⁻¹)`. -/
noncomputable def dPoly (rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (E F : Module.End ℂ V) (n : ℕ) : Polynomial (Module.End ℂ V) :=
  expPoly E n * expInvPoly F n * expPoly E n * C (rho wOne⁻¹)

@[simp] theorem evalA_C_mul_X_pow (t : ℂ) (c : Module.End ℂ V) (k : ℕ) :
    evalA t (C c * X ^ k) = t ^ k • c := by
  rw [evalA_mul, evalA_C, evalA_X_pow, mul_smul_comm, mul_one]

theorem evalA_expPoly (A : Module.End ℂ V) (n : ℕ) (t : ℂ) :
    evalA t (expPoly A n) = expSum A n t := by
  rw [expPoly, evalA_finset_sum, expSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [evalA_C_mul_X_pow, smul_smul, div_eq_mul_inv]

theorem evalA_expInvPoly {a : ℂ} (ha : a ≠ 0) (A : Module.End ℂ V) {n : ℕ} (hn : 1 ≤ n) :
    evalA a (expInvPoly A n) = a ^ (n - 1) • expSum A n (-a⁻¹) := by
  rw [expInvPoly, evalA_finset_sum, expSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [evalA_C_mul_X_pow, smul_smul, smul_smul]
  congr 1
  have hkn : k ≤ n - 1 := by omega
  have h1 : ((-a⁻¹ : ℂ)) ^ k = (-1) ^ k * (a ^ k)⁻¹ := by
    rw [show (-a⁻¹ : ℂ) = (-1) * a⁻¹ by ring, mul_pow, inv_pow]
  rw [h1, pow_sub₀ a ha hkn, div_eq_mul_inv]
  ring

/-! ### The action of the torus -/

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V}
  {E F : Module.End ℂ V} {n : ℕ}

theorem evalA_dPoly (hU : ∀ t : ℂ, rho (uPlus t) = expSum E n t)
    (hL : ∀ t : ℂ, rho (uMinus t) = expSum F n t) (hn : 1 ≤ n) {a : ℂ} (ha : a ≠ 0) :
    evalA a (dPoly rho E F n) = a ^ (n - 1) • rho (dMat a) := by
  rw [dPoly, evalA_mul, evalA_mul, evalA_mul, evalA_C, evalA_expPoly,
    evalA_expInvPoly ha F hn, ← hU, ← hL, dMat_factor ha]
  simp only [map_mul]
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]

/-! ### The two conjugation relations -/

theorem dMat_one : dMat (1 : ℂ) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat_coe (one_ne_zero (α := ℂ))]

/-- The linear coefficient of an exponential curve is determined by the curve. -/
theorem linear_coeff_eq {m : ℕ} (hm : 2 ≤ m) {c d : ℕ → Module.End ℂ V}
    (h : ∀ t : ℂ, t ≠ 0 → ∑ k ∈ Finset.range m, (t ^ k / (Nat.factorial k : ℂ)) • c k
      = ∑ k ∈ Finset.range m, (t ^ k / (Nat.factorial k : ℂ)) • d k) : c 1 = d 1 := by
  have hcurve : ∀ t : ℂ, t ∉ ({0} : Set ℂ) →
      ∑ k ∈ Finset.range m, t ^ k • (((Nat.factorial k : ℂ))⁻¹ • c k)
      = ∑ k ∈ Finset.range m, t ^ k • (((Nat.factorial k : ℂ))⁻¹ • d k) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    have hrw : ∀ (e : ℕ → Module.End ℂ V),
        ∑ k ∈ Finset.range m, t ^ k • (((Nat.factorial k : ℂ))⁻¹ • e k)
        = ∑ k ∈ Finset.range m, (t ^ k / (Nat.factorial k : ℂ)) • e k := by
      intro e
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, div_eq_mul_inv]
    rw [hrw, hrw]
    exact h t ht
  have := curve_coeff_eq (Set.finite_singleton (0 : ℂ)) hcurve (show 1 < m by omega)
  simpa using this

variable (hU : ∀ t : ℂ, rho (uPlus t) = expSum E n t)
  (hL : ∀ t : ℂ, rho (uMinus t) = expSum F n t)

include hU in
theorem torus_mul_E (hn : 2 ≤ n) {a : ℂ} (ha : a ≠ 0) :
    rho (dMat a) * E = a ^ 2 • (E * rho (dMat a)) := by
  refine linear_coeff_eq (c := fun k => rho (dMat a) * E ^ k)
    (d := fun k => (a ^ (2 * k)) • (E ^ k * rho (dMat a))) hn ?_
  intro t _
  have hgroup : rho (dMat a) * rho (uPlus t) = rho (uPlus (a ^ 2 * t)) * rho (dMat a) := by
    rw [← map_mul, ← map_mul, dMat_mul_uPlus ha t]
  rw [hU, hU, expSum, expSum, Finset.mul_sum, Finset.sum_mul] at hgroup
  calc ∑ k ∈ Finset.range n, (t ^ k / (Nat.factorial k : ℂ)) • (rho (dMat a) * E ^ k)
      = ∑ k ∈ Finset.range n, rho (dMat a) * ((t ^ k / (Nat.factorial k : ℂ)) • E ^ k) :=
        Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
    _ = ∑ k ∈ Finset.range n,
          ((a ^ 2 * t) ^ k / (Nat.factorial k : ℂ)) • E ^ k * rho (dMat a) := hgroup
    _ = ∑ k ∈ Finset.range n,
          (t ^ k / (Nat.factorial k : ℂ)) • ((a ^ (2 * k)) • (E ^ k * rho (dMat a))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mul_assoc, smul_smul]
        congr 1
        rw [mul_pow, pow_mul]
        ring


include hU hL in
theorem dPoly_mul_C_E (hn : 2 ≤ n) :
    dPoly rho E F n * C E = C E * dPoly rho E F n * X ^ 2 := by
  refine ext_of_evalA_eq (Set.finite_singleton (0 : ℂ)) fun a ha => ?_
  rw [Set.mem_singleton_iff] at ha
  have hd := evalA_dPoly hU hL (show 1 ≤ n by omega) ha
  have hE := torus_mul_E hU hn ha
  rw [evalA_mul, evalA_mul, evalA_mul, evalA_C, evalA_X_pow, hd, smul_mul_assoc, hE]
  simp only [smul_smul, mul_smul_comm, mul_one]
  congr 1
  ring

include hL in
theorem torus_mul_F (hn : 2 ≤ n) {a : ℂ} (ha : a ≠ 0) :
    rho (dMat a) * F = (a ^ 2)⁻¹ • (F * rho (dMat a)) := by
  have key : rho (dMat a) * F ^ 1 = (((a ^ 2)⁻¹) ^ 1) • (F ^ 1 * rho (dMat a)) := by
   refine linear_coeff_eq (c := fun k => rho (dMat a) * F ^ k)
    (d := fun k => (((a ^ 2)⁻¹) ^ k) • (F ^ k * rho (dMat a))) hn ?_
   intro t _
   have hgroup : rho (dMat a) * rho (uMinus t)
       = rho (uMinus ((a ^ 2)⁻¹ * t)) * rho (dMat a) := by
     rw [← map_mul, ← map_mul, dMat_mul_uMinus ha t]
   rw [hL, hL, expSum, expSum, Finset.mul_sum, Finset.sum_mul] at hgroup
   calc ∑ k ∈ Finset.range n, (t ^ k / (Nat.factorial k : ℂ)) • (rho (dMat a) * F ^ k)
       = ∑ k ∈ Finset.range n, rho (dMat a) * ((t ^ k / (Nat.factorial k : ℂ)) • F ^ k) :=
         Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
     _ = ∑ k ∈ Finset.range n,
           (((a ^ 2)⁻¹ * t) ^ k / (Nat.factorial k : ℂ)) • F ^ k * rho (dMat a) := hgroup
     _ = ∑ k ∈ Finset.range n,
           (t ^ k / (Nat.factorial k : ℂ)) • ((((a ^ 2)⁻¹) ^ k) • (F ^ k * rho (dMat a))) := by
         refine Finset.sum_congr rfl fun k _ => ?_
         rw [smul_mul_assoc, smul_smul]
         congr 1
         rw [mul_pow]
         ring
  simpa using key

include hU hL in
theorem dPoly_mul_C_F (hn : 2 ≤ n) :
    dPoly rho E F n * C F * X ^ 2 = C F * dPoly rho E F n := by
  refine ext_of_evalA_eq (Set.finite_singleton (0 : ℂ)) fun a ha => ?_
  rw [Set.mem_singleton_iff] at ha
  have hd := evalA_dPoly hU hL (show 1 ≤ n by omega) ha
  have hF := torus_mul_F hL hn ha
  have ha2 : (a ^ 2 : ℂ) ≠ 0 := pow_ne_zero _ ha
  rw [evalA_mul, evalA_mul, evalA_mul, evalA_C, evalA_X_pow, hd, smul_mul_assoc, hF]
  simp only [smul_smul, mul_smul_comm, mul_one]
  congr 1
  field_simp

/-- The Cartan element of the representation: the logarithmic derivative of the action of
the diagonal torus at the identity. -/
noncomputable def cartan (rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (E F : Module.End ℂ V) (n : ℕ) : Module.End ℂ V :=
  evalA 1 (Polynomial.derivative (dPoly rho E F n))

include hU hL in
theorem evalA_one_dPoly (hn : 1 ≤ n) : evalA 1 (dPoly rho E F n) = 1 := by
  rw [evalA_dPoly hU hL hn (one_ne_zero (α := ℂ)), dMat_one, map_one, one_pow, one_smul]

include hU hL in
/-- `[H₀, E] = 2E`. -/
theorem cartan_mul_E (hn : 2 ≤ n) :
    cartan rho E F n * E = E * cartan rho E F n + 2 • E := by
  have h := congrArg Polynomial.derivative (dPoly_mul_C_E hU hL hn)
  have h2 := congrArg (evalA (V := V) 1) h
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero,
    zero_mul, zero_add, Polynomial.derivative_X_pow, evalA_mul, evalA_C, evalA_add,
    evalA_X_pow] at h2
  rw [evalA_one_dPoly hU hL (by omega)] at h2
  simpa [cartan, two_smul, mul_two] using h2

include hU hL in
/-- `[H₀, F] = -2F`. -/
theorem cartan_mul_F (hn : 2 ≤ n) :
    cartan rho E F n * F + 2 • F = F * cartan rho E F n := by
  have h := congrArg Polynomial.derivative (dPoly_mul_C_F hU hL hn)
  have h2 := congrArg (evalA (V := V) 1) h
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero,
    zero_mul, zero_add, Polynomial.derivative_X_pow, evalA_mul, evalA_C, evalA_add,
    evalA_X_pow] at h2
  rw [evalA_one_dPoly hU hL (by omega)] at h2
  simpa [cartan, two_smul, mul_two] using h2

/-! ### The big-cell identity -/

theorem natDegree_expPoly_le (A : Module.End ℂ V) (n : ℕ) :
    (expPoly A n).natDegree ≤ n - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (C (((Nat.factorial k : ℂ))⁻¹ • A ^ k)).natDegree = 0 := Polynomial.natDegree_C _
  have h2 : ((X : Polynomial (Module.End ℂ V)) ^ k).natDegree ≤ k :=
    Polynomial.natDegree_X_pow_le k
  omega

theorem natDegree_expInvPoly_le (A : Module.End ℂ V) (n : ℕ) :
    (expInvPoly A n).natDegree ≤ n - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (C ((((-1 : ℂ) ^ k) * ((Nat.factorial k : ℂ))⁻¹) • A ^ k)).natDegree = 0 :=
    Polynomial.natDegree_C _
  have h2 : ((X : Polynomial (Module.End ℂ V)) ^ (n - 1 - k)).natDegree ≤ n - 1 - k :=
    Polynomial.natDegree_X_pow_le _
  omega

theorem natDegree_dPoly_le : (dPoly rho E F n).natDegree ≤ 3 * (n - 1) := by
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h4 : (C (rho wOne⁻¹)).natDegree = 0 := Polynomial.natDegree_C _
  have h123 : (expPoly E n * expInvPoly F n * expPoly E n).natDegree ≤ 3 * (n - 1) := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h12 : (expPoly E n * expInvPoly F n).natDegree ≤ (n - 1) + (n - 1) :=
      le_trans Polynomial.natDegree_mul_le
        (Nat.add_le_add (natDegree_expPoly_le E n) (natDegree_expInvPoly_le F n))
    have h3 := natDegree_expPoly_le E n
    omega
  omega

/-- The polynomial whose value at `s` is `(1+s²)^(n-1)` times the exponential series at
`s/(1+s²)`. -/
noncomputable def expCPoly (A : Module.End ℂ V) (n : ℕ) : Polynomial (Module.End ℂ V) :=
  ∑ k ∈ Finset.range n, C (((Nat.factorial k : ℂ))⁻¹ • A ^ k) * sqFactor (n - 1 - k) * X ^ k

/-- The polynomial whose value at `s` is a power of `1+s²` times the action of the torus at
`(1+s²)⁻¹`. -/
noncomputable def dCPoly (rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (E F : Module.End ℂ V) (n : ℕ) : Polynomial (Module.End ℂ V) :=
  ∑ j ∈ Finset.range (3 * (n - 1) + 1),
    C ((dPoly rho E F n).coeff j) * sqFactor (3 * (n - 1) - j)

theorem evalA_expCPoly (A : Module.End ℂ V) {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (hs : 1 + s ^ 2 ≠ 0) :
    evalA s (expCPoly A n)
      = ((1 + s ^ 2) ^ (n - 1)) • expSum A n (s * (1 + s ^ 2)⁻¹) := by
  rw [expCPoly, evalA_finset_sum, expSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [evalA_mul, evalA_mul, evalA_C, evalA_sqFactor, evalA_X_pow, mul_smul_comm, mul_one,
    smul_mul_assoc, mul_smul_comm, mul_one, smul_smul, smul_smul, smul_smul]
  congr 1
  have hkn : k ≤ n - 1 := by omega
  rw [mul_pow, inv_pow, pow_sub₀ _ hs hkn, div_eq_mul_inv]
  ring

theorem evalA_dCPoly {s : ℂ} (hs : 1 + s ^ 2 ≠ 0) :
    evalA s (dCPoly rho E F n)
      = ((1 + s ^ 2) ^ (3 * (n - 1))) • evalA ((1 + s ^ 2)⁻¹) (dPoly rho E F n) := by
  rw [dCPoly, evalA_finset_sum,
    evalA_eq_sum_range (lt_of_le_of_lt natDegree_dPoly_le (Nat.lt_succ_self _)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [evalA_mul, evalA_C, evalA_sqFactor, mul_smul_comm, mul_one, smul_smul]
  congr 1
  have hjd : j ≤ 3 * (n - 1) := by omega
  rw [inv_pow, pow_sub₀ _ hs hjd]

include hU hL in
theorem bruhat_poly (hn : 2 ≤ n) :
    sqFactor (3 * (n - 1) + (n - 1)) * (expPoly F n * expPoly E n)
      = expCPoly E n * dCPoly rho E F n * expCPoly F n := by
  refine ext_of_evalA_eq (S := {Complex.I, -Complex.I}) (Set.toFinite _) fun s hsmem => ?_
  have hs : 1 + s ^ 2 ≠ 0 := by
    intro h
    have hfac : (s - Complex.I) * (s + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination h - hI
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hsmem (by simp [sub_eq_zero.mp h1])
    · exact hsmem (by simp [eq_neg_of_add_eq_zero_left h1])
  have hc : (1 + s ^ 2)⁻¹ ≠ 0 := inv_ne_zero hs
  have hgroup : rho (uMinus s) * rho (uPlus s)
      = rho (uPlus (s * (1 + s ^ 2)⁻¹)) * rho (dMat ((1 + s ^ 2)⁻¹))
        * rho (uMinus (s * (1 + s ^ 2)⁻¹)) := by
    rw [← map_mul, ← map_mul, ← map_mul, bruhat hs]
  simp only [evalA_mul]
  rw [evalA_sqFactor, evalA_expPoly, evalA_expPoly, evalA_expCPoly E (by omega) hs,
    evalA_expCPoly F (by omega) hs, evalA_dCPoly hs, evalA_dPoly hU hL (by omega) hc,
    ← hU, ← hL, ← hU, ← hL, hgroup]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
  congr 1
  have hpow : ((1 + s ^ 2)⁻¹) ^ (n - 1) * (1 + s ^ 2) ^ (n - 1) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs, one_pow]
  rw [pow_add]
  field_simp
  ring
  exact hpow.symm

/-! ### Reading off the coefficient of `s²` -/

theorem coeff_C_mul_X_pow (c : Module.End ℂ V) (k j : ℕ) :
    (C c * X ^ k).coeff j = if k = j then c else 0 := by
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]

theorem sum_range_eq_three {m : ℕ} (hm : 3 ≤ m) (g : ℕ → Module.End ℂ V)
    (hg : ∀ k, 3 ≤ k → g k = 0) : ∑ k ∈ Finset.range m, g k = g 0 + g 1 + g 2 := by
  have hsub : Finset.range 3 ⊆ Finset.range m := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hm)
  rw [← Finset.sum_subset hsub (fun k _ hk => hg k (by simpa using hk))]
  simp [Finset.sum_range_succ]

theorem coeff_expPoly_lt {A : Module.End ℂ V} {m j : ℕ} (hj : j < m) :
    (expPoly A m).coeff j = ((Nat.factorial j : ℂ))⁻¹ • A ^ j := by
  rw [expPoly, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro k _ hk
    rw [coeff_C_mul_X_pow, if_neg hk]
  · intro hj'
    exact absurd (Finset.mem_range.mpr hj) hj'

theorem coeff_expCPoly {A : Module.End ℂ V} {m : ℕ} (hm : 3 ≤ m) :
    (expCPoly A m).coeff 0 = 1 ∧ (expCPoly A m).coeff 1 = A ∧
      (expCPoly A m).coeff 2 = ((m : ℂ) - 1) • 1 + ((2 : ℂ))⁻¹ • A ^ 2 := by
  have hterm : ∀ (k j : ℕ),
      ((C (((Nat.factorial k : ℂ))⁻¹ • A ^ k) * sqFactor (m - 1 - k)) * X ^ k).coeff j
        = if k ≤ j then (((Nat.factorial k : ℂ))⁻¹ • A ^ k)
            * (sqFactor (V := V) (m - 1 - k)).coeff (j - k) else 0 := by
    intro k j
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs with h
    · rw [Polynomial.coeff_C_mul]
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [expCPoly, Polynomial.finset_sum_coeff]
    rw [sum_range_eq_three hm _ (fun k hk => by rw [hterm, if_neg (by omega)])]
    rw [hterm, hterm, hterm]
    norm_num
  · rw [expCPoly, Polynomial.finset_sum_coeff]
    rw [sum_range_eq_three hm _ (fun k hk => by rw [hterm, if_neg (by omega)])]
    rw [hterm, hterm, hterm]
    norm_num
  · rw [expCPoly, Polynomial.finset_sum_coeff]
    rw [sum_range_eq_three hm _ (fun k hk => by rw [hterm, if_neg (by omega)])]
    rw [hterm, hterm, hterm]
    norm_num
    have hcast : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
      have h1 : (1 : ℕ) ≤ m := by omega
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcast]

theorem coeff_dCPoly_zero :
    (dCPoly rho E F n).coeff 0
      = ∑ j ∈ Finset.range (3 * (n - 1) + 1), (dPoly rho E F n).coeff j := by
  rw [dCPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, coeff_sqFactor_zero, mul_one]

theorem coeff_dCPoly_one : (dCPoly rho E F n).coeff 1 = 0 := by
  rw [dCPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Polynomial.coeff_C_mul, coeff_sqFactor_one, mul_zero]

theorem coeff_dCPoly_two :
    (dCPoly rho E F n).coeff 2
      = ∑ j ∈ Finset.range (3 * (n - 1) + 1),
          (((3 * (n - 1) - j : ℕ)) : ℂ) • (dPoly rho E F n).coeff j := by
  rw [dCPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, coeff_sqFactor_two, mul_smul_comm, mul_one]

theorem natCast_add_one_eq (i : ℕ) :
    ((i : Module.End ℂ V) + 1) = (((i : ℂ) + 1)) • (1 : Module.End ℂ V) := by
  rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]

theorem evalA_one_eq_sum_coeff {p : Polynomial (Module.End ℂ V)} {m : ℕ} (hm : p.natDegree < m) :
    evalA 1 p = ∑ j ∈ Finset.range m, p.coeff j := by
  rw [evalA_eq_sum_range hm]
  simp

theorem evalA_one_derivative_eq_sum {p : Polynomial (Module.End ℂ V)} {m : ℕ}
    (hm : p.natDegree < m) :
    evalA 1 (Polynomial.derivative p) = ∑ j ∈ Finset.range m, (j : ℂ) • p.coeff j := by
  have hd : (Polynomial.derivative p).natDegree < m :=
    lt_of_le_of_lt (le_trans (Polynomial.natDegree_derivative_le p) (Nat.sub_le _ 1)) hm
  rw [evalA_eq_sum_range hd]
  have hterm : ∀ i : ℕ, (1 : ℂ) ^ i • (Polynomial.derivative p).coeff i
      = ((i : ℂ) + 1) • p.coeff (i + 1) := by
    intro i
    rw [one_pow, one_smul, Polynomial.coeff_derivative, natCast_add_one_eq, mul_smul_comm,
      mul_one]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.range m) => hterm i]
  have h1 : ∑ j ∈ Finset.range (m + 1), (j : ℂ) • p.coeff j
      = ∑ i ∈ Finset.range m, ((i : ℂ) + 1) • p.coeff (i + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : ∑ j ∈ Finset.range (m + 1), (j : ℂ) • p.coeff j
      = ∑ j ∈ Finset.range m, (j : ℂ) • p.coeff j := by
    rw [Finset.sum_range_succ, Polynomial.coeff_eq_zero_of_natDegree_lt hm, smul_zero, add_zero]
  rw [← h1, h2]

include hU hL in
theorem coeff_dCPoly_zero_eq (hn : 1 ≤ n) : (dCPoly rho E F n).coeff 0 = 1 := by
  rw [coeff_dCPoly_zero,
    ← evalA_one_eq_sum_coeff (lt_of_le_of_lt natDegree_dPoly_le (Nat.lt_succ_self _)),
    evalA_one_dPoly hU hL hn]

theorem coeff_dCPoly_two_eq :
    (dCPoly rho E F n).coeff 2
      = ((3 * (n - 1) : ℕ) : ℂ) • (∑ j ∈ Finset.range (3 * (n - 1) + 1),
          (dPoly rho E F n).coeff j) - cartan rho E F n := by
  rw [coeff_dCPoly_two]
  have hsum : ∀ j ∈ Finset.range (3 * (n - 1) + 1),
      (((3 * (n - 1) - j : ℕ)) : ℂ) • (dPoly rho E F n).coeff j
        = ((3 * (n - 1) : ℕ) : ℂ) • (dPoly rho E F n).coeff j
          - (j : ℂ) • (dPoly rho E F n).coeff j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← sub_smul]
    congr 1
    have hjd : j ≤ 3 * (n - 1) := by omega
    push_cast [Nat.cast_sub hjd]
    ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_sub_distrib, ← Finset.smul_sum, cartan,
    evalA_one_derivative_eq_sum (lt_of_le_of_lt natDegree_dPoly_le (Nat.lt_succ_self _))]

include hU hL in
theorem cartan_eq_commutator (hn : 3 ≤ n) :
    cartan rho E F n = E * F - F * E + ((n : ℂ) - 1) • 1 := by
  have hid := bruhat_poly hU hL (by omega)
  have hc := congrArg (fun p => Polynomial.coeff p 2) hid
  have hE0 : (expPoly E n).coeff 0 = 1 := by
    rw [coeff_expPoly_lt (show 0 < n by omega)]; simp
  have hE1 : (expPoly E n).coeff 1 = E := by
    rw [coeff_expPoly_lt (show 1 < n by omega)]; simp
  have hE2 : (expPoly E n).coeff 2 = ((2 : ℂ))⁻¹ • E ^ 2 := by
    rw [coeff_expPoly_lt (show 2 < n by omega)]; norm_num
  have hF0 : (expPoly F n).coeff 0 = 1 := by
    rw [coeff_expPoly_lt (show 0 < n by omega)]; simp
  have hF1 : (expPoly F n).coeff 1 = F := by
    rw [coeff_expPoly_lt (show 1 < n by omega)]; simp
  have hF2 : (expPoly F n).coeff 2 = ((2 : ℂ))⁻¹ • F ^ 2 := by
    rw [coeff_expPoly_lt (show 2 < n by omega)]; norm_num
  obtain ⟨hUc0, hUc1, hUc2⟩ := coeff_expCPoly (A := E) (m := n) hn
  obtain ⟨hLc0, hLc1, hLc2⟩ := coeff_expCPoly (A := F) (m := n) hn
  have hD0 : (dCPoly rho E F n).coeff 0 = 1 := coeff_dCPoly_zero_eq hU hL (by omega)
  have hD1 : (dCPoly rho E F n).coeff 1 = 0 := coeff_dCPoly_one
  have hD2 : (dCPoly rho E F n).coeff 2
      = ((3 * (n - 1) : ℕ) : ℂ) • 1 - cartan rho E F n := by
    rw [coeff_dCPoly_two_eq,
      ← evalA_one_eq_sum_coeff (lt_of_le_of_lt natDegree_dPoly_le (Nat.lt_succ_self _)),
      evalA_one_dPoly hU hL (by omega)]
  simp only [coeff_mul_two, coeff_mul_one, coeff_mul_zero, coeff_sqFactor_zero,
    coeff_sqFactor_one, coeff_sqFactor_two, hE0, hE1, hE2, hF0, hF1, hF2,
    hUc0, hUc1, hUc2, hLc0, hLc1, hLc2, hD0, hD1, hD2] at hc
  have h1 : (1 : ℕ) ≤ n := by omega
  have hcast : ((3 * (n - 1) : ℕ) : ℂ) = 3 * ((n : ℂ) - 1) := by
    push_cast [Nat.cast_sub h1]; ring
  have hcast2 : ((3 * (n - 1) + (n - 1) : ℕ) : ℂ) = 4 * ((n : ℂ) - 1) := by
    push_cast [Nat.cast_sub h1]; ring
  rw [hcast, hcast2] at hc
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at hc
  linear_combination (norm := module) hc

/-! ### The `sl₂`-triple and Weyl's theorem -/

variable {N : ℕ}

/-- **The `sl₂` relations are a consequence of the group law.**  If the two unipotent
one-parameter subgroups of `SL(2,ℂ)` act by the exponential series of nilpotent operators
`E` and `F`, then `E`, `F` and `H := EF - FE` satisfy the `sl₂` commutation relations. -/
theorem sl2_relations_of_unipotent (h : IsUnipotentExp rho E F N) :
    (E * F - F * E) * E - E * (E * F - F * E) = 2 • E ∧
      (E * F - F * E) * F - F * (E * F - F * E) = -(2 • F) := by
  set m := N + 3 with hm
  have hUm : ∀ t : ℂ, rho (uPlus t) = expSum E m t := fun t =>
    (h.expE t).trans (expSum_extend (N := N) (m := m) h.nilpotent_E (by omega) t)
  have hLm : ∀ t : ℂ, rho (uMinus t) = expSum F m t := fun t =>
    (h.expF t).trans (expSum_extend (N := N) (m := m) h.nilpotent_F (by omega) t)
  have hcart := cartan_eq_commutator hUm hLm (by omega)
  have hE := cartan_mul_E hUm hLm (by omega)
  have hF := cartan_mul_F hUm hLm (by omega)
  rw [hcart] at hE hF
  have e1 : (E * F - F * E + ((m : ℂ) - 1) • 1) * E
      = (E * F - F * E) * E + ((m : ℂ) - 1) • E := by
    rw [add_mul, smul_mul_assoc, one_mul]
  have e2 : E * (E * F - F * E + ((m : ℂ) - 1) • 1)
      = E * (E * F - F * E) + ((m : ℂ) - 1) • E := by
    rw [mul_add, mul_smul_comm, mul_one]
  have e3 : (E * F - F * E + ((m : ℂ) - 1) • 1) * F
      = (E * F - F * E) * F + ((m : ℂ) - 1) • F := by
    rw [add_mul, smul_mul_assoc, one_mul]
  have e4 : F * (E * F - F * E + ((m : ℂ) - 1) • 1)
      = F * (E * F - F * E) + ((m : ℂ) - 1) • F := by
    rw [mul_add, mul_smul_comm, mul_one]
  rw [e1, e2] at hE
  rw [e3, e4] at hF
  exact ⟨by linear_combination (norm := module) hE, by linear_combination (norm := module) hF⟩

/-- The `sl₂`-triple carried by a unipotent representation of `SL(2,ℂ)`. -/
noncomputable def sl2OfUnipotent (h : IsUnipotentExp rho E F N) : Sl2Rep V where
  E := E
  F := F
  H := E * F - F * E
  he := (sl2_relations_of_unipotent h).1
  hf := (sl2_relations_of_unipotent h).2
  hef := rfl





/-! ### The hypothesis is satisfiable: the defining representation -/



end Unipotent

end BookProof.ChapterWeylSL2Unipotent


