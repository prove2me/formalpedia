-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCWt
-- name    : RPLib_S4_AlgGrpCWt
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:59:16.9722+00:00
-- url     : https://prove2.me/theorems/ac248389-b556-4503-8fc6-c84f06a64551
-- title:
--   Larsen's alternative library: monomial weights and the finite-dimensional pieces `Ad d`
-- statement:
--   * `derD (diagonal lam)` acts on `monomial e c` by the scalar `wt (wtv lam) e` (`derD_diag_monomial`),
--     and replacing `lam` by `ψ ∘ lam` (`ψ` additive) replaces the weight `m` by `ψ m` (`wt_comp`).
--   * `Ad d`, the span of the monomials of degree `≤ d`, is finite-dimensional and every `derD Z`
--     maps it into itself (`derD_mem_Ad`); every polynomial lies in some `Ad d` (`mem_Ad_totalDegree`).
--   * Iterates of a derivation: if `D^[p+1] a = 0` and `D^[q+1] b = 0` then `D^[p+q+1] (a*b) = 0`;
--     hence a derivation killing the variables after `m+1` steps kills `monomial e 1` after
--     `m * degree e + 1` steps (`iterate_monomial_eq_zero`). Any field.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCBrk

/-!
# S4-AlgGrpC, file Wt: monomial weights and the finite-dimensional pieces `Ad d`

* `derD (diagonal lam)` acts on `monomial e c` by the scalar `wt (wtv lam) e` (`derD_diag_monomial`),
  and replacing `lam` by `ψ ∘ lam` (`ψ` additive) replaces the weight `m` by `ψ m` (`wt_comp`).
* `Ad d`, the span of the monomials of degree `≤ d`, is finite-dimensional and every `derD Z`
  maps it into itself (`derD_mem_Ad`); every polynomial lies in some `Ad d` (`mem_Ad_totalDegree`).
* Iterates of a derivation: if `D^[p+1] a = 0` and `D^[q+1] b = 0` then `D^[p+q+1] (a*b) = 0`;
  hence a derivation killing the variables after `m+1` steps kills `monomial e 1` after
  `m * degree e + 1` steps (`iterate_monomial_eq_zero`). Any field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The weight of a coordinate under `diagonal lam`: `x_ij ↦ lam j`, `y_ij ↦ -lam i`. -/
def wtv (lam : n → K) : Var n → K := Sum.elim (fun ij => lam ij.2) (fun ij => -lam ij.1)

/-- The weight of an exponent vector. -/
def wt (w : Var n → K) (e : Var n →₀ ℕ) : K := ∑ v, (e v : K) * w v

theorem wt_zero (w : Var n → K) : wt w 0 = 0 := by simp [wt]

theorem wt_add (w : Var n → K) (e f : Var n →₀ ℕ) : wt w (e + f) = wt w e + wt w f := by
  simp [wt, add_mul, Finset.sum_add_distrib]

theorem wt_single (w : Var n → K) (v : Var n) (b : ℕ) : wt w (Finsupp.single v b) = b * w v := by
  simp [wt, Finsupp.single_apply]

theorem wt_comp (w : Var n → K) (ψ : K →+ K) (e : Var n →₀ ℕ) :
    wt (fun v => ψ (w v)) e = ψ (wt w e) := by
  simp only [wt, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]

theorem wtv_comp (lam : n → K) (ψ : K →+ K) (v : Var n) :
    wtv (fun j => ψ (lam j)) v = ψ (wtv lam v) := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩ <;> simp [wtv]

theorem derD_diag_X (lam : n → K) (v : Var n) :
    derD (Matrix.diagonal lam) (X v) = wtv lam v • X v := by
  rw [derD_X]
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [dN, Sum.elim_inl, wtv]
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.diagonal_apply_ne _ hk, C_0, mul_zero])
      (by simp), Matrix.diagonal_apply_eq, smul_eq_C_mul, mul_comm]
  · simp only [dN, Sum.elim_inr, wtv]
    rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [Matrix.neg_apply, Matrix.diagonal_apply_ne _ hk.symm, neg_zero, C_0, zero_mul])
      (by simp), Matrix.neg_apply, Matrix.diagonal_apply_eq, smul_eq_C_mul]

/-- A derivation scaling each variable acts on monomials by their weight. -/
theorem derivation_monomial (w : Var n → K)
    (D : Derivation K (MvPolynomial (Var n) K) (MvPolynomial (Var n) K))
    (hD : ∀ v, D (X v) = w v • X v) (e : Var n →₀ ℕ) :
    ∀ c : K, D (monomial e c) = wt w e • monomial e c := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · intro c
    rw [monomial_zero', MvPolynomial.derivation_C, wt_zero, zero_smul]
  · intro f g hf hg c
    rw [show monomial (f + g) c = monomial f c * monomial g 1 by rw [monomial_mul, mul_one],
      Derivation.leibniz, hf, hg (1 : K), wt_add, smul_eq_mul, smul_eq_mul, smul_eq_C_mul,
      smul_eq_C_mul, smul_eq_C_mul, C_add]
    ring
  · intro a b c
    rw [← C_mul_X_pow_eq_monomial, Derivation.leibniz, MvPolynomial.derivation_C, smul_zero,
      add_zero, Derivation.leibniz_pow, hD, wt_single, smul_eq_mul]
    rcases b with _ | b
    · simp
    · simp only [smul_eq_C_mul, nsmul_eq_mul, add_tsub_cancel_right, map_mul, map_add, map_one,
        map_natCast, Nat.cast_add, Nat.cast_one]
      ring

theorem derD_diag_monomial (lam : n → K) (e : Var n →₀ ℕ) (c : K) :
    derD (Matrix.diagonal lam) (monomial e c) = wt (wtv lam) e • monomial e c :=
  derivation_monomial (wtv lam) _ (derD_diag_X lam) e c

/-- Exponent vectors of degree at most `d`. -/
def expS (d : ℕ) : Set (Var n →₀ ℕ) := {e | e.degree ≤ d}

theorem expS_finite (d : ℕ) : (expS (n := n) d).Finite := Finsupp.finite_of_degree_le d

/-- The polynomials of total degree at most `d`, as the span of their monomials. -/
def Ad (d : ℕ) : Submodule K (MvPolynomial (Var n) K) :=
  Submodule.span K ((fun e => monomial e (1 : K)) '' expS d)

instance Ad_finite (d : ℕ) : FiniteDimensional K (Ad (n := n) (K := K) d) :=
  FiniteDimensional.span_of_finite K ((expS_finite d).image _)

theorem monomial_mem_Ad {d : ℕ} {e : Var n →₀ ℕ} (he : e ∈ expS d) (c : K) :
    monomial e c ∈ Ad (K := K) d := by
  rw [show monomial e c = c • monomial e (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨e, he, rfl⟩)

theorem mem_Ad_totalDegree (f : MvPolynomial (Var n) K) : f ∈ Ad (K := K) f.totalDegree := by
  have h : ∀ e ∈ f.support, monomial e (coeff e f) ∈ Ad (K := K) f.totalDegree := fun e he =>
    monomial_mem_Ad (show e.degree ≤ f.totalDegree from le_totalDegree he) _
  have := Submodule.sum_mem (Ad (K := K) f.totalDegree) h
  rwa [← f.as_sum] at this

theorem pderiv_mul_X_mem {d : ℕ} {e : Var n →₀ ℕ} (he : e ∈ expS d) (c : K) (v w : Var n) :
    pderiv v (monomial e c) * X w ∈ Ad (K := K) d := by
  rw [pderiv_monomial]
  by_cases hv : e v = 0
  · rw [hv, Nat.cast_zero, mul_zero, monomial_zero, zero_mul]
    exact Submodule.zero_mem _
  · rw [X, monomial_mul, mul_one]
    refine monomial_mem_Ad ?_ _
    have h1 := congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel hv)
    have he' : e.degree ≤ d := he
    change (e - Finsupp.single v 1 + Finsupp.single w 1).degree ≤ d
    rw [map_add, Finsupp.degree_single] at h1 ⊢
    omega

theorem derD_monomial_mem_Ad (Z : Matrix n n K) {d : ℕ} {e : Var n →₀ ℕ} (he : e ∈ expS d) :
    derD Z (monomial e (1 : K)) ∈ Ad (K := K) d := by
  rw [derD_apply, derN]
  refine Submodule.sum_mem _ fun v _ => ?_
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [dN, Sum.elim_inl, Finset.mul_sum, ← mul_assoc]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mul_comm, C_mul']
    exact Submodule.smul_mem _ _ (pderiv_mul_X_mem he _ _ _)
  · simp only [dN, Sum.elim_inr, Finset.mul_sum, C_mul', mul_smul_comm]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pderiv_mul_X_mem he _ _ _)

/-- Every left-invariant derivation preserves `Ad d`. -/
theorem derD_mem_Ad (Z : Matrix n n K) {d : ℕ} {p : MvPolynomial (Var n) K} (hp : p ∈ Ad d) :
    derD Z p ∈ Ad (K := K) d := by
  have : Ad (n := n) (K := K) d ≤ (Ad d).comap (derD Z).toLinearMap := by
    rw [Ad, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    exact derD_monomial_mem_Ad Z he
  exact this hp

/-- Endomorphisms of `Ad d` agreeing on the monomials are equal. -/
theorem Ad_ext {d : ℕ} {f g : Module.End K (Ad (n := n) (K := K) d)}
    (h : ∀ e (he : e ∈ expS d), f ⟨monomial e 1, monomial_mem_Ad he 1⟩ =
      g ⟨monomial e 1, monomial_mem_Ad he 1⟩) : f = g := by
  refine LinearMap.ext_on (Submodule.span_span_coe_preimage) fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := hx
  have : x = ⟨monomial e 1, monomial_mem_Ad he 1⟩ := Subtype.ext hxe.symm
  rw [this]
  exact h e he

section Iter

variable {A : Type*} [CommRing A] [Algebra K A]

theorem iterate_mul_eq_zero (D : Derivation K A A) (k : ℕ) :
    ∀ p q : ℕ, p + q = k → ∀ a b : A, D^[p + 1] a = 0 → D^[q + 1] b = 0 →
      D^[k + 1] (a * b) = 0 := by
  induction k with
  | zero =>
    intro p q hpq a b ha hb
    obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    simp only [zero_add, Function.iterate_one] at ha hb ⊢
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  | succ k ih =>
    intro p q hpq a b ha hb
    rw [Function.iterate_succ_apply, Derivation.leibniz, iterate_map_add, smul_eq_mul, smul_eq_mul]
    have h1 : D^[k + 1] (a * D b) = 0 := by
      rcases q with _ | q
      · simp only [zero_add, Function.iterate_one] at hb
        rw [hb, mul_zero, iterate_map_zero]
      · exact ih p q (by omega) a (D b) ha (by rwa [← Function.iterate_succ_apply])
    have h2 : D^[k + 1] (b * D a) = 0 := by
      rcases p with _ | p
      · simp only [zero_add, Function.iterate_one] at ha
        rw [ha, mul_zero, iterate_map_zero]
      · exact ih q p (by omega) b (D a) hb (by rwa [← Function.iterate_succ_apply])
    rw [h1, h2, add_zero]

theorem iterate_eq_zero_of_le (D : Derivation K A A) {j k : ℕ} (hjk : j ≤ k) {a : A}
    (ha : D^[j] a = 0) : D^[k] a = 0 := by
  rw [show k = (k - j) + j by omega, Function.iterate_add_apply, ha, iterate_map_zero]

end Iter

/-- A derivation killing every variable after `m + 1` steps kills `monomial e 1` after
`m * degree e + 1` steps. -/
theorem iterate_monomial_eq_zero (D : Derivation K (MvPolynomial (Var n) K) (MvPolynomial (Var n) K))
    (m : ℕ) (hX : ∀ v, D^[m + 1] (X v) = 0) (e : Var n →₀ ℕ) :
    D^[m * e.degree + 1] (monomial e (1 : K)) = 0 := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · rw [map_zero, mul_zero, zero_add, Function.iterate_one, monomial_zero',
      MvPolynomial.derivation_C]
  · intro f g hf hg
    rw [show monomial (f + g) (1 : K) = monomial f 1 * monomial g 1 by rw [monomial_mul, mul_one],
      map_add, mul_add]
    exact iterate_mul_eq_zero D _ _ _ rfl _ _ hf hg
  · intro a b
    rw [Finsupp.degree_single, ← X_pow_eq_monomial]
    induction b with
    | zero =>
      rw [pow_zero, mul_zero, zero_add, Function.iterate_one, Derivation.map_one_eq_zero]
    | succ b ih =>
      rw [pow_succ, show m * (b + 1) = m * b + m by ring]
      exact iterate_mul_eq_zero D _ _ _ rfl _ _ ih (hX a)

end RamanujanPetersson.AlgGrpC


