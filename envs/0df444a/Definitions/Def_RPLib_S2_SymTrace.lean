-- Prove2me | Definitions.Def_RPLib_S2_SymTrace
-- name    : RPLib_S2_SymTrace
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:45:52.306056+00:00
-- url     : https://prove2.me/theorems/9a26b393-84ae-4422-b9de-e059d858701d
-- title:
--   Symmetric powers of a $2\times 2$ matrix: traces $U_n(t,d)$ and eigenvalues
-- statement:
--   For a $2 \times 2$ matrix $A$ over a commutative ring with trace $t$ and determinant $d$, the trace of $\mathrm{Sym}^n A$ (on homogeneous polynomials of degree $n$ in two variables) equals $U_n(t,d)$, where $U_0 = 1$, $U_1 = t$, $U_{n+1} = tU_n - dU_{n-1}$. Over a field the eigenvalues of $\mathrm{Sym}^n A$ are $\alpha^i\beta^{n-i}$; over $\mathbb{C}$, if $|\alpha| = |\beta| = q^{1/2}$ they all have modulus $q^{n/2}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   W. Fulton and J. Harris, Representation Theory, GTM 129, Springer 1991, Lecture 11, doi:10.1007/978-1-4612-0979-9

import Mathlib

/-!
# Symmetric powers of a rank-2 operator: traces `U_n(t, d)` and eigenvalues

Unit S2-SymTrace of the Ramanujan-Petersson project (pure linear algebra).

Model. `Sym^n (R^2)` is the space of homogeneous polynomials of degree `n` in two variables
`x = X 0`, `y = X 1`, with the monomial basis `x^i y^(n-i)` (`i = 0..n`). A `2 x 2` matrix `A`
acts on `R^2` (column `i` is the image of the `i`-th basis vector) and hence on the polynomial
ring by the algebra substitution `X i ↦ ∑ j, A j i • X j` (`subst A`). `symMat n A` is the
matrix of this substitution on the degree-`n` part, in the monomial basis. It is multiplicative
(`symHom n` is a monoid hom), natural in the ring (`symMat_map`), and for a free module `V` with a
basis `b` the endomorphism `Sym^n f` has matrix `symMat n (LinearMap.toMatrix b b f)`.

Main results.
* `trace_symMat` : over any commutative ring, `trace (Sym^n A) = U n (trace A) (det A)`.
* `trace_symMat_of_charpoly` : the same for an endomorphism of a free rank-2 module with
  characteristic polynomial `X^2 - t X + d`.
* `charpoly_symMat` : over a field, if `charpoly A = (X - α)(X - β)` then
  `charpoly (Sym^n A) = ∏ i, (X - α^i β^(n-i))`; `isRoot_charpoly_symMat_iff` (the eigenvalues).
* `trace_symMat_pow` : `trace (Sym^n A ^ m) = ∑ i, α^(m i) β^(m (n-i))`.
* `norm_eigenvalue_symMat` : over `ℂ`, if `|α| = |β| = √q` then every eigenvalue of `Sym^n A` has
  absolute value `√q ^ n = q^(n/2)`.
* `U_mul_genFun` : `(∑ n, U_n(t,d) X^n) * (1 - t X + d X^2) = 1` in `R⟦X⟧`.
* `U_two_mul_one` / `U_eq_pow_mul_chebyshev` : relation with Mathlib's Chebyshev `U`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.SymTrace

/-! ## The recursion `U_n(t, d)` -/

/-- `U 0 t d = 1`, `U 1 t d = t`, `U (n+2) t d = t * U (n+1) t d - d * U n t d`. -/
def U {R : Type*} [CommRing R] : ℕ → R → R → R
  | 0, _, _ => 1
  | 1, t, _ => t
  | (n + 2), t, d => t * U (n + 1) t d - d * U n t d

section URec

variable {R : Type*} [CommRing R]

@[simp] lemma U_zero (t d : R) : U 0 t d = 1 := rfl

@[simp] lemma U_one (t d : R) : U 1 t d = t := rfl

lemma U_add_two (n : ℕ) (t d : R) : U (n + 2) t d = t * U (n + 1) t d - d * U n t d := rfl

lemma U_succ_succ (n : ℕ) (t d : R) :
    U (n + 1 + 1) t d = t * U (n + 1) t d - d * U n t d := rfl

/-- `U` commutes with ring homomorphisms. -/
lemma map_U {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) (t d : R) :
    f (U n t d) = U n (f t) (f d) := by
  have key : ∀ n : ℕ, f (U n t d) = U n (f t) (f d) ∧
      f (U (n + 1) t d) = U (n + 1) (f t) (f d) := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [U_succ_succ, U_succ_succ, map_sub, map_mul, map_mul, ih.1, ih.2]
  exact (key n).1

/-- `U_n(α + β, α β) = ∑_{i=0}^n α^i β^(n-i)` (complete homogeneous symmetric polynomial). -/
lemma U_add_mul (n : ℕ) (a b : R) :
    U n (a + b) (a * b) = ∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n - i) := by
  have step : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1 + 1), a ^ i * b ^ (m + 1 - i)
      = b ^ (m + 1) + a * ∑ i ∈ Finset.range (m + 1), a ^ i * b ^ (m - i) := by
    intro m
    rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right]
      ring
  have key : ∀ n : ℕ, U n (a + b) (a * b) = ∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n - i) ∧
      U (n + 1) (a + b) (a * b) = ∑ i ∈ Finset.range (n + 1 + 1), a ^ i * b ^ (n + 1 - i) := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp [Finset.sum_range_succ]; ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [U_succ_succ, ih.1, ih.2, step (k + 1), step k]
      ring
  exact (key n).1

/-- Scaling: `U_n(s t, s^2 d) = s^n U_n(t, d)`. -/
lemma U_smul (n : ℕ) (s t d : R) : U n (s * t) (s ^ 2 * d) = s ^ n * U n t d := by
  have key : ∀ n : ℕ, U n (s * t) (s ^ 2 * d) = s ^ n * U n t d ∧
      U (n + 1) (s * t) (s ^ 2 * d) = s ^ (n + 1) * U (n + 1) t d := by
    intro n
    induction n with
    | zero => constructor <;> simp
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [U_succ_succ, U_succ_succ, ih.1, ih.2]
      ring
  exact (key n).1

/-- Relation with Mathlib's Chebyshev polynomials of the second kind: `U_n(2x, 1) = U_n(x)`. -/
lemma U_two_mul_one (n : ℕ) (x : R) :
    U n (2 * x) 1 = (Polynomial.Chebyshev.U R n).eval x := by
  have key : ∀ n : ℕ, U n (2 * x) 1 = (Polynomial.Chebyshev.U R n).eval x ∧
      U (n + 1) (2 * x) 1 = (Polynomial.Chebyshev.U R ((n + 1 : ℕ) : ℤ)).eval x := by
    intro n
    induction n with
    | zero => constructor <;> simp [Polynomial.Chebyshev.U_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [U_succ_succ, ih.1, ih.2]
      have h2 := Polynomial.Chebyshev.U_add_two R (k : ℤ)
      push_cast
      rw [show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring, h2]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      ring
  exact (key n).1

/-- Homogeneous form (Deligne normalisation): `U_n(2 s x, s^2) = s^n U_n(x)`. -/
lemma U_eq_pow_mul_chebyshev (n : ℕ) (s x : R) :
    U n (2 * s * x) (s ^ 2) = s ^ n * (Polynomial.Chebyshev.U R n).eval x := by
  rw [← U_two_mul_one, ← U_smul]
  congr 1 <;> ring

/-- The generating function: `(∑_n U_n(t,d) X^n) * (1 - t X + d X^2) = 1`, i.e.
`∑_n U_n(t,d) X^n = 1 / (1 - t X + d X^2)`. -/
lemma U_mul_genFun (t d : R) :
    PowerSeries.mk (fun n => U n t d) *
      (1 - PowerSeries.C t * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2) = 1 := by
  set F : PowerSeries R := PowerSeries.mk (fun n => U n t d) with hF
  have e : F * (1 - PowerSeries.C t * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2) =
      F - PowerSeries.C t * (F * PowerSeries.X ^ 1) + PowerSeries.C d * (F * PowerSeries.X ^ 2) := by
    ring
  rw [e]
  ext n
  rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one]
  rcases n with _ | _ | k
  · simp [hF]
  · simp [hF]
  · simp only [hF, PowerSeries.coeff_mk]
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega),
      show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega, U_succ_succ]
    ring

/-- The same identity with the inverse, over a field. -/
lemma genFun_eq_inv {K : Type*} [Field K] (t d : K) :
    PowerSeries.mk (fun n => U n t d) =
      (1 - PowerSeries.C t * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · exact U_mul_genFun t d
  · simp

end URec

/-! ## The symmetric power of a `2 x 2` matrix -/

section SymPow

variable {R : Type*} [CommRing R]

/-- The algebra substitution of `MvPolynomial (Fin 2) R` induced by `A`: `X i ↦ ∑ j, A j i • X j`. -/
noncomputable def subst (A : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval fun i => ∑ j, MvPolynomial.C (A j i) * MvPolynomial.X j

lemma subst_X (A : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    subst A (MvPolynomial.X i) = ∑ j, MvPolynomial.C (A j i) * MvPolynomial.X j :=
  MvPolynomial.aeval_X _ _

lemma subst_C (A : Matrix (Fin 2) (Fin 2) R) (r : R) :
    subst A (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]

lemma subst_mul (A B : Matrix (Fin 2) (Fin 2) R) : subst (A * B) = (subst A).comp (subst B) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, subst_X, subst_X, map_sum]
  simp only [map_mul, subst_C, subst_X, Matrix.mul_apply, Fin.sum_univ_two, map_add]
  ring

lemma subst_one : subst (1 : Matrix (Fin 2) (Fin 2) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [subst_X]
  fin_cases i <;> simp [Matrix.one_apply]

/-- Exponent of the basis monomial `x^i y^(n-i)`. -/
noncomputable def mon (n i : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 (n - i)

@[simp] lemma mon_apply_zero (n i : ℕ) : mon n i 0 = i := by simp [mon]

@[simp] lemma mon_apply_one (n i : ℕ) : mon n i 1 = n - i := by simp [mon]

lemma degree_mon {n i : ℕ} (h : i ≤ n) : (mon n i).degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, mon_apply_zero, mon_apply_one]
  omega

lemma mon_injective {n i j : ℕ} (h : mon n i = mon n j) : i = j := by
  have := congrArg (fun m => m 0) h
  simpa using this

lemma eq_mon_of_degree {n : ℕ} (d : Fin 2 →₀ ℕ) (hd : d.degree = n) : d = mon n (d 0) := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
  ext i
  fin_cases i
  · simp
  · simp only [Fin.mk_one, mon_apply_one]
    omega

/-- The basis monomial `x^i y^(n-i)`. -/
noncomputable def smon (n i : ℕ) : MvPolynomial (Fin 2) R := MvPolynomial.monomial (mon n i) 1

lemma smon_eq (n i : ℕ) :
    (smon n i : MvPolynomial (Fin 2) R) = MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (n - i) := by
  simp [smon, mon, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]

lemma subst_smon (A : Matrix (Fin 2) (Fin 2) R) (n i : ℕ) :
    subst A (smon n i) = subst A (MvPolynomial.X 0) ^ i * subst A (MvPolynomial.X 1) ^ (n - i) := by
  rw [smon_eq, map_mul, map_pow, map_pow]

lemma isHomogeneous_subst_X (A : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (subst A (MvPolynomial.X i)).IsHomogeneous 1 := by
  rw [subst_X]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _

lemma isHomogeneous_subst_smon (A : Matrix (Fin 2) (Fin 2) R) {n i : ℕ} (h : i ≤ n) :
    (subst A (smon n i)).IsHomogeneous n := by
  rw [subst_smon]
  have := ((isHomogeneous_subst_X A 0).pow i).mul ((isHomogeneous_subst_X A 1).pow (n - i))
  convert this using 1
  omega

/-- A homogeneous polynomial of degree `n` in two variables is a combination of the
`x^k y^(n-k)`. -/
lemma eq_sum_mon {n : ℕ} {p : MvPolynomial (Fin 2) R} (hp : p.IsHomogeneous n) :
    p = ∑ k : Fin (n + 1), MvPolynomial.monomial (mon n k) (MvPolynomial.coeff (mon n k) p) := by
  ext d
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = n
  · have hd0 : d 0 < n + 1 := by
      have := hd
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
      omega
    have e : mon n (d 0) = d := (eq_mon_of_degree d hd).symm
    rw [Finset.sum_eq_single ⟨d 0, hd0⟩]
    · simp [e]
    · intro k _ hk
      rw [if_neg]
      intro h
      apply hk
      apply Fin.ext
      have := congrArg (fun m => m 0) h
      simpa using this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hp.coeff_eq_zero hd]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro h
    apply hd
    rw [← h]
    exact degree_mon k.is_le

/-- **The symmetric power.** `symMat n A` is the matrix of `Sym^n A` in the basis `x^i y^(n-i)`:
its `(i, j)` entry is the coefficient of `x^i y^(n-i)` in `A • (x^j y^(n-j))`. -/
noncomputable def symMat (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => MvPolynomial.coeff (mon n i) (subst A (smon n j))

lemma symMat_apply_coeff (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (i j : Fin (n + 1)) :
    symMat n A i j = MvPolynomial.coeff (mon n i) (subst A (smon n j)) := rfl

lemma symMat_mul (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) R) :
    symMat n (A * B) = symMat n A * symMat n B := by
  ext i j
  rw [symMat_apply_coeff, Matrix.mul_apply, subst_mul, AlgHom.comp_apply,
    eq_sum_mon (isHomogeneous_subst_smon B j.is_le), map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_one (MvPolynomial.coeff (mon n k) _), ← MvPolynomial.C_mul_monomial, map_mul, subst_C,
    MvPolynomial.coeff_C_mul, mul_comm]
  rfl

lemma symMat_one (n : ℕ) : symMat n (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  rw [symMat_apply_coeff, subst_one, AlgHom.id_apply, smon, MvPolynomial.coeff_monomial,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Fin.ext (mon_injective h').symm)

/-- `Sym^n` as a monoid homomorphism `M_2(R) →* M_{n+1}(R)`. -/
noncomputable def symHom (n : ℕ) :
    Matrix (Fin 2) (Fin 2) R →* Matrix (Fin (n + 1)) (Fin (n + 1)) R where
  toFun := symMat n
  map_one' := symMat_one n
  map_mul' := symMat_mul n

@[simp] lemma symHom_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) : symHom n A = symMat n A := rfl

lemma symMat_pow (n m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) : symMat n (A ^ m) = symMat n A ^ m :=
  map_pow (symHom n) A m

/-- `Sym^n` of a representation `G → GL_2(R)`. -/
noncomputable def symRep (n : ℕ) : GL (Fin 2) R →* GL (Fin (n + 1)) R :=
  Units.map (symHom n)

lemma symRep_val (n : ℕ) (g : GL (Fin 2) R) :
    ((symRep n g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = symMat n g := rfl

/-- Dehomogenisation `x ↦ X`, `y ↦ 1`. -/
noncomputable def deh : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval ![Polynomial.X, 1]

lemma coeff_deh {n : ℕ} {p : MvPolynomial (Fin 2) R} (hp : p.IsHomogeneous n) (i : Fin (n + 1)) :
    (deh p).coeff i = MvPolynomial.coeff (mon n i) p := by
  conv_lhs => rw [eq_sum_mon hp]
  rw [map_sum, Polynomial.finsetSum_coeff]
  have hm : ∀ k : Fin (n + 1), deh (MvPolynomial.monomial (mon n k) (MvPolynomial.coeff (mon n k) p))
      = Polynomial.C (MvPolynomial.coeff (mon n k) p) * Polynomial.X ^ (k : ℕ) := by
    intro k
    rw [← mul_one (MvPolynomial.coeff (mon n k) p), ← MvPolynomial.C_mul_monomial, mul_one]
    change deh (MvPolynomial.C _ * smon n k) = _
    rw [smon_eq, map_mul, map_mul, map_pow, map_pow]
    simp [deh]
  simp only [hm, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk (Fin.ext h).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Explicit formula: the `(i, j)` entry of `Sym^n A` is the coefficient of `X^i` in
`(A₀₀ X + A₁₀)^j (A₀₁ X + A₁₁)^(n-j)`. -/
lemma symMat_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (i j : Fin (n + 1)) :
    symMat n A i j = ((Polynomial.C (A 0 0) * Polynomial.X + Polynomial.C (A 1 0)) ^ (j : ℕ) *
      (Polynomial.C (A 0 1) * Polynomial.X + Polynomial.C (A 1 1)) ^ (n - j)).coeff i := by
  rw [symMat_apply_coeff, ← coeff_deh (isHomogeneous_subst_smon A j.is_le), subst_smon, map_mul,
    map_pow, map_pow, subst_X, subst_X]
  simp [deh, Fin.sum_univ_two]

/-- Naturality of `Sym^n` in the ring. -/
lemma symMat_map {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    symMat n (A.map f) = (symMat n A).map f := by
  ext i j
  rw [Matrix.map_apply, symMat_apply, symMat_apply, ← Polynomial.coeff_map]
  simp [Polynomial.map_mul, Polynomial.map_pow]

lemma map_trace_symMat {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : f (symMat n A).trace = (symMat n (A.map f)).trace := by
  rw [symMat_map]
  simp [Matrix.trace, map_sum]

lemma map_trace_two {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) :
    f A.trace = (A.map f).trace := by
  simp [Matrix.trace_fin_two]

lemma map_det_two {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) :
    f A.det = (A.map f).det := by
  simp [Matrix.det_fin_two]

/-! ### Triangular matrices -/

lemma symMat_lower (n : ℕ) (T : Matrix (Fin 2) (Fin 2) R) (hT : T 1 0 = 0) {i j : Fin (n + 1)}
    (hij : i < j) : symMat n T i j = 0 := by
  rw [symMat_apply, hT, map_zero, add_zero, mul_pow, mul_comm (Polynomial.C (T 0 0) ^ (j : ℕ)),
    mul_assoc, Polynomial.coeff_X_pow_mul', if_neg]
  exact not_le.mpr hij

lemma symMat_diag (n : ℕ) (T : Matrix (Fin 2) (Fin 2) R) (hT : T 1 0 = 0) (i : Fin (n + 1)) :
    symMat n T i i = T 0 0 ^ (i : ℕ) * T 1 1 ^ (n - i) := by
  rw [symMat_apply, hT, map_zero, add_zero, mul_pow, mul_comm (Polynomial.C (T 0 0) ^ (i : ℕ)),
    mul_assoc, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero]
  simp

lemma trace_symMat_lower (n : ℕ) (T : Matrix (Fin 2) (Fin 2) R) (hT : T 1 0 = 0) :
    (symMat n T).trace = ∑ i ∈ Finset.range (n + 1), T 0 0 ^ i * T 1 1 ^ (n - i) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, symMat_diag n T hT]
  exact Fin.sum_univ_eq_sum_range (fun i => T 0 0 ^ i * T 1 1 ^ (n - i)) (n + 1)

lemma charpoly_symMat_lower (n : ℕ) (T : Matrix (Fin 2) (Fin 2) R) (hT : T 1 0 = 0) :
    (symMat n T).charpoly =
      ∏ i : Fin (n + 1), (Polynomial.X - Polynomial.C (T 0 0 ^ (i : ℕ) * T 1 1 ^ (n - i))) := by
  have hu : (symMat n T).transpose.IsUpperTriangular := fun i j hij => symMat_lower n T hT hij
  rw [← Matrix.charpoly_transpose, Matrix.charpoly_of_isUpperTriangular _ hu]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.transpose_apply, symMat_diag n T hT]

lemma pow_lower (T : Matrix (Fin 2) (Fin 2) R) (hT : T 1 0 = 0) (m : ℕ) :
    (T ^ m) 1 0 = 0 ∧ (T ^ m) 0 0 = T 0 0 ^ m ∧ (T ^ m) 1 1 = T 1 1 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, hT]
    refine ⟨by ring, by ring, by ring⟩

/-! ### Conjugation -/

lemma symMat_conj {n : ℕ} {A P T : Matrix (Fin 2) (Fin 2) R} (hP : IsUnit P) (h : A * P = P * T) :
    symMat n A = symMat n P * symMat n T * (symMat n P)⁻¹ := by
  have hQ : IsUnit (symMat n P) := hP.map (symHom n)
  have h' : symMat n A * symMat n P = symMat n P * symMat n T := by
    rw [← symMat_mul, h, symMat_mul]
  rw [← h', Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ)]

lemma trace_symMat_conj {n : ℕ} {A P T : Matrix (Fin 2) (Fin 2) R} (hP : IsUnit P)
    (h : A * P = P * T) : (symMat n A).trace = (symMat n T).trace := by
  have hQ : IsUnit (symMat n P).det := (Matrix.isUnit_iff_isUnit_det _).mp (hP.map (symHom n))
  rw [symMat_conj hP h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ,
    Matrix.one_mul]

lemma charpoly_symMat_conj {n : ℕ} {A P T : Matrix (Fin 2) (Fin 2) R} (hP : IsUnit P)
    (h : A * P = P * T) : (symMat n A).charpoly = (symMat n T).charpoly := by
  obtain ⟨u, hu⟩ := hP.map (symHom n)
  rw [symMat_conj hP h]
  change (symHom n P * symMat n T * (symHom n P)⁻¹).charpoly = _
  rw [← hu, Matrix.charpoly_units_conj]

lemma pow_conj {A P T : Matrix (Fin 2) (Fin 2) R} (h : A * P = P * T) (m : ℕ) :
    A ^ m * P = P * T ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih,
      Matrix.mul_assoc]

/-- If `charpoly A = (X - α)(X - β)` then `trace A = α + β` and `det A = α β`. -/
lemma trace_det_of_charpoly {A : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (hA : A.charpoly = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    A.trace = α + β ∧ A.det = α * β := by
  have e : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) =
      Polynomial.X ^ 2 - Polynomial.C (α + β) * Polynomial.X + Polynomial.C (α * β) := by
    simp only [map_add, map_mul]
    ring
  rw [e] at hA
  constructor
  · rw [Matrix.trace_eq_neg_charpoly_coeff, hA]
    simp
  · rw [Matrix.det_eq_sign_charpoly_coeff, hA]
    simp

end SymPow

/-! ## Triangularisation over a field -/

section Field

variable {K : Type*} [Field K]

/-- Over a field, a `2 x 2` matrix with an eigenvalue `α` is conjugate to a lower-left-zero
matrix with diagonal `(α, trace A - α)`. -/
lemma exists_triangular (A : Matrix (Fin 2) (Fin 2) K) (α : K)
    (hα : α ^ 2 - A.trace * α + A.det = 0) :
    ∃ P T : Matrix (Fin 2) (Fin 2) K, IsUnit P ∧ A * P = P * T ∧ T 1 0 = 0 ∧ T 0 0 = α ∧
      T 1 1 = A.trace - α := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hα
  by_cases hc : A 1 0 = 0
  · by_cases ha : α = A 0 0
    · exact ⟨1, A, isUnit_one, by simp, hc, ha.symm, by rw [Matrix.trace_fin_two, ha]; ring⟩
    · have hd : α = A 1 1 := by
        have h0 : (α - A 0 0) * (α - A 1 1) = 0 := by
          rw [hc] at hα
          linear_combination hα
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd (sub_eq_zero.mp h) ha
        · exact sub_eq_zero.mp h
      refine ⟨!![A 0 1, 1; A 1 1 - A 0 0, 0], !![A 1 1, 0; 0, A 0 0], ?_, ?_, rfl, hd.symm, ?_⟩
      · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of, isUnit_iff_ne_zero]
        intro h
        apply ha
        rw [hd]
        linear_combination -h
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;> ring
      · simp [Matrix.trace_fin_two, hd]
  · refine ⟨!![α - A 1 1, 1; A 1 0, 0], !![α, 1; 0, A 0 0 + A 1 1 - α], ?_, ?_, rfl, rfl, ?_⟩
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of, isUnit_iff_ne_zero]
      intro h
      apply hc
      linear_combination -h
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hα | linear_combination -hα
    · simp [Matrix.trace_fin_two]

/-- Over a field, if `α` is an eigenvalue of `A` then `trace (Sym^n A) = U_n(trace A, det A)`. -/
lemma trace_symMat_of_root (n : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (α : K)
    (hα : α ^ 2 - A.trace * α + A.det = 0) :
    (symMat n A).trace = U n A.trace A.det := by
  obtain ⟨P, T, hP, h, h10, h00, h11⟩ := exists_triangular A α hα
  obtain ⟨β, hβ⟩ : ∃ β, A.trace - α = β := ⟨_, rfl⟩
  have ht : A.trace = α + β := by rw [← hβ]; ring
  have hd : A.det = α * β := by rw [← hβ]; linear_combination hα
  rw [trace_symMat_conj hP h, trace_symMat_lower n T h10, h00, h11, hβ, ht, hd, U_add_mul]

/-- Over a field, if `charpoly A = (X - α)(X - β)` then
`charpoly (Sym^n A) = ∏_{i=0}^n (X - α^i β^(n-i))`: the eigenvalues of `Sym^n A` are the
`α^i β^(n-i)`. -/
theorem charpoly_symMat (n : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (α β : K)
    (hA : A.charpoly = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    (symMat n A).charpoly =
      ∏ i : Fin (n + 1), (Polynomial.X - Polynomial.C (α ^ (i : ℕ) * β ^ (n - i))) := by
  obtain ⟨ht, hd⟩ := trace_det_of_charpoly hA
  obtain ⟨P, T, hP, h, h10, h00, h11⟩ := exists_triangular A α (by rw [ht, hd]; ring)
  have hb : A.trace - α = β := by rw [ht]; ring
  rw [charpoly_symMat_conj hP h, charpoly_symMat_lower n T h10, h00, h11, hb]

/-- The eigenvalues of `Sym^n A` are exactly the `α^i β^(n-i)`, `0 ≤ i ≤ n`. -/
theorem isRoot_charpoly_symMat_iff (n : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (α β : K)
    (hA : A.charpoly = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) (μ : K) :
    (symMat n A).charpoly.IsRoot μ ↔ ∃ i : Fin (n + 1), μ = α ^ (i : ℕ) * β ^ (n - i) := by
  rw [charpoly_symMat n A α β hA, Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- `trace (Sym^n A ^ m) = ∑_{i=0}^n α^(m i) β^(m (n-i))`. -/
theorem trace_symMat_pow (n m : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (α β : K)
    (hA : A.charpoly = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    (symMat n A ^ m).trace = ∑ i ∈ Finset.range (n + 1), α ^ (m * i) * β ^ (m * (n - i)) := by
  obtain ⟨ht, hd⟩ := trace_det_of_charpoly hA
  obtain ⟨P, T, hP, h, h10, h00, h11⟩ := exists_triangular A α (by rw [ht, hd]; ring)
  have hb : A.trace - α = β := by rw [ht]; ring
  obtain ⟨p10, p00, p11⟩ := pow_lower T h10 m
  rw [← symMat_pow, trace_symMat_conj hP (pow_conj h m), trace_symMat_lower n _ p10, p00, p11, h00,
    h11, hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul, ← pow_mul]

end Field

/-! ## The trace formula over an arbitrary commutative ring (generic matrix argument) -/

section Generic

/-- The universal ring of `2 x 2` matrices. -/
abbrev UnivRing : Type := MvPolynomial (Fin 2 × Fin 2) ℤ

/-- An algebraically closed field containing `UnivRing`. -/
abbrev UnivField : Type := AlgebraicClosure (FractionRing UnivRing)

/-- The embedding `UnivRing → UnivField`. -/
noncomputable def univEmb : UnivRing →+* UnivField :=
  (algebraMap (FractionRing UnivRing) UnivField).comp (algebraMap UnivRing (FractionRing UnivRing))

lemma univEmb_injective : Function.Injective univEmb :=
  (algebraMap (FractionRing UnivRing) UnivField).injective.comp
    (IsFractionRing.injective UnivRing (FractionRing UnivRing))

/-- The generic `2 x 2` matrix. -/
noncomputable def genMat : Matrix (Fin 2) (Fin 2) UnivRing :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

lemma trace_symMat_genMat (n : ℕ) : (symMat n genMat).trace = U n genMat.trace genMat.det := by
  apply univEmb_injective
  rw [map_trace_symMat, map_U, map_trace_two, map_det_two]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (genMat.map univEmb).charpoly
    (by rw [Matrix.charpoly_degree_eq_dim]; simp)
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hα
  exact trace_symMat_of_root n _ α (by simpa using hα)

/-- **Trace of a symmetric power.** For any `2 x 2` matrix `A` over a commutative ring,
`trace (Sym^n A) = U_n(trace A, det A)`. -/
theorem trace_symMat {R : Type*} [CommRing R] (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    (symMat n A).trace = U n A.trace A.det := by
  let φ : UnivRing →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun p => A p.1 p.2)
  have hA : genMat.map φ = A := by
    ext i j
    simp [genMat, φ]
  have := congrArg φ (trace_symMat_genMat n)
  rwa [map_trace_symMat, map_U, map_trace_two, map_det_two, hA] at this

/-- The module form: for an endomorphism `f` of a free module of rank 2 with characteristic
polynomial `X^2 - t X + d`, and any basis `b`, `trace (Sym^n f) = U_n(t, d)`. -/
theorem trace_symMat_of_charpoly {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] [Module.Free R V] [Module.Finite R V] (b : Module.Basis (Fin 2) R V)
    (f : Module.End R V) (t d : R)
    (hf : f.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) (n : ℕ) :
    (symMat n (LinearMap.toMatrix b b f)).trace = U n t d := by
  have hc : (LinearMap.toMatrix b b f).charpoly =
      Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d := by
    rw [LinearMap.charpoly_toMatrix f b, hf]
  have ht : (LinearMap.toMatrix b b f).trace = t := by
    rw [Matrix.trace_eq_neg_charpoly_coeff, hc]
    simp
  have hd : (LinearMap.toMatrix b b f).det = d := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hc]
    simp
  rw [trace_symMat, ht, hd]

/-- `Sym^n f` as an endomorphism of `Sym^n V ≅ R^(n+1)` (basis `x^i y^(n-i)` built from `b`). -/
noncomputable def symEnd {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (n : ℕ) (f : Module.End R V) :
    Module.End R (Fin (n + 1) → R) :=
  Matrix.toLin' (symMat n (LinearMap.toMatrix b b f))

theorem trace_symEnd {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] [Module.Free R V] [Module.Finite R V] (b : Module.Basis (Fin 2) R V)
    (f : Module.End R V) (t d : R)
    (hf : f.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) (n : ℕ) :
    LinearMap.trace R _ (symEnd b n f) = U n t d := by
  rw [symEnd, Matrix.trace_toLin'_eq, trace_symMat_of_charpoly b f t d hf n]

/-- `Sym^n` is functorial on endomorphisms: `Sym^n (f ∘ g) = Sym^n f ∘ Sym^n g`. -/
theorem symEnd_comp {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (n : ℕ) (f g : Module.End R V) :
    symEnd b n (f * g) = symEnd b n f * symEnd b n g := by
  rw [symEnd, symEnd, symEnd, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b, symMat_mul,
    Matrix.toLin'_mul, Module.End.mul_eq_comp]

/-- Change of basis: `Sym^n` of the matrices of `f` in two bases are conjugate by `Sym^n` of the
change-of-basis matrix (so the trace and characteristic polynomial do not depend on `b`). -/
theorem symMat_toMatrix_basis_change {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] (b b' : Module.Basis (Fin 2) R V) (n : ℕ) (f : Module.End R V) :
    symMat n (LinearMap.toMatrix b b f) =
      symMat n (b.toMatrix b') * symMat n (LinearMap.toMatrix b' b' f) * symMat n (b'.toMatrix b) := by
  rw [← symMat_mul, ← symMat_mul, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

theorem symMat_basis_change_mul_flip {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] (b b' : Module.Basis (Fin 2) R V) (n : ℕ) :
    symMat n (b.toMatrix b') * symMat n (b'.toMatrix b) = 1 := by
  rw [← symMat_mul, Module.Basis.toMatrix_mul_toMatrix_flip, symMat_one]

end Generic

/-! ## Over `ℂ`: absolute values of the eigenvalues -/

/-- If `|α| = |β| = √q` then every eigenvalue of `Sym^n A` has absolute value `√q ^ n`. -/
theorem norm_eigenvalue_symMat (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (α β : ℂ)
    (hA : A.charpoly = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) (q : ℝ)
    (hα : ‖α‖ = Real.sqrt q) (hβ : ‖β‖ = Real.sqrt q) (μ : ℂ)
    (hμ : (symMat n A).charpoly.IsRoot μ) : ‖μ‖ = Real.sqrt q ^ n := by
  obtain ⟨i, rfl⟩ := (isRoot_charpoly_symMat_iff n A α β hA μ).mp hμ
  rw [norm_mul, norm_pow, norm_pow, hα, hβ, ← pow_add, Nat.add_sub_of_le i.is_le]

lemma sqrt_pow_eq_rpow (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : Real.sqrt q ^ n = q ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq]
  congr 1
  ring

/-- The same with `q^(n/2)`. -/
theorem norm_eigenvalue_symMat_rpow (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (α β : ℂ)
    (hA : A.charpoly = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) (q : ℝ)
    (hq : 0 ≤ q) (hα : ‖α‖ = Real.sqrt q) (hβ : ‖β‖ = Real.sqrt q) (μ : ℂ)
    (hμ : (symMat n A).charpoly.IsRoot μ) : ‖μ‖ = q ^ ((n : ℝ) / 2) := by
  rw [norm_eigenvalue_symMat n A α β hA q hα hβ μ hμ, sqrt_pow_eq_rpow q hq]

end RamanujanPetersson.SymTrace


