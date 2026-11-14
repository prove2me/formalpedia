-- Prove2me | Definitions.Def_RPLib_S2_HasseA
-- name    : RPLib_S2_HasseA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:28:58.774018+00:00
-- url     : https://prove2.me/theorems/9c328e39-9b0d-48ea-9318-d91b118b044f
-- title:
--   Frobenius on $E[n]$ and the Hasse bound
-- statement:
--   For $E/\mathbb{F}_q$ with $a = q + 1 - \#E(\mathbb{F}_q)$: $\mathrm{tr}(\pi \mid E[n]) = a$, $\det(\pi \mid E[n]) = q$, $\pi^2 - a\pi + q = 0$ on $E[n]$, $\deg(r + s\pi) = r^2 + ars + qs^2$, hence $a^2 \le 4q$, the Hasse bound $|q + 1 - \#E(\mathbb{F}_q)| \le 2\sqrt q$, and both roots of $X^2 - aX + q$ have absolute value $\sqrt q$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Theorem V.1.1 and Theorem V.2.3.1

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDeg

/-!
# S2-Hasse: the Frobenius on `E[n]` and the Hasse bound

For an elliptic curve `W` over a finite field `F` with `q = #F` elements, `N = #W(F)` and
`a = q + 1 - N` (`RPLib.EllFq.trace W`), and an algebraically closed `L ⊇ F`:

* (1) `trace_frobTors`, `det_frobTors` : `tr (π | E[n]) = a`, `det (π | E[n]) = q` in `ℤ/n`, and
  `frobTors_sq_sub` : `π² - a π + q = 0` on `E[n]`, for every `n` with `(n : L) ≠ 0`.
* (2) `deg_rsHom` : `deg (r + s π) = r² + a r s + q s²`; hence `trace_sq_le` : `a² ≤ 4 q`.
  Mathlib-language forms (no `RPLib` in the statement): `trace_sq_le_four_mul` and
  **`hasse_bound`** : `|q + 1 - #W(F)| ≤ 2 √q`.
* (3) `norm_root_eq_sqrt` : every complex root of `X² - a X + q` has norm `√q`.
* Over `F_{q^m}` (`K / F` with `#K = q ^ m`): `trace_baseChange` : `a(W/K) = tseq a q m`, where
  `tseq a q` is the recurrence `2, a, a·t₁ - q·t₀, …`; Mathlib-language form
  **`card_baseChange_eq`** : `#W(K) = q^m + 1 - (α^m + β^m)` for `α + β = a`, `α β = q`, and
  `norm_root_pow` : `‖α ^ m‖ = √(q ^ m)`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.Hasse

/-! ### Rank-two linear algebra -/

section RankTwo

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

lemma det_smul_id_add_smul (b : Module.Basis (Fin 2) R M) (f : M →ₗ[R] M) (r s : R) :
    LinearMap.det (r • LinearMap.id + s • f) =
      r ^ 2 + r * s * LinearMap.trace R M f + s ^ 2 * LinearMap.det f := by
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b f,
    LinearMap.trace_eq_matrix_trace R b f, map_add, map_smul, map_smul, LinearMap.toMatrix_id,
    Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring

/-- Cayley–Hamilton in rank two. -/
lemma sq_eq_trace_smul_sub (b : Module.Basis (Fin 2) R M) (f : M →ₗ[R] M) :
    f ^ 2 = LinearMap.trace R M f • f - LinearMap.det f • (1 : M →ₗ[R] M) := by
  apply (LinearMap.toMatrix b b).injective
  rw [map_sub, map_smul, map_smul, sq, LinearMap.toMatrix_mul, LinearMap.toMatrix_one,
    LinearMap.trace_eq_matrix_trace R b f, ← LinearMap.det_toMatrix b f, Matrix.det_fin_two,
    Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma trace_pow_add_two (b : Module.Basis (Fin 2) R M) (f : M →ₗ[R] M) (m : ℕ) :
    LinearMap.trace R M (f ^ (m + 2)) =
      LinearMap.trace R M f * LinearMap.trace R M (f ^ (m + 1)) -
        LinearMap.det f * LinearMap.trace R M (f ^ m) := by
  rw [pow_add, sq_eq_trace_smul_sub b f, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
    ← pow_succ, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma trace_one_fin_two (b : Module.Basis (Fin 2) R M) : LinearMap.trace R M 1 = 2 := by
  rw [LinearMap.trace_eq_matrix_trace R b, LinearMap.toMatrix_one, Matrix.trace_one,
    Fintype.card_fin, Nat.cast_ofNat]

end RankTwo

/-! ### The trace recurrence `t₀ = 2`, `t₁ = a`, `t_{m+2} = a t_{m+1} - q t_m` -/

section TSeq

/-- `tseq a q m = α ^ m + β ^ m` when `α + β = a`, `α β = q` (`tseq_add_mul`). -/
def tseq {R : Type*} [CommRing R] (a q : R) : ℕ → R
  | 0 => 2
  | 1 => a
  | m + 2 => a * tseq a q (m + 1) - q * tseq a q m

variable {R : Type*} [CommRing R]

lemma tseq_zero (a q : R) : tseq a q 0 = 2 := rfl

lemma tseq_one (a q : R) : tseq a q 1 = a := rfl

lemma tseq_add_two (a q : R) (m : ℕ) :
    tseq a q (m + 2) = a * tseq a q (m + 1) - q * tseq a q m := rfl

lemma map_tseq {S : Type*} [CommRing S] (φ : R →+* S) (a q : R) :
    ∀ m, φ (tseq a q m) = tseq (φ a) (φ q) m
  | 0 => by rw [tseq_zero, tseq_zero, map_ofNat]
  | 1 => by rw [tseq_one, tseq_one]
  | m + 2 => by
    rw [tseq_add_two, tseq_add_two, map_sub, map_mul, map_mul, map_tseq φ a q m,
      map_tseq φ a q (m + 1)]

lemma tseq_add_mul (α β : R) : ∀ m, tseq (α + β) (α * β) m = α ^ m + β ^ m
  | 0 => by rw [tseq_zero, pow_zero, pow_zero, one_add_one_eq_two]
  | 1 => by rw [tseq_one, pow_one, pow_one]
  | m + 2 => by
    rw [tseq_add_two, tseq_add_mul α β m, tseq_add_mul α β (m + 1)]
    ring

lemma trace_pow_eq_tseq {M : Type*} [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M)
    (f : M →ₗ[R] M) : ∀ m, LinearMap.trace R M (f ^ m) =
      tseq (LinearMap.trace R M f) (LinearMap.det f) m
  | 0 => by rw [pow_zero, trace_one_fin_two b, tseq_zero]
  | 1 => by rw [pow_one, tseq_one]
  | m + 2 => by
    rw [trace_pow_add_two b, trace_pow_eq_tseq b f m, trace_pow_eq_tseq b f (m + 1), tseq_add_two]

end TSeq

/-! ### Integers congruent modulo every `n` prime to `p` -/

section Cong

variable (F : Type*) [Field F] [Fintype F] (L : Type*) [Field L] [Algebra F L]

include F in
lemma int_eq_of_zmod {x y : ℤ}
    (h : ∀ (n : ℕ) [NeZero n], (n : L) ≠ 0 → (x : ZMod n) = (y : ZMod n)) : x = y := by
  have hq : ((Fintype.card F : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap F L), FiniteField.cast_card_eq_zero, map_zero]
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  haveI : NeZero (Fintype.card F * (x - y).natAbs + 1) := ⟨Nat.succ_ne_zero _⟩
  have hnL : ((Fintype.card F * (x - y).natAbs + 1 : ℕ) : L) ≠ 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hq, zero_mul, zero_add, Nat.cast_one]
    exact one_ne_zero
  have h1 := h _ hnL
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have hlt : (y - x).natAbs < ((Fintype.card F * (x - y).natAbs + 1 : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    have : (y - x).natAbs = (x - y).natAbs := by rw [← Int.natAbs_neg, neg_sub]
    rw [this]
    exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_left _ hq1)
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1 hlt
  omega

end Cong

/-! ### (1) The Frobenius on `E[n]`; (2) degrees of `r + s π` and `a² ≤ 4q` -/

section Frob

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

open RPLib.Weil RPLib.Isog

attribute [local instance] torsModule

variable (W L) in
lemma exists_basis (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) (ZMod n) (RPLib.Torsion.tors (W.baseChange L) n)) := by
  obtain ⟨e⟩ := RPLib.Torsion.tors_equiv (W := W.baseChange L) n hn
  exact ⟨(Module.Basis.finTwoProd (ZMod n)).map (e.toLinearEquiv (ZMod.map_smul (n := n) e)).symm⟩

/-- **`tr (π | E[n]) = a = q + 1 - N`** in `ℤ/n`. -/
theorem trace_frobTors (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.trace (ZMod n) _ (frobTors W L n) = (RPLib.EllFq.trace W : ZMod n) := by
  obtain ⟨b⟩ := exists_basis W L n hn
  have h1 := det_one_sub_frob (W := W) n hn
  rw [torsLin_rs, det_smul_id_add_smul b, det_frobTors W L n hn] at h1
  rw [RPLib.EllFq.trace_eq]
  push_cast at h1 ⊢
  linear_combination -h1

/-- **`π² - a π + q = 0`** on `E[n]` (Cayley–Hamilton with `tr = a`, `det = q`). -/
theorem frobTors_sq_sub (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    frobTors W L n ^ 2 - (RPLib.EllFq.trace W : ZMod n) • frobTors W L n +
      (Fintype.card F : ZMod n) • (1 : Module.End (ZMod n) _) = 0 := by
  obtain ⟨b⟩ := exists_basis W L n hn
  rw [sq_eq_trace_smul_sub b, trace_frobTors n hn, det_frobTors W L n hn]
  abel

/-- `tr (π ^ m | E[n]) = tseq a q m`. -/
theorem trace_frobTors_pow (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) (m : ℕ) :
    LinearMap.trace (ZMod n) _ (frobTors W L n ^ m) =
      ((tseq (RPLib.EllFq.trace W) (Fintype.card F : ℤ) m : ℤ) : ZMod n) := by
  obtain ⟨b⟩ := exists_basis W L n hn
  rw [trace_pow_eq_tseq b, trace_frobTors n hn, det_frobTors W L n hn]
  have := map_tseq (Int.castRingHom (ZMod n)) (RPLib.EllFq.trace W) (Fintype.card F : ℤ) m
  simp only [eq_intCast, Int.cast_natCast] at this
  exact this.symm

/-- **`deg (r + s π) = r² + a r s + q s²`.** -/
theorem deg_rsHom (r s : ℤ) :
    (deg (rsHom W L r s) : ℤ) =
      r ^ 2 + RPLib.EllFq.trace W * r * s + (Fintype.card F : ℤ) * s ^ 2 := by
  refine int_eq_of_zmod F L fun n _ hn => ?_
  obtain ⟨b⟩ := exists_basis W L n hn
  have h1 := det_rs_eq_deg (W := W) r s n hn
  rw [torsLin_rs, det_smul_id_add_smul b, trace_frobTors n hn, det_frobTors W L n hn] at h1
  push_cast
  rw [← h1]
  ring

variable (W L) in
include L in
/-- **`a² ≤ 4 q`**, from `deg (-a + 2 π) = 4 q - a² ≥ 0`. -/
theorem trace_sq_le : RPLib.EllFq.trace W ^ 2 ≤ 4 * Fintype.card F := by
  have h := deg_rsHom (W := W) (L := L) (-RPLib.EllFq.trace W) 2
  have h' : (deg (rsHom W L (-RPLib.EllFq.trace W) 2) : ℤ) =
      4 * Fintype.card F - RPLib.EllFq.trace W ^ 2 := by
    rw [h]; ring
  have h0 : (0 : ℤ) ≤ deg (rsHom W L (-RPLib.EllFq.trace W) 2) := Int.natCast_nonneg _
  linarith

end Frob

/-! ### The Hasse bound in Mathlib language -/

section Mathlib

/-- **Hasse**, integer form: `(q + 1 - #W(F))² ≤ 4 q`. -/
theorem trace_sq_le_four_mul {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)
    [W.IsElliptic] :
    ((Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point) ^ 2 ≤ 4 * Fintype.card F := by
  classical
  have h := trace_sq_le W (AlgebraicClosure F)
  rw [RPLib.EllFq.trace_eq] at h
  exact h

/-- **The Hasse bound** `|q + 1 - #W(F)| ≤ 2 √q` for an elliptic curve over a finite field. -/
theorem hasse_bound {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic] :
    |(Fintype.card F : ℝ) + 1 - Nat.card W.toAffine.Point| ≤ 2 * Real.sqrt (Fintype.card F) := by
  have h := trace_sq_le_four_mul W
  have h' : ((Fintype.card F : ℝ) + 1 - Nat.card W.toAffine.Point) ^ 2 ≤ 4 * Fintype.card F := by
    exact_mod_cast h
  have h2 : Real.sqrt (4 * Fintype.card F) = 2 * Real.sqrt (Fintype.card F) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h2]
  exact Real.abs_le_sqrt h'

/-- A complex root of `X² - a X + q` with `a² ≤ 4 q` has norm `√q`. -/
lemma norm_eq_sqrt_of_root {a q : ℝ} (h : a ^ 2 ≤ 4 * q) {z : ℂ}
    (hz : z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0) : ‖z‖ = Real.sqrt q := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [sq, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.zero_im, zero_mul, sub_zero, add_zero] at hre him
  have key : z.re ^ 2 + z.im ^ 2 = q := by
    have hfac : z.im * (2 * z.re - a) = 0 := by linear_combination him
    rcases mul_eq_zero.mp hfac with h1 | h1
    · rw [h1] at hre
      have h2 : (2 * z.re - a) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      have h3 : 2 * z.re - a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rw [h1]
      linear_combination -hre + z.re * h3
    · have h3 : a = 2 * z.re := by linarith
      linear_combination -hre - z.re * h3
  rw [Complex.norm_eq_sqrt_sq_add_sq, key]

/-- **Both complex roots of `X² - a X + q` have absolute value `√q`** (`a = q + 1 - #W(F)`). -/
theorem norm_root_eq_sqrt {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)
    [W.IsElliptic] {z : ℂ}
    (hz : z ^ 2 - ((Fintype.card F : ℂ) + 1 - Nat.card W.toAffine.Point) * z + Fintype.card F = 0) :
    ‖z‖ = Real.sqrt (Fintype.card F) := by
  have h := trace_sq_le_four_mul W
  refine norm_eq_sqrt_of_root (a := (Fintype.card F : ℝ) + 1 - Nat.card W.toAffine.Point) ?_ ?_
  · exact_mod_cast h
  · push_cast
    exact hz

end Mathlib

end RPLib.Hasse


