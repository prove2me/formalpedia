-- Prove2me | Definitions.Def_RPLib_S3_SSHasseC
-- name    : RPLib_S3_SSHasseC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:24:35.159588+00:00
-- url     : https://prove2.me/theorems/ffca7998-f065-4360-9cbe-a53bc13ea416
-- title:
--   Weight-two Ramanujan-Petersson library: supersingular `j`-values
-- statement:
--   Supersingular `j`-values.
--
--   * `Et t : y² + xy = x³ - 36t x - t` (`Δ = t(1+1728t)²`, `c₄ = 1+1728t`, `j = 1728 + 1/t`), and the Hasse
--     polynomial `HZ p ∈ ℤ[T]` with `hasseA p (Et t) = HZ(t)` and `HZ(0) = 1` (`HF_ne_zero`).
--   * `hasseA_eq_zero_of_dvd_trace` : over `F_{p^m}`, `p` odd, `p ∣ a_E → hasseA p E = 0`.
--   * `jv_mem_of_hasseA` : a Tate curve with vanishing Hasse invariant has `j ∈ {0, 1728} ∪ (1728 + 1/·)(roots HF)`.
--   * `c₄_eq_zero_of_two_dvd_trace` : in characteristic `2`, `2 ∣ a_E` forces `a₁ = 0`, hence `c₄ = 0` (`j = 0`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_SSHasseB

/-!
# S3-DWS-Supersingular, part B4/B5: supersingular `j`-values

* `Et t : y² + xy = x³ - 36t x - t` (`Δ = t(1+1728t)²`, `c₄ = 1+1728t`, `j = 1728 + 1/t`), and the Hasse
  polynomial `HZ p ∈ ℤ[T]` with `hasseA p (Et t) = HZ(t)` and `HZ(0) = 1` (`HF_ne_zero`).
* `hasseA_eq_zero_of_dvd_trace` : over `F_{p^m}`, `p` odd, `p ∣ a_E → hasseA p E = 0`.
* `jv_mem_of_hasseA` : a Tate curve with vanishing Hasse invariant has `j ∈ {0, 1728} ∪ (1728 + 1/·)(roots HF)`.
* `c₄_eq_zero_of_two_dvd_trace` : in characteristic `2`, `2 ∣ a_E` forces `a₁ = 0`, hence `c₄ = 0` (`j = 0`).
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve RPLib RPLib.TateNF

namespace RamanujanPetersson.S3.DWSS

section HasseC

/-- The family `E_t : y² + xy = x³ - 36t x - t`. -/
def Et {F : Type*} [Field F] (t : F) : WeierstrassCurve F := ⟨1, 0, 0, -36 * t, -t⟩

/-- `g_{E_T}(Y)` over `ℤ[T]`. -/
noncomputable def GZ : (ℤ[X])[X] := C (C 4) * X ^ 3 + X ^ 2 - C (C 144 * X) * X - C (C 4 * X)

/-- The Hasse polynomial of the family, `[Y^{p-1}] g_{E_T}(Y)^{(p-1)/2} ∈ ℤ[T]`. -/
noncomputable def HZ (p : ℕ) : ℤ[X] := (GZ ^ ((p - 1) / 2)).coeff (p - 1)

/-- Its image in `F[T]`. -/
noncomputable def HF (F : Type*) [Field F] (p : ℕ) : F[X] := (HZ p).map (Int.castRingHom F)

variable {F : Type*} [Field F]

lemma Et_Δ (t : F) : (Et t).Δ = t * (1 + 1728 * t) ^ 2 := by
  simp only [Et, Δ, b₂, b₄, b₆, b₈]; ring

lemma Et_c₄ (t : F) : (Et t).c₄ = 1 + 1728 * t := by
  simp only [Et, c₄, b₂, b₄]; ring

lemma gE_Et (t : F) : gE (Et t) = C 4 * X ^ 3 + X ^ 2 - C (144 * t) * X - C (4 * t) := by
  have h2 : (Et t).b₂ = 1 := by simp only [Et, b₂]; ring
  have h4 : 2 * (Et t).b₄ = -(144 * t) := by simp only [Et, b₄]; ring
  have h6 : (Et t).b₆ = -(4 * t) := by simp only [Et, b₆]; ring
  rw [gE, h2, h4, h6, C_1, one_mul, C_neg, C_neg]; ring

lemma GZ_map (t : F) : GZ.map (eval₂RingHom (Int.castRingHom F) t) = gE (Et t) := by
  rw [gE_Et]
  simp only [GZ, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
    map_X, coe_eval₂RingHom, eval₂_C, eval₂_X, eval₂_mul]
  simp only [eq_intCast, Int.cast_ofNat]

lemma hasseA_Et (p : ℕ) (t : F) : hasseA p (Et t) = (HF F p).eval t := by
  rw [hasseA, ← GZ_map, ← Polynomial.map_pow, coeff_map, HF, eval_map, HZ, coe_eval₂RingHom]

lemma hasseA_Et_zero (p : ℕ) (hpo : p % 2 = 1) : hasseA p (Et (0 : F)) = 1 := by
  have e : gE (Et (0 : F)) = (C 4 * X + 1) * X ^ 2 := by
    rw [gE_Et]; simp only [mul_zero, map_zero, zero_mul, sub_zero]; ring
  obtain ⟨n, hn⟩ : ∃ n, p - 1 = 2 * n := ⟨(p - 1) / 2, by omega⟩
  rw [hasseA, e, hn, Nat.mul_div_cancel_left n (by norm_num : 0 < 2), mul_pow, ← pow_mul,
    coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero]
  simp

lemma HF_ne_zero (p : ℕ) (hpo : p % 2 = 1) : HF F p ≠ 0 := by
  intro h
  have := hasseA_Et_zero (F := F) p hpo
  rw [hasseA_Et, h, eval_zero] at this
  exact zero_ne_one this

lemma natDegree_HF_le (p : ℕ) : (HF F p).natDegree ≤ (HZ p).natDegree := natDegree_map_le

/-- **Bridge.** Over `F_{p^m}` (`p` odd), `p ∣ a_E` forces the Hasse invariant to vanish. -/
theorem hasseA_eq_zero_of_dvd_trace (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [Fintype F] [DecidableEq F]
    [CharP F p] {m : ℕ} (hq : Fintype.card F = p ^ m) (W : WeierstrassCurve F) [W.IsElliptic]
    (h : (p : ℤ) ∣ EllFq.trace W) : hasseA p W = 0 := by
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have e := trace_cast_eq_coeff hF W
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  rw [(CharP.intCast_eq_zero_iff F p _).mpr h, hq] at e
  rw [hq] at hodd
  have e2 : p ^ m / 2 = (p ^ m - 1) / 2 := by omega
  rw [e2] at e
  exact hasseA_eq_zero_of_hasseM p hp2 W (m := m) e.symm

/-- A Tate curve with vanishing Hasse invariant has `j ∈ {0, 1728} ∪ (1728 + 1/·)(roots HF)`. -/
theorem jv_mem_of_hasseA (p : ℕ) [Fact p.Prime] [CharP F p] {b c : F} (hD : tateDisc b c ≠ 0)
    (hA : hasseA p (tate b c) = 0) :
    jv b c = 0 ∨ jv b c = 1728 ∨ ∃ t, (HF F p).eval t = 0 ∧ jv b c = 1728 + 1 / t := by
  by_cases j0 : jv b c = 0
  · exact Or.inl j0
  by_cases j1 : jv b c = 1728
  · exact Or.inr (Or.inl j1)
  refine Or.inr (Or.inr ⟨(jv b c - 1728)⁻¹, ?_, by rw [one_div, inv_inv]; ring⟩)
  set t := (jv b c - 1728)⁻¹ with ht_def
  have ht' : t * (jv b c - 1728) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr j1)
  have ht : t ≠ 0 := inv_ne_zero (sub_ne_zero.mpr j1)
  have h1 : 1 + 1728 * t ≠ 0 := by
    intro h; apply j0
    have : jv b c * t = 0 := by linear_combination ht' + h
    exact (mul_eq_zero.mp this).resolve_right ht
  have : (Et t).IsElliptic := ⟨by rw [Et_Δ]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero ht (pow_ne_zero 2 h1))⟩
  have : (tate b c).IsElliptic := isElliptic_tate hD
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hj : ((tate b c).map (algebraMap F (AlgebraicClosure F))).j =
      ((Et t).map (algebraMap F (AlgebraicClosure F))).j := by
    rw [map_j, map_j, ← jv_eq_j]
    congr 1
    rw [j_eq_div, Et_c₄, Et_Δ, eq_div_iff (mul_ne_zero ht (pow_ne_zero 2 h1))]
    linear_combination (1 + 1728 * t) ^ 2 * ht'
  obtain ⟨V, hV⟩ := exists_variableChange_of_j_eq _ _ hj
  have hL : hasseA p ((Et t).map (algebraMap F (AlgebraicClosure F))) = 0 := by
    rw [← hV, hasseA_variableChange_eq_zero, hasseA_map, hA, map_zero]
  rw [hasseA_map, map_eq_zero] at hL
  rw [← hasseA_Et]; exact hL

/-- In characteristic `2`, a curve with `a₁ ≠ 0` has a rational `2`-torsion point. -/
theorem two_dvd_numPoints [Fintype F] [DecidableEq F] (hF : ringChar F = 2) (W : WeierstrassCurve F)
    [W.IsElliptic] (ha : W.a₁ ≠ 0) : 2 ∣ EllFq.numPoints W := by
  have : CharP F 2 := ringChar.of_eq hF
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  set x₀ := -W.a₃ / W.a₁ with hx₀
  have hx : W.a₁ * x₀ + W.a₃ = 0 := by rw [hx₀, mul_div_assoc', mul_div_cancel_left₀ _ ha, neg_add_cancel]
  obtain ⟨y₀, hy⟩ := FiniteField.isSquare_of_char_two hF (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
  have heq : W.toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff]; linear_combination y₀ * hx - hy
  have hns : W.toAffine.Nonsingular x₀ y₀ := Affine.equation_iff_nonsingular.mp heq
  have hneg : y₀ = W.toAffine.negY x₀ y₀ := by
    rw [Affine.negY]; linear_combination y₀ * h2F + hx
  have h2 : (2 : ℕ) • (Affine.Point.some x₀ y₀ hns) = 0 := by
    rw [two_nsmul]; exact Affine.Point.add_self_of_Y_eq hneg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho := addOrderOf_eq_prime h2 (Affine.Point.some_ne_zero hns)
  rw [EllFq.numPoints, ← ho]; exact addOrderOf_dvd_natCard _

/-- In characteristic `2`, `2 ∣ a_{E(b,c)}` forces `c₄ = 0`. -/
theorem c₄_eq_zero_of_two_dvd_trace [Fintype F] [DecidableEq F] (hF : ringChar F = 2) {b c : F}
    (hD : tateDisc b c ≠ 0) (h : (2 : ℤ) ∣ EllFq.trace (tate b c)) : (tate b c).c₄ = 0 := by
  have : CharP F 2 := ringChar.of_eq hF
  have : (tate b c).IsElliptic := isElliptic_tate hD
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have ha : (tate b c).a₁ = 0 := by
    by_contra ha
    have hP := two_dvd_numPoints hF (tate b c) ha
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    have hq : 2 ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hn]; exact dvd_pow_self 2 n.ne_zero
    rw [EllFq.trace] at h
    omega
  simp only [tate] at ha
  simp only [c₄, b₂, b₄, tate]
  linear_combination ((1 - c) ^ 3 - 8 * (1 - c) * b + 24 * b) * ha + 8 * b ^ 2 * h2F

end HasseC

end RamanujanPetersson.S3.DWSS


