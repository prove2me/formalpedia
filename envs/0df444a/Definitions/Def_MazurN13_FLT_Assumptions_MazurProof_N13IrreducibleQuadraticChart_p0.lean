-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:04:47.069145+00:00
-- url     : https://prove2.me/theorems/4e41131a-eb4c-4b64-8419-3ee9be4d2413
-- title:
--   FLT.Assumptions.MazurProof.N13IrreducibleQuadraticChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IrreducibleQuadraticChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IrreducibleQuadraticChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RepeatedRootSpread_p0
import Mathlib.NumberTheory.Padics.Hensel

set_option autoImplicit false




/-!
# The proper chart of an irreducible quadratic N13 graph

An irreducible monic quadratic over `ℚ₂` cannot have one root in each
valuation regime.  A root-free Hensel argument gives the exact Newton
dichotomy: either both ordinary coefficients are integral, or both
coefficients of the reciprocal monic quadratic are integral.

This isolates the proper chart for the remaining nonsplit degree-two
graph without constructing its splitting field or enumerating quadratic
extensions.
-/

open Polynomial

namespace MazurProof.N13IrreducibleQuadraticChart

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type := ℚ_[2]
abbrev Z₂ : Type := ℤ_[2]

/-- If the constant term is strictly smaller than the square of a
nonintegral linear coefficient, Hensel's lemma produces a root near the
linear term.  Hence the quadratic is reducible. -/
theorem quadratic_reducible_of_norm_const_lt_sq_linear
    (a b : Q₂)
    (ha : 1 < ‖a‖)
    (hb : ‖b‖ < ‖a‖ ^ 2) :
    ¬ Irreducible
        (X ^ 2 + C a * X + C b : Q₂[X]) := by
  intro hirr
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  let cQ : Q₂ := b / a ^ 2
  have hcQnorm : ‖cQ‖ < 1 := by
    rw [show ‖cQ‖ = ‖b‖ / ‖a‖ ^ 2 by
      simp [cQ, norm_div, norm_pow]]
    exact (div_lt_one (by positivity)).2 hb
  let c : Z₂ := ⟨cQ, le_of_lt hcQnorm⟩
  let F : Z₂[X] := X ^ 2 + X + C c
  have hFroot (z : Z₂) : F.aeval z = z ^ 2 + z + c := by
    simp [F, Polynomial.aeval_def, Polynomial.eval₂_C]
  have hFminus : F.aeval (-1 : Z₂) = c := by
    simpa using hFroot (-1)
  have hFderiv : F.derivative.aeval (-1 : Z₂) = -1 := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_C]
  have hHensel :
      ‖F.aeval (-1 : Z₂)‖ <
        ‖F.derivative.aeval (-1 : Z₂)‖ ^ 2 := by
    rw [hFminus, hFderiv]
    simpa [c] using hcQnorm
  obtain ⟨z, hz, _⟩ := hensels_lemma hHensel
  have hzQ :
      (z : Q₂) ^ 2 + (z : Q₂) + cQ = 0 := by
    have hz₀ : F.aeval z = 0 := hz
    rw [hFroot] at hz₀
    have hz' := congrArg (fun w : Z₂ ↦ (w : Q₂)) hz₀
    push_cast at hz'
    simpa [c] using hz'
  let r : Q₂ := a * z
  have hr :
      (X ^ 2 + C a * X + C b : Q₂[X]).IsRoot r := by
    rw [IsRoot]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
    calc
      r ^ 2 + a * r + b =
          a ^ 2 * ((z : Q₂) ^ 2 + (z : Q₂) + cQ) := by
            dsimp [r, cQ]
            field_simp
      _ = 0 := by rw [hzQ, mul_zero]
  have hdegree :=
    Polynomial.degree_eq_one_of_irreducible_of_root hirr hr
  have hdegreeTwo :
      (X ^ 2 + C a * X + C b : Q₂[X]).degree = 2 := by
    compute_degree <;> norm_num
  rw [hdegreeTwo] at hdegree
  norm_num at hdegree

/-- Root-free Newton dichotomy for an irreducible monic quadratic:
either its ordinary coefficients are integral, or the coefficients after
passing to the reciprocal monic polynomial are integral. -/
theorem irreducible_quadratic_norm_chart
    (a b : Q₂)
    (hirr :
      Irreducible
        (X ^ 2 + C a * X + C b : Q₂[X])) :
    (‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1) ∨
      (‖a / b‖ ≤ 1 ∧ ‖b⁻¹‖ ≤ 1) := by
  by_cases ha : ‖a‖ ≤ 1
  · by_cases hb : ‖b‖ ≤ 1
    · exact Or.inl ⟨ha, hb⟩
    · right
      have hb1 : 1 < ‖b‖ := lt_of_not_ge hb
      constructor
      · rw [norm_div, div_le_one (by positivity)]
        exact ha.trans hb1.le
      · rw [norm_inv, inv_le_one₀ (by positivity)]
        exact hb1.le
  · right
    have ha1 : 1 < ‖a‖ := lt_of_not_ge ha
    have hab : ‖a‖ ^ 2 ≤ ‖b‖ := by
      by_contra h
      exact
        (quadratic_reducible_of_norm_const_lt_sq_linear
          a b ha1 (lt_of_not_ge h)) hirr
    have hbpos : 0 < ‖b‖ := by
      exact lt_of_lt_of_le (by positivity : 0 < ‖a‖ ^ 2) hab
    constructor
    · rw [norm_div, div_le_one hbpos]
      exact (le_self_pow₀ ha1.le (by norm_num : 2 ≠ 0)).trans hab
    · rw [norm_inv, inv_le_one₀ hbpos]
      exact ha1.le.trans
        ((le_self_pow₀ ha1.le (by norm_num : 2 ≠ 0)).trans hab)

/-- Coefficient form of a monic quadratic. -/
theorem monic_quadratic_eq
    (p : Q₂[X])
    (hp : p.Monic)
    (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have hc₂ : p.coeff 2 = 1 := by
    calc
      p.coeff 2 = p.coeff p.natDegree :=
        congrArg p.coeff hdeg.symm
      _ = 1 := hp.coeff_natDegree
  have hpDegreeLe : p.degree ≤ 2 := by
    rw [degree_eq_natDegree hp.ne_zero, hdeg]
    norm_num
  calc
    p =
        C (p.coeff 2) * X ^ 2 +
          C (p.coeff 1) * X +
          C (p.coeff 0) :=
      p.eq_quadratic_of_degree_le_two hpDegreeLe
    _ = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      rw [hc₂, C_1]
      ring

/-- An irreducible monic quadratic has a literal integral horizontal
equation on one of the two ordinary charts.  In the second alternative
the displayed polynomial is the monic reciprocal equation for `t = x⁻¹`. -/
theorem irreducible_monic_quadratic_has_integral_chart
    (p : Q₂[X])
    (hp : p.Monic)
    (hdeg : p.natDegree = 2)
    (hirr : Irreducible p) :
    (∃ a b : Z₂,
        p =
          X ^ 2 + C (a : Q₂) * X + C (b : Q₂)) ∨
      (p.coeff 0 ≠ 0 ∧
        ∃ a b : Z₂,
          (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (p.coeff 1 / p.coeff 0) * X +
              C ((p.coeff 0)⁻¹)) := by
  have hshape := monic_quadratic_eq p hp hdeg
  have hirrShape :
      Irreducible
        (X ^ 2 +
          C (p.coeff 1) * X +
          C (p.coeff 0) : Q₂[X]) := by
    rw [← hshape]
    exact hirr
  have hconst : p.coeff 0 ≠ 0 := by
    intro hzero
    have hroot : p.IsRoot 0 := by
      rw [hshape, hzero]
      simp [IsRoot]
    have hdegree :=
      Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
    have hpdegree : p.degree = 2 := by
      rw [degree_eq_natDegree hp.ne_zero, hdeg]
      norm_num
    rw [hpdegree] at hdegree
    norm_num at hdegree
  rcases
      irreducible_quadratic_norm_chart
        (p.coeff 1) (p.coeff 0) hirrShape with
    hAffine | hInfinity
  · left
    let a : Z₂ := ⟨p.coeff 1, hAffine.1⟩
    let b : Z₂ := ⟨p.coeff 0, hAffine.2⟩
    exact ⟨a, b, by simpa [a, b] using hshape⟩
  · right
    refine ⟨hconst, ?_⟩
    let a : Z₂ :=
      ⟨p.coeff 1 / p.coeff 0, hInfinity.1⟩
    let b : Z₂ :=
      ⟨(p.coeff 0)⁻¹, hInfinity.2⟩
    exact ⟨a, b, by simp [a, b]⟩

/-- The same proper-chart dichotomy for the horizontal polynomial of an
arbitrary balanced quadratic N13 Mumford graph. -/
theorem mumford_u_irreducible_norm_chart
    (D : SexticMumford.Mumford N13AllPointAffineSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    (‖D.u.coeff 1‖ ≤ 1 ∧ ‖D.u.coeff 0‖ ≤ 1) ∨
      (‖D.u.coeff 1 / D.u.coeff 0‖ ≤ 1 ∧
        ‖(D.u.coeff 0)⁻¹‖ ≤ 1) := by
  apply irreducible_quadratic_norm_chart
  rw [← monic_quadratic_eq D.u D.u_monic hdeg]
  exact hirr

end

end MazurProof.N13IrreducibleQuadraticChart


