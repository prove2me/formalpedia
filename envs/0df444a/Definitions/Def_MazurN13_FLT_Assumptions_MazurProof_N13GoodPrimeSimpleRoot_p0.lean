-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeSimpleRoot_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeSimpleRoot_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:16:57.970175+00:00
-- url     : https://prove2.me/theorems/51a7165d-3ea0-436a-959a-963a85a7539d
-- title:
--   FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeCompletion_p0
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.ContentIdeal

set_option autoImplicit false




/-!
# The simple-root branch of the N13 denominator-prime argument

At a height-one prime away from the different, a primitive quadratic
Mumford polynomial has only two possible behaviours at the integral branch
point.  In the simple-root case, Hensel lifting gives an actual nearby root.
The value of the quadratic at the branch point is then the root difference
times a unit.  The same root difference is a square up to a unit by the
Mumford equation and the unit secant slope of the smooth sextic.

This file packages that structural argument over an arbitrary Henselian
pair.  In particular, the denominator-clearing scale is absorbed into the
square root in the fraction field; no denominator prime is enumerated.
-/

open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring

namespace MazurProof.N13GoodPrimeSimpleRoot

noncomputable section

open N13GoodPrimeCompletion

/-- Elements of a Henselian ideal may be added to a unit without changing
unitness. -/
theorem isUnit_add_of_mem_henselianIdeal
    {R : Type*} [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    {u δ : R} (hu : IsUnit u) (hδ : δ ∈ I) :
    IsUnit (u + δ) := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  letI : IsLocalHom q :=
    isLocalHom_of_le_jacobson_bot I HenselianRing.jac
  apply IsUnit.of_map q
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hδ, add_zero]
  exact hu.map q

/-- A quadratic written by its three coefficients. -/
def quadratic
    {R : Type*} [Semiring R] (a b c : R) : R[X] :=
  C a * X ^ 2 + C b * X + C c

@[simp] theorem quadratic_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).eval x =
      a * x ^ 2 + b * x + c := by
  simp [quadratic]

@[simp] theorem quadratic_derivative_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).derivative.eval x =
      2 * a * x + b := by
  simp [quadratic]
  ring

/-- Every polynomial of degree at most two is recovered from its first
three coefficients. -/
theorem eq_quadratic_of_natDegree_le_two
    {R : Type*} [CommRing R]
    (p : R[X]) (hdeg : p.natDegree ≤ 2) :
    p = quadratic (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [quadratic]
  by_cases hn1 : n = 1
  · subst n
    simp [quadratic]
  by_cases hn2 : n = 2
  · subst n
    simp [quadratic]
  have hn : 2 < n := by omega
  have hpzero :
      p.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (hdeg.trans_lt hn)
  rw [hpzero]
  simp [quadratic, coeff_C, coeff_X, coeff_X_pow,
    hn0, hn2, Ne.symm hn1]

/-- Structural isolation of the remaining quadratic regime.

In a local ring, a degree-at-most-two polynomial whose coefficients generate
the unit ideal cannot be both small and nonsimple unless its quadratic
coefficient is a unit.  Thus the only branch not handled by the simple-root
theorem is the leading-unit double-root branch. -/
theorem coeff_two_isUnit_of_content_top_small_nonsimple
    {R : Type*} [CommRing R] [IsLocalRing R]
    (p : R[X]) (hdeg : p.natDegree ≤ 2)
    (hcontent : p.contentIdeal = ⊤)
    (x : R)
    (hsmall :
      p.eval x ∈ IsLocalRing.maximalIdeal R)
    (hnonsimple :
      ¬ IsUnit (p.derivative.eval x)) :
    IsUnit (p.coeff 2) := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  by_contra ha_unit
  have hp :
      p = quadratic a b c := by
    simpa only [a, b, c] using
      eq_quadratic_of_natDegree_le_two p hdeg
  have ha_mem :
      a ∈ IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using ha_unit
  have hderiv_mem :
      2 * a * x + b ∈
        IsLocalRing.maximalIdeal R := by
    have h :=
      (show
        p.derivative.eval x ∈
          IsLocalRing.maximalIdeal R by
        simpa only [IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff] using hnonsimple)
    rw [hp] at h
    simpa using h
  have hax_mem :
      2 * a * x ∈
        IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).mul_mem_left
        (2 * x) ha_mem
    convert this using 1
    all_goals ring
  have hb_mem :
      b ∈ IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).sub_mem
        hderiv_mem hax_mem
    convert this using 1
    all_goals ring
  have hsmall' :
      a * x ^ 2 + b * x + c ∈
        IsLocalRing.maximalIdeal R := by
    rw [hp] at hsmall
    simpa using hsmall
  have hax2_mem :
      a * x ^ 2 ∈
        IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right
      (x ^ 2) ha_mem
  have hbx_mem :
      b * x ∈
        IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right
      x hb_mem
  have hc_mem :
      c ∈ IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).sub_mem
        ((IsLocalRing.maximalIdeal R).sub_mem
          hsmall' hax2_mem)
        hbx_mem
    convert this using 1
    all_goals ring
  have hle :
      p.contentIdeal ≤
        IsLocalRing.maximalIdeal R := by
    rw [Polynomial.contentIdeal_def,
      Ideal.span_le]
    intro z hz
    obtain ⟨n, -, rfl⟩ :=
      Polynomial.mem_coeffs_iff.mp hz
    rw [hp]
    by_cases hn0 : n = 0
    · subst n
      simpa [quadratic] using hc_mem
    by_cases hn1 : n = 1
    · subst n
      simpa [quadratic] using hb_mem
    by_cases hn2 : n = 2
    · subst n
      simpa [quadratic] using ha_mem
    simp [quadratic, coeff_C, coeff_X, coeff_X_pow,
      hn0, hn2, Ne.symm hn1]
  have htop :
      (⊤ : Ideal R) ≤
        IsLocalRing.maximalIdeal R := by
    rw [← hcontent]
    exact hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_unique htop)

/-- A simple approximate root of a quadratic lifts to a root for which the
complementary linear factor is a unit. -/
theorem exists_quadratic_root_with_unit_cofactor
    {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) [HenselianRing R I]
    (a b c x₀ : R)
    (hroot : a * x₀ ^ 2 + b * x₀ + c ∈ I)
    (hderiv : IsUnit (2 * a * x₀ + b)) :
    ∃ r : R,
      a * r ^ 2 + b * r + c = 0 ∧
      r - x₀ ∈ I ∧
      IsUnit (a * (x₀ + r) + b) ∧
      a * x₀ ^ 2 + b * x₀ + c =
        (x₀ - r) * (a * (x₀ + r) + b) := by
  obtain ⟨r, hr, hrx⟩ :=
    exists_quadratic_root_sub_mem_of_henselian
      I a b c x₀ hroot hderiv
  have hperturb :
      a * (r - x₀) ∈ I :=
    I.mul_mem_left a hrx
  have hcofactor :
      IsUnit (a * (x₀ + r) + b) := by
    have heq :
        a * (x₀ + r) + b =
          (2 * a * x₀ + b) + a * (r - x₀) := by
      ring
    rw [heq]
    exact
      isUnit_add_of_mem_henselianIdeal
        I hderiv hperturb
  refine ⟨r, hr, hrx, hcofactor, ?_⟩
  linear_combination hr

/-- The polynomial secant based at `x`: division by `X - x`. -/
def secantAt
    {R : Type*} [CommRing R] (p : R[X]) (x : R) : R[X] :=
  p /ₘ (X - C x)

/-- Evaluation of the secant recovers the usual difference quotient
identity without division in the coefficient ring. -/
theorem eval_sub_eval_eq_sub_mul_secantAt
    {R : Type*} [CommRing R]
    (p : R[X]) (x y : R) :
    p.eval y - p.eval x =
      (y - x) * (secantAt p x).eval y := by
  have h :=
    congrArg (Polynomial.eval y)
      (Polynomial.modByMonic_add_div p (X - C x))
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h
  change
    p.eval x + (y - x) * (secantAt p x).eval y =
      p.eval y at h
  rw [← h]
  ring

/-- The secant specializes to the derivative on the diagonal. -/
theorem secantAt_eval_self
    {R : Type*} [CommRing R]
    (p : R[X]) (x : R) :
    (secantAt p x).eval x =
      p.derivative.eval x := by
  have h :=
    congrArg (Polynomial.eval x)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
        p x)
  simpa [secantAt] using h

/-- Along one Henselian residue class, the secant slope of a smooth
polynomial remains a unit. -/
theorem secantAt_eval_isUnit_of_sub_mem
    {R : Type*} [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    (p : R[X]) (x y : R)
    (hderiv : IsUnit (p.derivative.eval x))
    (hyx : y - x ∈ I) :
    IsUnit ((secantAt p x).eval y) := by
  obtain ⟨d, hd⟩ :=
    Polynomial.sub_dvd_eval_sub y x (secantAt p x)
  have hdiff :
      (secantAt p x).eval y -
          (secantAt p x).eval x ∈ I := by
    rw [hd]
    exact I.mul_mem_right d hyx
  have hself :
      IsUnit ((secantAt p x).eval x) := by
    rw [secantAt_eval_self]
    exact hderiv
  have heq :
      (secantAt p x).eval y =
        (secantAt p x).eval x +
          ((secantAt p x).eval y -
            (secantAt p x).eval x) := by
    ring
  rw [heq]
  exact
    isUnit_add_of_mem_henselianIdeal
      I hself hdiff

/-- Local simple-root Mumford principle.

If an integral quadratic is small at `x₀` and has unit derivative there,
then its value at `x₀` is a unit times a square in the fraction field.
The polynomial relation is allowed to contain an arbitrary nonzero
homogeneous scale.  That scale enters the square root, rather than the
unit squareclass, which is exactly what removes the artificial denominator
support. -/
theorem quadratic_eval_eq_unit_mul_sq_of_simpleRoot
    {R K : Type*}
    [CommRing R] [Nontrivial R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) [HenselianRing R I]
    (a b c x₀ scale : R)
    (F V W : R[X])
    (hscale : scale ≠ 0)
    (hsmall :
      a * x₀ ^ 2 + b * x₀ + c ∈ I)
    (hquadDeriv :
      IsUnit (2 * a * x₀ + b))
    (hFroot : F.eval x₀ = 0)
    (hFderiv :
      IsUnit (F.derivative.eval x₀))
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K
          (a * x₀ ^ 2 + b * x₀ + c) =
        algebraMap R K (u : R) * z ^ 2 := by
  obtain ⟨r, hr, hrx, hlinear, hfactor⟩ :=
    exists_quadratic_root_with_unit_cofactor
      I a b c x₀ hsmall hquadDeriv
  let Q : R :=
    (secantAt F x₀).eval r
  have hQ : IsUnit Q := by
    exact
      secantAt_eval_isUnit_of_sub_mem
        I F x₀ r hFderiv hrx
  have hsecant :
      F.eval r =
        (r - x₀) * Q := by
    have h :=
      eval_sub_eval_eq_sub_mul_secantAt
        F x₀ r
    rw [hFroot, sub_zero] at h
    exact h
  have hrelation_r :=
    congrArg (Polynomial.eval r) hrelation
  simp only [eval_sub, eval_mul, eval_pow, eval_C,
    quadratic_eval, hr, zero_mul] at hrelation_r
  have hcurve :
      scale ^ 2 * ((r - x₀) * Q) =
        (V.eval r) ^ 2 := by
    rw [← hsecant]
    linear_combination hrelation_r
  let lUnit : Rˣ := hlinear.unit
  let qUnit : Rˣ := hQ.unit
  let u : Rˣ := -lUnit * qUnit⁻¹
  let z : K :=
    algebraMap R K (V.eval r) /
      algebraMap R K scale
  refine ⟨u, z, ?_⟩
  have hscaleK :
      algebraMap R K scale ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective R K).ne hscale
  have hQK :
      algebraMap R K Q ≠ 0 :=
    (hQ.map (algebraMap R K)).ne_zero
  have hcurveK :=
    congrArg (algebraMap R K) hcurve
  simp only [map_mul, map_pow] at hcurveK
  have huQ_R :
      (u : R) * Q =
        -(a * (x₀ + r) + b) := by
    calc
      (u : R) * Q =
          ((u * qUnit : Rˣ) : R) := by
        simp only [Units.val_mul]
        dsimp only [qUnit]
        rw [hQ.unit_spec]
      _ = ((-lUnit : Rˣ) : R) := by
        rw [show u * qUnit = -lUnit by
          simp [u]]
      _ = -(a * (x₀ + r) + b) := by
        simp only [Units.val_neg]
        dsimp only [lUnit]
        rw [hlinear.unit_spec]
  have huQK :=
    congrArg (algebraMap R K) huQ_R
  simp only [map_mul, map_neg] at huQK
  rw [hfactor]
  simp only [z, map_mul]
  field_simp [hscaleK]
  calc
    algebraMap R K (x₀ - r) *
          algebraMap R K (a * (x₀ + r) + b) *
          algebraMap R K scale ^ 2 =
        -(algebraMap R K scale ^ 2 *
          algebraMap R K (r - x₀) *
          algebraMap R K (a * (x₀ + r) + b)) := by
      simp only [map_sub]
      ring
    _ =
        algebraMap R K scale ^ 2 *
          algebraMap R K (r - x₀) *
          (algebraMap R K (u : R) *
            algebraMap R K Q) := by
      rw [huQK]
      ring
    _ =
        algebraMap R K (u : R) *
          (algebraMap R K scale ^ 2 *
            (algebraMap R K (r - x₀) *
              algebraMap R K Q)) := by
      ring
    _ =
        algebraMap R K (u : R) *
          algebraMap R K (V.eval r) ^ 2 := by
      rw [hcurveK]

/-- Completion form of the simple-root principle: once the global element
is identified with the quadratic evaluation in the local integers, its
height-one multiplicity is even. -/
theorem multiplicity_even_of_completion_quadratic_simpleRoot
    {A K : Type*}
    [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsDedekindDomain A]
    (v : HeightOneSpectrum A)
    {global : A} (hglobal_ne : global ≠ 0)
    (a b c x₀ scale :
      v.adicCompletionIntegers K)
    (F V W :
      (v.adicCompletionIntegers K)[X])
    (hglobal :
      algebraMap A (v.adicCompletion K) global =
        ((a * x₀ ^ 2 + b * x₀ + c :
            v.adicCompletionIntegers K) :
          v.adicCompletion K))
    (hscale : scale ≠ 0)
    (hsmall :
      a * x₀ ^ 2 + b * x₀ + c ∈
        v.completionIdeal K)
    (hquadDeriv :
      IsUnit (2 * a * x₀ + b))
    (hFroot : F.eval x₀ = 0)
    (hFderiv :
      IsUnit (F.derivative.eval x₀))
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {global})) := by
  letI :
      HenselianRing
        (v.adicCompletionIntegers K)
        (v.completionIdeal K) :=
    completionIntegers_henselianRing v
  obtain ⟨u, z, huz⟩ :=
    quadratic_eval_eq_unit_mul_sq_of_simpleRoot
      (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K)
      (v.completionIdeal K)
      a b c x₀ scale F V W hscale
      hsmall hquadDeriv hFroot hFderiv hrelation
  apply
    multiplicity_even_of_completion_eq_unit_mul_sq
      v hglobal_ne u z
  change
    algebraMap A (v.adicCompletion K) global =
      algebraMap
          (v.adicCompletionIntegers K)
          (v.adicCompletion K) (u :
            v.adicCompletionIntegers K) *
        z ^ 2
  rw [hglobal]
  exact huz

end

end MazurProof.N13GoodPrimeSimpleRoot


