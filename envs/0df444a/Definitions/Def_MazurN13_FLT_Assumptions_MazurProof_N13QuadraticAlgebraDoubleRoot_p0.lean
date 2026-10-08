-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticAlgebraDoubleRoot_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13QuadraticAlgebraDoubleRoot_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:20:14.764858+00:00
-- url     : https://prove2.me/theorems/33f1f1d6-e203-45f9-9619-17508382e299
-- title:
--   FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeSimpleRoot_p0
import Mathlib.Algebra.QuadraticAlgebra.Basic

set_option autoImplicit false




/-!
# The quadratic-algebra double-root principle

The leading-unit double-root branch is controlled by the rank-two algebra
cut out by the Mumford quadratic.  Its distinguished root makes the
quadratic value a norm.  At a double root, the trace and norm of the
correction term are both small, so the smooth-curve secant remains a unit.
Taking norms in the Mumford relation then writes the original quadratic
value as a unit times a square.

This argument is uniform in the prime and absorbs every nonzero
denominator-clearing scale into a fourth power.  It does not enumerate
primes, residue-field elements, or squareclasses.
-/

open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

namespace MazurProof.N13QuadraticAlgebraDoubleRoot

noncomputable section

open N13GoodPrimeSimpleRoot

abbrev QA
    (R : Type*) [CommRing R]
    (B C : R) :=
  QuadraticAlgebra R (-C) (-B)

def delta
    {R : Type*} [CommRing R]
    {B C : R} (x : R) : QA R B C :=
  QuadraticAlgebra.omega -
    algebraMap R (QA R B C) x

def qtrace
    {R : Type*} [CommRing R]
    {B C : R} (z : QA R B C) : R :=
  2 * z.re - B * z.im

theorem omega_quadratic
    {R : Type*} [CommRing R]
    (B C : R) :
    (QuadraticAlgebra.omega : QA R B C) ^ 2 +
        algebraMap R (QA R B C) B *
          QuadraticAlgebra.omega +
        algebraMap R (QA R B C) C = 0 := by
  ext <;> simp [pow_two]

theorem norm_delta
    {R : Type*} [CommRing R]
    (B C x : R) :
    QuadraticAlgebra.norm (delta (B := B) (C := C) x) =
      x ^ 2 + B * x + C := by
  simp [delta, QuadraticAlgebra.norm_def]
  ring

theorem norm_algebraMap_add
    {R : Type*} [CommRing R]
    {B C : R} (r : R) (z : QA R B C) :
    QuadraticAlgebra.norm
        (algebraMap R (QA R B C) r + z) =
      r ^ 2 + r * qtrace z +
        QuadraticAlgebra.norm z := by
  simp [qtrace, QuadraticAlgebra.norm_def]
  ring

theorem qtrace_delta_mul
    {R : Type*} [CommRing R]
    (B C x : R) (z : QA R B C) :
    qtrace (delta (B := B) (C := C) x * z) =
      -(2 * x + B) * z.re +
        ((B + x) * (2 * x + B) -
          2 * (x ^ 2 + B * x + C)) * z.im := by
  simp [qtrace, delta]
  ring

theorem qtrace_delta_mul_mem
    {R : Type*} [CommRing R]
    (I : Ideal R)
    (B C x : R)
    (htrace : 2 * x + B ∈ I)
    (hnorm : x ^ 2 + B * x + C ∈ I)
    (z : QA R B C) :
    qtrace (delta (B := B) (C := C) x * z) ∈ I := by
  rw [qtrace_delta_mul]
  apply I.add_mem
  · exact I.mul_mem_right z.re (I.neg_mem htrace)
  · apply I.mul_mem_right z.im
    exact I.sub_mem
      (I.mul_mem_left (B + x) htrace)
      (I.mul_mem_left 2 hnorm)

theorem norm_delta_mul_mem
    {R : Type*} [CommRing R]
    (I : Ideal R)
    (B C x : R)
    (hnorm : x ^ 2 + B * x + C ∈ I)
    (z : QA R B C) :
    QuadraticAlgebra.norm
        (delta (B := B) (C := C) x * z) ∈ I := by
  rw [map_mul, norm_delta]
  exact I.mul_mem_right _ hnorm

theorem secant_eval_omega_isUnit
    {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) [HenselianRing R I]
    (B C x : R)
    (htrace : 2 * x + B ∈ I)
    (hnorm : x ^ 2 + B * x + C ∈ I)
    (F : R[X])
    (hFderiv : IsUnit (F.derivative.eval x)) :
    IsUnit
      ((secantAt
          (F.map
            (algebraMap R (QA R B C)))
          (algebraMap R (QA R B C) x)).eval
        (QuadraticAlgebra.omega : QA R B C)) := by
  let xS : QA R B C :=
    algebraMap R (QA R B C) x
  let Q : (QA R B C)[X] :=
    secantAt
      (F.map (algebraMap R (QA R B C))) xS
  let q : QA R B C :=
    Q.eval QuadraticAlgebra.omega
  let q0 : R := F.derivative.eval x
  have hqself :
      Q.eval xS =
        algebraMap R (QA R B C) q0 := by
    dsimp only [Q, xS, q0]
    rw [secantAt_eval_self, derivative_map,
      eval_map_apply]
  obtain ⟨d, hd⟩ :=
    Polynomial.sub_dvd_eval_sub
      (QuadraticAlgebra.omega : QA R B C)
      xS Q
  have hq :
      q =
        algebraMap R (QA R B C) q0 +
          delta (B := B) (C := C) x * d := by
    dsimp only [q]
    rw [hqself] at hd
    change
      Q.eval QuadraticAlgebra.omega -
          algebraMap R (QA R B C) q0 =
        delta (B := B) (C := C) x * d at hd
    linear_combination hd
  have htraceMem :
      qtrace
          (delta (B := B) (C := C) x * d) ∈ I :=
    qtrace_delta_mul_mem I B C x
      htrace hnorm d
  have hnormMem :
      QuadraticAlgebra.norm
          (delta (B := B) (C := C) x * d) ∈ I :=
    norm_delta_mul_mem I B C x hnorm d
  have hperturb :
      q0 *
          qtrace
            (delta (B := B) (C := C) x * d) +
        QuadraticAlgebra.norm
          (delta (B := B) (C := C) x * d) ∈ I :=
    I.add_mem (I.mul_mem_left q0 htraceMem) hnormMem
  have hnormq :
      QuadraticAlgebra.norm q =
        q0 ^ 2 +
          (q0 *
              qtrace
                (delta (B := B) (C := C) x * d) +
            QuadraticAlgebra.norm
              (delta (B := B) (C := C) x * d)) := by
    rw [hq, norm_algebraMap_add]
    ring
  apply
    (QuadraticAlgebra.isUnit_iff_norm_isUnit).mpr
  rw [hnormq]
  exact
    isUnit_add_of_mem_henselianIdeal
      I (hFderiv.pow 2) hperturb

theorem monic_quadratic_eval_eq_unit_mul_sq_of_doubleRoot
    {R K : Type*}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) [HenselianRing R I]
    (B D x scale : R)
    (F V W : R[X])
    (hscale : scale ≠ 0)
    (hsmall : x ^ 2 + B * x + D ∈ I)
    (hdouble : 2 * x + B ∈ I)
    (hFroot : F.eval x = 0)
    (hFderiv : IsUnit (F.derivative.eval x))
    (hrelation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic 1 B D * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K (x ^ 2 + B * x + D) =
        algebraMap R K (u : R) * z ^ 2 := by
  let S := QA R B D
  let xS : S := algebraMap R S x
  let t : S := QuadraticAlgebra.omega
  let d : S := delta (B := B) (C := D) x
  let FS : S[X] := F.map (algebraMap R S)
  let Q : S[X] := secantAt FS xS
  let q : S := Q.eval t
  let v : S := eval₂ (algebraMap R S) t V
  have hqUnit : IsUnit q := by
    exact
      secant_eval_omega_isUnit I B D x
        hdouble hsmall F hFderiv
  have hF_t :
      eval₂ (algebraMap R S) t F = d * q := by
    have hsec :=
      eval_sub_eval_eq_sub_mul_secantAt
        FS xS t
    have hFxS :
        FS.eval xS = 0 := by
      dsimp only [FS, xS]
      rw [eval_map_apply, hFroot, map_zero]
    rw [hFxS, sub_zero] at hsec
    simpa only [FS, Q, q, d, t, xS, delta,
      eval_map] using hsec
  have hU_t :
      eval₂ (algebraMap R S) t
          (quadratic 1 B D) = 0 := by
    simp only [quadratic, eval₂_add, eval₂_mul,
      eval₂_pow, eval₂_C, eval₂_X, map_one,
      one_mul]
    change
      (QuadraticAlgebra.omega : QA R B D) ^ 2 +
          algebraMap R (QA R B D) B *
            QuadraticAlgebra.omega +
          algebraMap R (QA R B D) D = 0
    exact omega_quadratic B D
  have hrel :=
    congrArg
      (eval₂ (algebraMap R S) t)
      hrelation
  simp only [eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_C, hU_t, zero_mul] at hrel
  have hcurve :
      algebraMap R S (scale ^ 2) * (d * q) =
        v ^ 2 := by
    rw [← hF_t]
    dsimp only [v]
    linear_combination hrel
  have hnorm :=
    congrArg
      (QuadraticAlgebra.norm :
        QA R B D →* R)
      hcurve
  dsimp only [S] at hnorm
  simp only [map_mul, map_pow,
    QuadraticAlgebra.norm_algebraMap] at hnorm
  change
    (scale ^ 2) ^ 2 *
          (QuadraticAlgebra.norm d *
            QuadraticAlgebra.norm q) =
      QuadraticAlgebra.norm v ^ 2 at hnorm
  have hnormd :
      QuadraticAlgebra.norm d =
        x ^ 2 + B * x + D := by
    exact norm_delta B D x
  rw [hnormd] at hnorm
  let nqUnit : Rˣ :=
    (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp
      hqUnit).unit
  let u : Rˣ := nqUnit⁻¹
  let z : K :=
    algebraMap R K (QuadraticAlgebra.norm v) /
      algebraMap R K (scale ^ 2)
  refine ⟨u, z, ?_⟩
  have hscaleK :
      algebraMap R K (scale ^ 2) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective R K).ne
        (pow_ne_zero 2 hscale)
  have hnq :
      (nqUnit : R) = QuadraticAlgebra.norm q := by
    dsimp only [nqUnit]
    exact
      (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp
        hqUnit).unit_spec
  have hnormK :=
    congrArg (algebraMap R K) hnorm
  simp only [map_mul, map_pow] at hnormK
  change
    algebraMap R K (x ^ 2 + B * x + D) =
      algebraMap R K (u : R) *
        (algebraMap R K (QuadraticAlgebra.norm v) /
          algebraMap R K (scale ^ 2)) ^ 2
  field_simp [hscaleK]
  have hu :
      (u : R) * QuadraticAlgebra.norm q = 1 := by
    rw [← hnq]
    simp [u]
  have huK :=
    congrArg (algebraMap R K) hu
  simp only [map_mul, map_one] at huK
  rw [← hnormK]
  calc
    algebraMap R K (x ^ 2 + B * x + D) *
          algebraMap R K (scale ^ 2) ^ 2 =
        (algebraMap R K scale ^ 2) ^ 2 *
          algebraMap R K (x ^ 2 + B * x + D) := by
      simp only [map_pow]
      ring
    _ =
        (algebraMap R K scale ^ 2) ^ 2 *
          algebraMap R K (x ^ 2 + B * x + D) *
          (algebraMap R K (u : R) *
            algebraMap R K
              (QuadraticAlgebra.norm q)) := by
      rw [huK, mul_one]
    _ =
        algebraMap R K (u : R) *
          ((algebraMap R K scale ^ 2) ^ 2 *
            (algebraMap R K (x ^ 2 + B * x + D) *
              algebraMap R K
                (QuadraticAlgebra.norm q))) := by
      ring

theorem quadratic_eval_eq_unit_mul_sq_of_doubleRoot
    {R K : Type*}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) [HenselianRing R I]
    (a b c x scale : R)
    (F V W : R[X])
    (hscale : scale ≠ 0)
    (ha : IsUnit a)
    (hsmall : a * x ^ 2 + b * x + c ∈ I)
    (hdouble : 2 * a * x + b ∈ I)
    (hFroot : F.eval x = 0)
    (hFderiv : IsUnit (F.derivative.eval x))
    (hrelation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K (a * x ^ 2 + b * x + c) =
        algebraMap R K (u : R) * z ^ 2 := by
  let au : Rˣ := ha.unit
  let ai : R := ↑(au⁻¹)
  let B : R := ai * b
  let D : R := ai * c
  have hau : (au : R) = a := ha.unit_spec
  have hai_a : ai * a = 1 := by
    rw [← hau]
    simp [ai]
  have ha_ai : a * ai = 1 := by
    rw [← hau]
    simp [ai]
  have hmonic_eval :
      x ^ 2 + B * x + D =
        ai * (a * x ^ 2 + b * x + c) := by
    dsimp only [B, D]
    calc
      x ^ 2 + ai * b * x + ai * c =
          (ai * a) * x ^ 2 +
            ai * b * x + ai * c := by
        rw [hai_a, one_mul]
      _ = ai * (a * x ^ 2 + b * x + c) := by
        ring
  have hmonic_small :
      x ^ 2 + B * x + D ∈ I := by
    rw [hmonic_eval]
    exact I.mul_mem_left ai hsmall
  have hmonic_double :
      2 * x + B ∈ I := by
    have h :
        ai * (2 * a * x + b) ∈ I :=
      I.mul_mem_left ai hdouble
    convert h using 1
    dsimp only [B]
    calc
      2 * x + ai * b =
          (ai * a) * (2 * x) + ai * b := by
        rw [hai_a, one_mul]
      _ = ai * (2 * a * x + b) := by
        ring
  have hquadratic :
      quadratic a b c =
        quadratic 1 B D * Polynomial.C a := by
    simp only [quadratic, B, D, Polynomial.C_mul,
      Polynomial.C_1, one_mul]
    have hCai_a :
        Polynomial.C ai * Polynomial.C a = 1 := by
      rw [← Polynomial.C_mul, hai_a,
        Polynomial.C_1]
    have hbterm :
        (Polynomial.C ai * Polynomial.C b * X) *
            Polynomial.C a =
          Polynomial.C b * X := by
      calc
        (Polynomial.C ai * Polynomial.C b * X) *
              Polynomial.C a =
            (Polynomial.C ai * Polynomial.C a) *
              (Polynomial.C b * X) := by
          ring
        _ = Polynomial.C b * X := by
          rw [hCai_a, one_mul]
    have hcterm :
        (Polynomial.C ai * Polynomial.C c) *
            Polynomial.C a =
          Polynomial.C c := by
      calc
        (Polynomial.C ai * Polynomial.C c) *
              Polynomial.C a =
            (Polynomial.C ai * Polynomial.C a) *
              Polynomial.C c := by
          ring
        _ = Polynomial.C c := by
          rw [hCai_a, one_mul]
    calc
      Polynomial.C a * X ^ 2 +
            Polynomial.C b * X + Polynomial.C c =
          X ^ 2 * Polynomial.C a +
            (Polynomial.C ai * Polynomial.C b * X) *
              Polynomial.C a +
            (Polynomial.C ai * Polynomial.C c) *
              Polynomial.C a := by
        rw [hbterm, hcterm]
        ring
      _ =
          (X ^ 2 +
              Polynomial.C ai * Polynomial.C b * X +
              Polynomial.C ai * Polynomial.C c) *
            Polynomial.C a := by
        ring
  have hmonic_relation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic 1 B D *
          (Polynomial.C a * W) := by
    rw [hrelation, hquadratic]
    ring
  obtain ⟨u, z, huz⟩ :=
    monic_quadratic_eval_eq_unit_mul_sq_of_doubleRoot
      (R := R) (K := K)
      I B D x scale F V (Polynomial.C a * W)
      hscale hmonic_small hmonic_double
      hFroot hFderiv hmonic_relation
  refine ⟨au * u, z, ?_⟩
  have horiginal :
      a * x ^ 2 + b * x + c =
        a * (x ^ 2 + B * x + D) := by
    rw [hmonic_eval]
    rw [← mul_assoc, ha_ai, one_mul]
  rw [horiginal, map_mul, huz]
  simp only [Units.val_mul, map_mul, hau]
  ring

theorem multiplicity_even_of_completion_quadratic_doubleRoot
    {A K : Type*}
    [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsDedekindDomain A]
    (v :
      IsDedekindDomain.HeightOneSpectrum A)
    {global : A} (hglobal_ne : global ≠ 0)
    (a b c x scale :
      v.adicCompletionIntegers K)
    (F V W :
      (v.adicCompletionIntegers K)[X])
    (hglobal :
      algebraMap A (v.adicCompletion K) global =
        ((a * x ^ 2 + b * x + c :
            v.adicCompletionIntegers K) :
          v.adicCompletion K))
    (hscale : scale ≠ 0)
    (ha : IsUnit a)
    (hsmall :
      a * x ^ 2 + b * x + c ∈
        v.completionIdeal K)
    (hnonsimple :
      ¬ IsUnit (2 * a * x + b))
    (hFroot : F.eval x = 0)
    (hFderiv :
      IsUnit (F.derivative.eval x))
    (hrelation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {global})) := by
  letI :
      HenselianRing
        (v.adicCompletionIntegers K)
        (v.completionIdeal K) :=
    N13GoodPrimeCompletion.completionIntegers_henselianRing
      v
  have hdouble :
      2 * a * x + b ∈
        v.completionIdeal K := by
    change
      2 * a * x + b ∈
        IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)
    simpa only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hnonsimple
  obtain ⟨u, z, huz⟩ :=
    quadratic_eval_eq_unit_mul_sq_of_doubleRoot
      (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K)
      (v.completionIdeal K)
      a b c x scale F V W hscale ha hsmall
      hdouble hFroot hFderiv hrelation
  apply
    N13GoodPrimeCompletion.multiplicity_even_of_completion_eq_unit_mul_sq
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

end MazurProof.N13QuadraticAlgebraDoubleRoot


