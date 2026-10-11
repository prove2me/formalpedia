-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0006
-- name    : PNT_ZeroFree_433_0006
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:04:39.126986+00:00
-- url     : https://prove2.me/theorems/101aed03-0caa-4420-a104-fa2c900068d0
-- title:
--   Zero-free region foundations: Cusp.MatrixPhases [0006]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L19-L701

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0005

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L19-L701
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
section
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

def U (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,t;0,1]
def L (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,0;t,1]
def E : Matrix (Fin 2) (Fin 2) R := !![0,-1;1,0]

theorem upper_inversion_lower (u v : R) :
    U u * E * L (-v) = !![u + v, -1; 1, 0] := by
  simp [U,E,L]

theorem lower_add (u v : R) : L u * L v = L (u + v) := by
  simp [L]

theorem cusp19_matrix (ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    U ω * E * L (-(ω ^ 2)) = !![-1,-1;1,0] := by
  rw [upper_inversion_lower]
  have hw : ω + ω ^ 2 = -1 := by linear_combination hω
  rw [hw]

theorem cusp10_matrix (ω : R) :
    U (-ω) * E * L (-ω) = E := by
  rw [upper_inversion_lower]
  simp [E]

theorem ramified_plus_matrix (ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    L (1 + 2 * ω) = L (2 + 3 * ω) * L (ω ^ 2) := by
  rw [lower_add]
  congr 1
  linear_combination -hω

theorem ramified_minus_matrix (ω : R) :
    L (-(1 + 2 * ω)) = L (-1 - 3 * ω) * L ω := by
  rw [lower_add]
  congr 1
  ring

theorem principal_case_div_three (a b c d : R)
    (hdet : a * d - b * c = 1)
    (ha : a = 1) (hb : b = 0) (hc : c = 0) :
    (!![a,b;c,d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst a
  subst b
  subst c
  have hd : d = 1 := by simpa using hdet
  subst d
  simp [Matrix.one_fin_two]

theorem principal_case_ramified (a b c d u : R)
    (hdet : a * d - b * c = 1)
    (ha : a = 1) (hb : b = 0) (hc : c = u) :
    (!![a - u * b,b;c - u * d,d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst a
  subst b
  subst c
  have hd : d = 1 := by simpa using hdet
  subst d
  simp [Matrix.one_fin_two]

theorem principal_case_unramified (a b c d u : R)
    (hdet : a * d - b * c = 1)
    (hc : c = 1) (hd : d = 0) (hu : u = a) :
    (!![-b,a + u * b;-d,c + u * d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst c
  subst d
  subst u
  have hb : b = -1 := by linear_combination -hdet
  subst b
  simp [Matrix.one_fin_two]

end ShortDraftCusp

namespace ShortDraftConcretePhase
open ShortDraftTrace

theorem concrete_fixed_phase_congr (d a b x : eisensteinSubring)
    (hd : d ≠ 0) (hcong : d ∣ a - b) :
    breveE ((a : ℂ) * (x : ℂ) / ((lamEis : ℂ) * (d : ℂ))) =
      breveE ((b : ℂ) * (x : ℂ) / ((lamEis : ℂ) * (d : ℂ))) := by
  apply ShortDraftCRT.addChar_congr_of_dvd
    (Subring.subtype eisensteinSubring) breveE lamEis d a b x
  · have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    change (1 + 2 * ω₃ : ℂ) ≠ 0
    have hLam : 1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
      unfold ω₃
      ring
    rw [hLam]
    exact mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  · change (d : ℂ) ≠ 0
    intro h
    apply hd
    exact Subtype.ext h
  · exact breveE_period_eisenstein
  · exact hcong

end ShortDraftConcretePhase

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem norm_gaussSum_eq_sqrt_card (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  let g := gaussSum χ ψ
  have hprod : g * conj g = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq] at h
    simpa only [g, Complex.star_def] using h
  have hnorm : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    apply Complex.ofReal_injective
    calc
      ((‖g‖ ^ 2 : ℝ) : ℂ) = (‖g‖ : ℂ) ^ 2 := by norm_cast
      _ = g * conj g := (Complex.mul_conj' g).symm
      _ = (Fintype.card F : ℂ) := hprod
      _ = ((Fintype.card F : ℝ) : ℂ) := by norm_cast
  have hcard : (0 : ℝ) ≤ Fintype.card F := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (Fintype.card F)]

theorem norm_normalized_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * gaussSum χ ψ‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hsqrt : Real.sqrt (Fintype.card F) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hcard), norm_gaussSum_eq_sqrt_card χ ψ hχ hψ]
  exact inv_mul_cancel₀ hsqrt

end ShortDraftGauss

namespace EisensteinRayPhase

abbrev SquareClass := ZMod 2 × ZMod 2

def R (a b : SquareClass) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)

theorem R_symmetric (a b : SquareClass) : R a b = R b a := by
  decide +revert

theorem R_mul_left (a b c : SquareClass) : R (a + b) c = R a c * R b c := by
  decide +revert

theorem R_mul_right (a b c : SquareClass) : R a (b + c) = R a b * R a c := by
  decide +revert

theorem R_self (a : SquareClass) : R a a = (-1) ^ (a.2.val) := by
  decide +revert

end EisensteinRayPhase

namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]

theorem sextic_power_is_unit_mask (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1) (u : R) :
    χ (u ^ 6) = if IsUnit u then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
  by_cases hu : IsUnit u
  · simp [hu, MulChar.one_apply]
  · simp [hu]

end ShortDraftSextic

namespace ShortDraftGaussJacobi
open Finset

variable {F : Type*} [Field F] [Fintype F]

theorem sum_cubic_jacobi_reduction_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring

theorem jacobiSum_reduction_zero {R : Type*} [CommRing R]
    (χ : MulChar F R) (ρ : R →+* F) (m : ℕ)
    (hχ : ∀ x : F, ρ (χ x) = x ^ m)
    (hm : 2 * m < Fintype.card F - 1) :
    ρ (jacobiSum χ χ) = 0 := by
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, hχ]
  exact sum_cubic_jacobi_reduction_zero m hm

theorem cubic_jacobi_product (χ : MulChar F ℂ)
    (horder : orderOf χ = 3)
    (hchar : ringChar ℂ ≠ ringChar F) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = (Fintype.card F : ℂ) := by
  have hχ : χ ≠ 1 := by
    intro h
    simp [h] at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [horder] at ho
    norm_num at ho
  exact jacobiSum_mul_jacobiSum_inv hchar hχ hχ hχ2

theorem cubic_gauss_cube (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = (Fintype.card F : ℂ) * jacobiSum χ χ := by
  have hχ : χ ≠ 1 := by
    intro h
    simp [h] at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [horder] at ho
    norm_num at ho
  have hneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (n := 3) (by decide)
      (by simpa [horder] using (pow_orderOf_eq_one χ))
  have hj := jacobiSum_mul_nontrivial hχ2 ψ
  have hg := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ hψ
  simp only [horder, Nat.reduceSub, pow_two] at hg
  rw [hneg, one_mul] at hg
  calc
    gaussSum χ ψ ^ 3 = gaussSum χ ψ * (gaussSum χ ψ * gaussSum χ ψ) := by ring
    _ = gaussSum χ ψ * (gaussSum (χ * χ) ψ * jacobiSum χ χ) := by rw [hj]
    _ = (Fintype.card F : ℂ) * jacobiSum χ χ := by rw [← mul_assoc, hg]

theorem normalized_cubic_gauss_cube (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 3 =
      jacobiSum χ χ / (Real.sqrt (Fintype.card F : ℝ) : ℂ) := by
  let s : ℂ := Real.sqrt (Fintype.card F : ℝ)
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_pos.2 hcard).ne'
  have hs2 : s ^ 2 = (Fintype.card F : ℂ) := by
    dsimp [s]
    exact_mod_cast Real.sq_sqrt hcard.le
  rw [div_pow, cubic_gauss_cube χ ψ horder hψ, ← hs2]
  field_simp
  change s ^ 2 * jacobiSum χ χ = jacobiSum χ χ * s ^ 2
  ring

end ShortDraftGaussJacobi

namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadratic_gauss_as_square_phase (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    have hterm : (∑ x ∈ Finset.univ with x ^ 2 = y, ψ (x ^ 2)) =
        (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
      rw [Finset.sum_congr rfl (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx])]
      simp
    exact hterm
  have hcount (y : F) :
      (#{x : F | x ^ 2 = y}.toFinset : ℂ) =
        (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul]
  rw [Finset.sum_add_distrib]
  have hzero : (∑ y : F, ψ y) = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  simp only [one_mul, hzero, add_zero]
  rfl

end ShortDraftQuadraticGauss

namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]

theorem quotient_phase (R : A → A → B) (G : A → B)
    (hRright : ∀ a b c, R a (b * c) = R a b * R a c)
    (hRsym : ∀ a b, R a b = R b a)
    (hRone : ∀ a, R a 1 = 1)
    (hRtwo : ∀ a b, R a b ^ 2 = 1)
    (hGmul : ∀ a b, G (a * b) = G a * G b * R a b)
    (hGone : G 1 = 1)
    (a b : A) :
    R a a * (G a)⁻¹ * G b * R a b = G (b * a⁻¹) := by
  have hRinv (x y : A) : R x y⁻¹ = (R x y)⁻¹ := by
    have h := hRright x y y⁻¹
    rw [mul_inv_cancel, hRone] at h
    have h' : R x y⁻¹ * R x y = 1 := by
      simpa [mul_comm] using h.symm
    exact (mul_eq_one_iff_eq_inv).mp h'
  have hRinv_eq (x y : A) : R x y⁻¹ = R x y := by
    rw [hRinv]
    have hsq : R x y * R x y = 1 := by
      simpa [pow_two] using hRtwo x y
    exact ((mul_eq_one_iff_eq_inv).mp hsq).symm
  have hGaInv : G a⁻¹ = R a a * (G a)⁻¹ := by
    have h := hGmul a a⁻¹
    rw [mul_inv_cancel, hGone, hRinv_eq] at h
    have ht : G a * G a⁻¹ = (R a a)⁻¹ :=
      (mul_eq_one_iff_eq_inv).mp h.symm
    have hsq : R a a * R a a = 1 := by
      simpa [pow_two] using hRtwo a a
    have hr : (R a a)⁻¹ = R a a :=
      ((mul_eq_one_iff_eq_inv).mp hsq).symm
    calc
      G a⁻¹ = (G a)⁻¹ * (G a * G a⁻¹) := by group
      _ = R a a * (G a)⁻¹ := by rw [ht, hr]; ac_rfl
  rw [hGmul b a⁻¹, hGaInv, hRinv_eq b a, hRsym b a]
  ac_rfl

end ShortDraftQuotientPhase

namespace EisensteinEPrimaryPhase

abbrev Coord := ZMod 4 × ZMod 4
abbrev Bit := ZMod 2

def mul (x y : Coord) : Coord :=
  (x.1 * y.1 - x.2 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def odd (x : Coord) : Prop := x.1.val % 2 = 1 ∨ x.2.val % 2 = 1

instance : DecidablePred odd := fun x =>
  inferInstanceAs (Decidable (x.1.val % 2 = 1 ∨ x.2.val % 2 = 1))

def rep (e f : Bit) : Coord :=
  if f = 0 then (if e = 0 then (1, 0) else (-1, 0))
  else (if e = 0 then (1, 2) else (-1, -2))

def norm (x : Coord) : ZMod 4 :=
  x.1 * x.1 - x.1 * x.2 + x.2 * x.2

def ePrimary (x : Coord) : Prop :=
  let cube := mul (mul x x) x
  cube.1 - 2 * cube.2 = 1

instance : DecidablePred ePrimary := fun x =>
  inferInstanceAs (Decidable ((mul (mul x x) x).1 -
    2 * (mul (mul x x) x).2 = 1))

theorem exists_squareclass (x : Coord) (hx : odd x) :
    ∃ (e f : Bit) (u : Coord), odd u ∧ x = mul (rep e f) (mul u u) := by
  decide +revert

theorem squareclass_bits_unique (e f e' f' : Bit) (u v : Coord)
    (hu : odd u) (hv : odd v)
    (h : mul (rep e f) (mul u u) = mul (rep e' f') (mul v v)) :
    e = e' ∧ f = f' := by
  decide +revert

theorem ePrimary_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    ePrimary (mul (rep e f) (mul u u)) ↔ e = 0 := by
  decide +revert

theorem norm_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    norm (mul (rep e f) (mul u u)) = (if f = 0 then 1 else 3) := by
  decide +revert

def signBit (x : Coord) : Bit := if ePrimary x then 0 else 1
def normBit (x : Coord) : Bit := if norm x = 1 then 0 else 1
def bits (x : Coord) : Bit × Bit := (signBit x, normBit x)

theorem bits_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    bits (mul (rep e f) (mul u u)) = (e, f) := by
  decide +revert

theorem odd_mul (x y : Coord) (hx : odd x) (hy : odd y) : odd (mul x y) := by
  decide +revert

theorem bits_mul (x y : Coord) (hx : odd x) (hy : odd y) :
    bits (mul x y) = bits x + bits y := by
  decide +revert

end EisensteinEPrimaryPhase

namespace ShortDraftGaussianPhaseTable
abbrev SquareClass := ZMod 2 × ZMod 2

def phase (a : SquareClass) : ZMod 4 :=
  if a.2 = 0 then 0 else if a.1 = 0 then 1 else 3

def reciprocity (a b : SquareClass) : ZMod 4 :=
  2 * ((a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val : ℕ) : ZMod 4)

theorem phase_cocycle (a b : SquareClass) :
    phase (a + b) = phase a + phase b + reciprocity a b := by
  decide +revert

end ShortDraftGaussianPhaseTable

namespace ActualEisensteinCoordinates
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
private instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
def omega : O := hζ.toInteger
private def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

theorem pb_gen : pb.gen = omega := by
  exact hζ.integralPowerBasis_gen

theorem exists_coordinates (x : O) :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm

private def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
private def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩

def eval (a b : ℤ) : O := (a : O) + (b : O) * omega

private theorem eval_basis (a b : ℤ) :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp [eval, PowerBasis.basis_eq_pow, i0, i1, pb_gen, mul_comm]

theorem unique_coordinates {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos, if_neg hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos, if_neg hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1

private theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ

theorem conventional_lambda_eq_neg_delta_square :
    omega - 1 = -eval 1 2 * omega ^ 2 := by
  have hc : omega ^ 3 = 1 := hζ.toInteger_cube_eq_one
  calc
    omega - 1 = -omega ^ 2 - 2 * omega ^ 3 := by
      rw [omega_sq, hc]
      ring
    _ = -eval 1 2 * omega ^ 2 := by
      simp only [eval]
      push_cast
      ring

theorem eval_mul (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

private theorem exists_pair (x : O) :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩

def coords (x : O) : ℤ × ℤ := Classical.choose (exists_pair x)

theorem eval_coords (x : O) : eval (coords x).1 (coords x).2 = x :=
  Classical.choose_spec (exists_pair x)

def residue (x : O) : EisensteinEPrimaryPhase.Coord :=
  ((coords x).1, (coords x).2)

theorem residue_eval (a b : ℤ) :
    residue (eval a b) = ((a : ZMod 4), (b : ZMod 4)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n : ZMod 4)) h.1)
    (congrArg (fun n : ℤ => (n : ZMod 4)) h.2)

theorem residue_mul (x y : O) :
    residue (x*y) = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
  calc
    residue (x*y) = residue (eval (coords x).1 (coords x).2 *
        eval (coords y).1 (coords y).2) := by rw [eval_coords, eval_coords]
    _ = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
      rw [eval_mul, residue_eval]
      simp [residue, EisensteinEPrimaryPhase.mul]

theorem residue_pow_two (x : O) :
    residue (x^2) = EisensteinEPrimaryPhase.mul (residue x) (residue x) := by
  simpa [pow_two] using residue_mul x x

theorem congr_mod_four_of_residue_eq {x y : O}
    (h : residue x = residue y) : ∃ z : O, x-y = 4*z := by
  rw [←eval_coords x, ←eval_coords y]
  apply eval_congr_mod_four
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def lift (v : EisensteinEPrimaryPhase.Coord) : O :=
  eval (v.1.val : ℤ) (v.2.val : ℤ)

theorem residue_lift (v : EisensteinEPrimaryPhase.Coord) :
    residue (lift v) = v := by
  simp [lift, residue_eval]

theorem exists_squareclass_mod_four (x : O)
    (hx : EisensteinEPrimaryPhase.odd (residue x)) :
    ∃ (e f : EisensteinEPrimaryPhase.Bit) (u z : O),
      x - lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2 = 4 * z := by
  obtain ⟨e, f, v, hv, hclass⟩ :=
    EisensteinEPrimaryPhase.exists_squareclass (residue x) hx
  refine ⟨e, f, lift v, ?_⟩
  apply congr_mod_four_of_residue_eq
  rw [residue_mul, residue_pow_two, residue_lift, residue_lift]
  exact hclass

theorem ePrimary_squareclass_actual
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.ePrimary
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) ↔ e = 0 := by
  rw [residue_mul, residue_pow_two, residue_lift]
  exact EisensteinEPrimaryPhase.ePrimary_squareclass e f (residue u) hu

theorem norm_squareclass_actual
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.norm
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) =
      (if f = 0 then 1 else 3) := by
  rw [residue_mul, residue_pow_two, residue_lift]
  exact EisensteinEPrimaryPhase.norm_squareclass e f (residue u) hu

private theorem residue_two : residue (2 : O) = (2, 0) := by
  have h : eval 2 0 = (2 : O) := by simp [eval]
  rw [← h, residue_eval]
  norm_num

private theorem not_odd_mul_two (v : EisensteinEPrimaryPhase.Coord) :
    ¬ EisensteinEPrimaryPhase.odd
      (EisensteinEPrimaryPhase.mul (2, 0) v) := by
  decide +revert

private theorem not_odd_cast_zero (v : EisensteinEPrimaryPhase.Coord)
    (h : ¬ EisensteinEPrimaryPhase.odd v) :
    (ZMod.cast v.1 : ZMod 2) = 0 ∧
      (ZMod.cast v.2 : ZMod 2) = 0 := by
  decide +revert

theorem odd_residue_iff_not_two_dvd (x : O) :
    EisensteinEPrimaryPhase.odd (residue x) ↔ ¬ (2 : O) ∣ x := by
  constructor
  · intro hx hdiv
    obtain ⟨y, hy⟩ := hdiv
    rw [hy, residue_mul, residue_two] at hx
    exact not_odd_mul_two (residue y) hx
  · intro hdiv
    by_contra hodd
    obtain ⟨ha, hb⟩ := not_odd_cast_zero (residue x) hodd
    have ha' : ((coords x).1 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using ha
    have hb' : ((coords x).2 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using hb
    obtain ⟨a, ha2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).1 2).mp ha'
    obtain ⟨b, hb2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).2 2).mp hb'
    apply hdiv
    refine ⟨eval a b, ?_⟩
    rw [← eval_coords x]
    dsimp [eval]
    rw [ha2, hb2]
    push_cast
    ring
def rayBits (x : O) : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit :=
  EisensteinEPrimaryPhase.bits (residue x)

theorem rayBits_mul (x y : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayBits (x*y) = rayBits x + rayBits y := by
  unfold rayBits
  rw [residue_mul]
  exact EisensteinEPrimaryPhase.bits_mul _ _
    ((odd_residue_iff_not_two_dvd x).mpr hx)
    ((odd_residue_iff_not_two_dvd y).mpr hy)

def rayPhaseBits (a b : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)

private theorem rayPhaseBits_symmetric (a b : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits a b = rayPhaseBits b a := by
  decide +revert

private theorem rayPhaseBits_mul_left
    (a b c : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits (a+b) c = rayPhaseBits a c * rayPhaseBits b c := by
  decide +revert

private theorem rayPhaseBits_mul_right
    (a b c : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits a (b+c) = rayPhaseBits a b * rayPhaseBits a c := by
  decide +revert

def rayPhase (x y : O) : ℤ := rayPhaseBits (rayBits x) (rayBits y)

theorem rayPhase_symmetric (x y : O) : rayPhase x y = rayPhase y x :=
  rayPhaseBits_symmetric _ _

theorem rayPhase_mul_left (x y z : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayPhase (x*y) z = rayPhase x z * rayPhase y z := by
  unfold rayPhase
  rw [rayBits_mul x y hx hy]
  exact rayPhaseBits_mul_left _ _ _

theorem rayPhase_mul_right (x y z : O)
    (hy : ¬ (2 : O) ∣ y) (hz : ¬ (2 : O) ∣ z) :
    rayPhase x (y*z) = rayPhase x y * rayPhase x z := by
  unfold rayPhase
  rw [rayBits_mul y z hy hz]
  exact rayPhaseBits_mul_right _ _ _
end ActualEisensteinCoordinates

end

end OAI

end


