-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianOrderTwo_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianOrderTwo_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:22:02.212714+00:00
-- url     : https://prove2.me/theorems/a6cce881-2242-4a93-898c-6e31688ecbbc
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianOrderTwo source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianOrderTwo

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianOrderTwo
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubic_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogRegimes_p0
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false




/-!
# The fixed Gaussian order at two for N13

This file constructs the first ramified quotient directly from the
Gaussian cubic presentation.  We first adjoin a root `i` of `T² + 1`
over `ℤ₂`, and then a root `θ` of

`T³ + 2T² - T - 1 - i(2T(T+1))`.

Sending `i` to `1 + ε` and `θ` to the cubic residue `α` defines a
surjective ring homomorphism to `𝔽₈[ε]/(ε²)`.  Its kernel is proved to
be exactly `(1-i)² = (2)` by the two nested monic power bases.  Hence the
ramified-prime-square quotient is identified with the dual-number ring.
This is the direct quotient-ring core needed by the local N13 descent;
no ray-class enumeration is involved.

The remaining arithmetic identification with the completed maximal
order is recorded separately in `scratch/N13_GAUSSIAN_ORDER_TWO.md`.
-/

open Polynomial
open scoped CharTwo

namespace MazurProof.N13GaussianOrderTwo

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module

abbrev Z2 : Type := ℤ_[2]

/-! ## The integral Gaussian cubic order -/

/-- The Gaussian quadratic polynomial over `ℤ₂`. -/
def gaussianPolynomial : Z2[X] :=
  X ^ 2 + 1

theorem gaussianPolynomial_monic :
    gaussianPolynomial.Monic := by
  unfold gaussianPolynomial
  monicity <;> omega

theorem gaussianPolynomial_natDegree :
    gaussianPolynomial.natDegree = 2 := by
  unfold gaussianPolynomial
  compute_degree!

/-- The Gaussian `ℤ₂`-order. -/
abbrev GaussianOrder : Type :=
  AdjoinRoot gaussianPolynomial

instance gaussianOrderNontrivial : Nontrivial GaussianOrder :=
  AdjoinRoot.nontrivial (f := gaussianPolynomial) (by
    have hdeg : gaussianPolynomial.degree = 2 := by
      unfold gaussianPolynomial
      compute_degree!
    rw [hdeg]
    norm_num)

/-- The integral Gaussian generator. -/
def gaussianI : GaussianOrder :=
  AdjoinRoot.root gaussianPolynomial

theorem gaussianI_sq :
    gaussianI ^ 2 = -1 := by
  have h : gaussianI ^ 2 + 1 = 0 := by
    have hs :
        AdjoinRoot.mk gaussianPolynomial gaussianPolynomial = 0 :=
      AdjoinRoot.mk_self
    change (AdjoinRoot.mk gaussianPolynomial X) ^ 2 + 1 = 0 at hs
    exact hs
  exact eq_neg_of_add_eq_zero_left h

/-- The cubic factor of the N13 sextic over the Gaussian order. -/
def cubicPolynomial : GaussianOrder[X] :=
  X ^ 3 + 2 * X ^ 2 - X - 1 -
    C gaussianI * (2 * X * (X + 1))

theorem cubicPolynomial_monic :
    cubicPolynomial.Monic := by
  unfold cubicPolynomial
  monicity <;> omega

theorem cubicPolynomial_natDegree :
    cubicPolynomial.natDegree = 3 := by
  unfold cubicPolynomial
  compute_degree!

/-- The fixed integral Gaussian cubic order used at the prime over two. -/
abbrev Order : Type :=
  AdjoinRoot cubicPolynomial

/-- The Gaussian generator inside the cubic order. -/
def i : Order :=
  AdjoinRoot.of cubicPolynomial gaussianI

/-- The cubic generator inside the order. -/
def theta : Order :=
  AdjoinRoot.root cubicPolynomial

theorem i_sq :
    i ^ 2 = -1 := by
  rw [i, ← map_pow, gaussianI_sq, map_neg, map_one]

theorem theta_gaussian_cubic :
    theta ^ 3 + 2 * theta ^ 2 - theta - 1 -
      i * (2 * theta * (theta + 1)) = 0 := by
  have h :
      AdjoinRoot.mk cubicPolynomial cubicPolynomial = 0 :=
    AdjoinRoot.mk_self
  change
    (AdjoinRoot.mk cubicPolynomial X) ^ 3 +
          2 * (AdjoinRoot.mk cubicPolynomial X) ^ 2 -
        AdjoinRoot.mk cubicPolynomial X - 1 -
      AdjoinRoot.mk cubicPolynomial (C gaussianI) *
        (2 * AdjoinRoot.mk cubicPolynomial X *
          (AdjoinRoot.mk cubicPolynomial X + 1)) = 0 at h
  exact h

/-! ## The two nested power bases -/

/-- The basis `1,i` of the Gaussian quadratic order. -/
def gaussianBasis : Basis (Fin 2) Z2 GaussianOrder :=
  (AdjoinRoot.powerBasis' gaussianPolynomial_monic).basis.reindex
    (finCongr gaussianPolynomial_natDegree)

@[simp] theorem gaussianBasis_apply (j : Fin 2) :
    gaussianBasis j = gaussianI ^ (j : ℕ) := by
  simp [gaussianBasis, PowerBasis.basis_eq_pow, gaussianI] <;> rfl

/-- The basis `1,θ,θ²` of the cubic order over its Gaussian base. -/
def cubicBasis : Basis (Fin 3) GaussianOrder Order :=
  (AdjoinRoot.powerBasis' cubicPolynomial_monic).basis.reindex
    (finCongr cubicPolynomial_natDegree)

@[simp] theorem cubicBasis_apply (j : Fin 3) :
    cubicBasis j = theta ^ (j : ℕ) := by
  simp [cubicBasis, PowerBasis.basis_eq_pow, theta] <;> rfl

def gaussianCoeff0 (a : GaussianOrder) : Z2 :=
  gaussianBasis.repr a 0

def gaussianCoeff1 (a : GaussianOrder) : Z2 :=
  gaussianBasis.repr a 1

theorem gaussian_recompose (a : GaussianOrder) :
    a = algebraMap Z2 GaussianOrder (gaussianCoeff0 a) +
      algebraMap Z2 GaussianOrder (gaussianCoeff1 a) * gaussianI := by
  have h := gaussianBasis.sum_repr a
  rw [Fin.sum_univ_two] at h
  simpa [gaussianCoeff0, gaussianCoeff1, Algebra.smul_def] using h.symm

def cubicCoeff0 (x : Order) : GaussianOrder :=
  cubicBasis.repr x 0

def cubicCoeff1 (x : Order) : GaussianOrder :=
  cubicBasis.repr x 1

def cubicCoeff2 (x : Order) : GaussianOrder :=
  cubicBasis.repr x 2

theorem cubic_recompose (x : Order) :
    x = algebraMap GaussianOrder Order (cubicCoeff0 x) +
      algebraMap GaussianOrder Order (cubicCoeff1 x) * theta +
      algebraMap GaussianOrder Order (cubicCoeff2 x) * theta ^ 2 := by
  have h := cubicBasis.sum_repr x
  rw [Fin.sum_univ_three] at h
  simpa [cubicCoeff0, cubicCoeff1, cubicCoeff2,
    Algebra.smul_def] using h.symm

/-! ## Direct reduction to the dual-number ring -/

/-- Reduction of Gaussian `ℤ₂` to the first ramified jet. -/
def gaussianReduction : GaussianOrder →+* DualNumber F8 :=
  AdjoinRoot.lift padicScalarDualHom gaussianIDual (by
    simp only [gaussianPolynomial, eval₂_add, eval₂_X_pow,
      eval₂_one]
    rw [gaussianIDual_sq]
    exact neg_add_cancel 1)

@[simp] theorem gaussianReduction_i :
    gaussianReduction gaussianI = gaussianIDual := by
  exact AdjoinRoot.lift_root _

@[simp] theorem gaussianReduction_scalar (z : Z2) :
    gaussianReduction (AdjoinRoot.of gaussianPolynomial z) =
      padicScalarDualHom z := by
  exact AdjoinRoot.lift_of _

/-- The fixed first-jet reduction of the Gaussian cubic order. -/
def reduction : Order →+* DualNumber F8 :=
  AdjoinRoot.lift gaussianReduction thetaDual (by
    simpa [cubicPolynomial] using gaussian_cubic_jet_relation)

@[simp] theorem reduction_theta :
    reduction theta = thetaDual := by
  exact AdjoinRoot.lift_root _

@[simp] theorem reduction_i :
    reduction i = gaussianIDual := by
  simp [reduction, i]

@[simp] theorem reduction_gaussian (a : GaussianOrder) :
    reduction (algebraMap GaussianOrder Order a) =
      gaussianReduction a := by
  exact AdjoinRoot.lift_of _

@[simp] theorem reduction_scalar (z : Z2) :
    reduction (algebraMap Z2 Order z) = padicScalarDualHom z := by
  simp [reduction, gaussianReduction, AdjoinRoot.algebraMap_eq']

def residue (z : Z2) : ZMod 2 :=
  PadicInt.toZMod z

def residueF8 (z : Z2) : F8 :=
  algebraMap (ZMod 2) F8 (residue z)

@[simp] theorem gaussianReduction_algebraMap (z : Z2) :
    gaussianReduction (algebraMap Z2 GaussianOrder z) =
      padicScalarDualHom z := by
  change
    gaussianReduction (AdjoinRoot.of gaussianPolynomial z) =
      padicScalarDualHom z
  exact gaussianReduction_scalar z

theorem gaussianReduction_fst_eq (a : GaussianOrder) :
    fst (gaussianReduction a) =
      residueF8 (gaussianCoeff0 a + gaussianCoeff1 a) := by
  calc
    fst (gaussianReduction a) =
        fst (gaussianReduction
          (algebraMap Z2 GaussianOrder (gaussianCoeff0 a) +
            algebraMap Z2 GaussianOrder (gaussianCoeff1 a) * gaussianI)) :=
      congrArg fst (congrArg gaussianReduction (gaussian_recompose a))
    _ = _ := by
      rw [map_add, map_mul, gaussianReduction_algebraMap,
        gaussianReduction_i]
      simp [padicScalarDualHom, gaussianIDual, residueF8, residue,
        TrivSqZeroExt.algebraMap_eq_inl']

theorem gaussianReduction_snd_eq (a : GaussianOrder) :
    snd (gaussianReduction a) =
      residueF8 (gaussianCoeff1 a) := by
  calc
    snd (gaussianReduction a) =
        snd (gaussianReduction
          (algebraMap Z2 GaussianOrder (gaussianCoeff0 a) +
            algebraMap Z2 GaussianOrder (gaussianCoeff1 a) * gaussianI)) :=
      congrArg snd (congrArg gaussianReduction (gaussian_recompose a))
    _ = _ := by
      rw [map_add, map_mul, gaussianReduction_algebraMap,
        gaussianReduction_i]
      simp [padicScalarDualHom, gaussianIDual, residueF8, residue,
        TrivSqZeroExt.algebraMap_eq_inl']

theorem reduction_eq_coords (x : Order) :
    reduction x =
      gaussianReduction (cubicCoeff0 x) +
        gaussianReduction (cubicCoeff1 x) * thetaDual +
        gaussianReduction (cubicCoeff2 x) * thetaDual ^ 2 := by
  calc
    reduction x =
        reduction
          (algebraMap GaussianOrder Order (cubicCoeff0 x) +
            algebraMap GaussianOrder Order (cubicCoeff1 x) * theta +
            algebraMap GaussianOrder Order (cubicCoeff2 x) *
              theta ^ 2) :=
      congrArg reduction (cubic_recompose x)
    _ = _ := by
      simp only [map_add, map_mul, map_pow, reduction_gaussian,
        reduction_theta]

theorem reduction_fst_eq (x : Order) :
    fst (reduction x) =
      residueF8
          (gaussianCoeff0 (cubicCoeff0 x) +
            gaussianCoeff1 (cubicCoeff0 x)) +
        residueF8
            (gaussianCoeff0 (cubicCoeff1 x) +
              gaussianCoeff1 (cubicCoeff1 x)) * alpha +
        residueF8
            (gaussianCoeff0 (cubicCoeff2 x) +
              gaussianCoeff1 (cubicCoeff2 x)) * alpha ^ 2 := by
  rw [reduction_eq_coords]
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.fst_pow, gaussianReduction_fst_eq]
  simp [thetaDual]

theorem reduction_snd_eq (x : Order) :
    snd (reduction x) =
      residueF8 (gaussianCoeff1 (cubicCoeff0 x)) +
        residueF8 (gaussianCoeff1 (cubicCoeff1 x)) * alpha +
        residueF8 (gaussianCoeff1 (cubicCoeff2 x)) * alpha ^ 2 := by
  rw [reduction_eq_coords]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    TrivSqZeroExt.snd_pow, gaussianReduction_fst_eq,
    gaussianReduction_snd_eq]
  simp [thetaDual]

/-! ## Exactness of the first-jet quotient -/

/-- Linear independence of `1, α, α²`, obtained from the cubic
presentation rather than from an enumeration of `𝔽₈`. -/
private theorem residue_coeffs_zero
    (c0 c1 c2 : ZMod 2)
    (h :
      (c0 : F8) + (c1 : F8) * alpha +
          (c2 : F8) * alpha ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  let p : (ZMod 2)[X] :=
    C c0 + C c1 * X + C c2 * X ^ 2
  have hm : AdjoinRoot.mk residueCubic p = 0 := by
    simpa [p, alpha, map_add, map_mul, map_pow] using h
  have hdvd : residueCubic ∣ p :=
    AdjoinRoot.mk_eq_zero.mp hm
  have hpdeg : p.natDegree ≤ 2 := by
    dsimp [p]
    compute_degree
  have hdeg : p.natDegree < residueCubic.natDegree := by
    rw [residueCubic_natDegree]
    omega
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  have h0 := congrArg (fun q : (ZMod 2)[X] => q.coeff 0) hpzero
  have h1 := congrArg (fun q : (ZMod 2)[X] => q.coeff 1) hpzero
  have h2 := congrArg (fun q : (ZMod 2)[X] => q.coeff 2) hpzero
  simp [p, coeff_X_pow] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

private theorem residue_coeff0_eq_zero
    (a : GaussianOrder)
    (hsum :
      residue (gaussianCoeff0 a + gaussianCoeff1 a) = 0)
    (h1 : residue (gaussianCoeff1 a) = 0) :
    residue (gaussianCoeff0 a) = 0 := by
  have hmap :
      residue (gaussianCoeff0 a + gaussianCoeff1 a) =
        residue (gaussianCoeff0 a) + residue (gaussianCoeff1 a) :=
    map_add PadicInt.toZMod _ _
  rw [hmap, h1, add_zero] at hsum
  exact hsum

private theorem exists_eq_two_mul_of_residue_eq_zero
    (z : Z2) (hz : residue z = 0) :
    ∃ w : Z2, z = 2 * w := by
  have hker : z ∈ RingHom.ker (PadicInt.toZMod : Z2 →+* ZMod 2) :=
    RingHom.mem_ker.mpr hz
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at hker
  exact hker

private theorem gaussian_exists_eq_two_mul
    (a : GaussianOrder)
    (h0 : residue (gaussianCoeff0 a) = 0)
    (h1 : residue (gaussianCoeff1 a) = 0) :
    ∃ b : GaussianOrder, a = 2 * b := by
  obtain ⟨b0, hb0⟩ :=
    exists_eq_two_mul_of_residue_eq_zero (gaussianCoeff0 a) h0
  obtain ⟨b1, hb1⟩ :=
    exists_eq_two_mul_of_residue_eq_zero (gaussianCoeff1 a) h1
  refine ⟨algebraMap Z2 GaussianOrder b0 +
    algebraMap Z2 GaussianOrder b1 * gaussianI, ?_⟩
  rw [gaussian_recompose a, hb0, hb1]
  simp only [map_mul, map_ofNat]
  ring

private theorem dual_two_eq_zero :
    (2 : DualNumber F8) = 0 := by
  ext
  · exact charTwo
  · exact TrivSqZeroExt.snd_natCast (R := F8) (M := F8) 2

private theorem dual_three_eq_one :
    (3 : DualNumber F8) = 1 := by
  calc
    (3 : DualNumber F8) = 2 + 1 := by norm_num
    _ = 1 := by rw [dual_two_eq_zero, zero_add]

/-! ## Compatibility with the N13 descent generators -/

/-- The first fundamental unit in the integral Gaussian presentation. -/
def e1Order : Order :=
  1 - theta ^ 2 + (i - 1) * theta

/-- The second fundamental unit in the integral Gaussian presentation. -/
def e2Order : Order :=
  1 + i * theta ^ 2 + (1 + 2 * i) * theta

/-- The prime over `13` used in the fake descent. -/
def primeAOrder : Order :=
  1 - i * theta ^ 2 - (1 + i) * theta

/-- The Gaussian factor of the second prime over `13`. -/
def primeQOrder : Order :=
  2 - 3 * i

@[simp] theorem reduction_e1Order :
    reduction e1Order = (e1Jet : DualNumber F8) := by
  simp only [e1Order, map_add, map_sub, map_mul, map_pow, map_one,
    reduction_i, reduction_theta, e1Jet,
    RamifiedDlog.unitOf_val]
  ext <;> simp [gaussianIDual, thetaDual] <;> ring

@[simp] theorem reduction_e2Order :
    reduction e2Order = (e2Jet : DualNumber F8) := by
  simp only [e2Order, map_add, map_mul, map_pow, map_ofNat, map_one,
    reduction_i, reduction_theta, e2Jet,
    RamifiedDlog.unitOf_val]
  rw [dual_two_eq_zero]
  ext <;> simp [gaussianIDual, thetaDual] <;> ring

@[simp] theorem reduction_primeAOrder :
    reduction primeAOrder = (aJet : DualNumber F8) := by
  simp only [primeAOrder, map_sub, map_mul, map_pow, map_add, map_one,
    reduction_i, reduction_theta, aJet,
    RamifiedDlog.unitOf_val]
  ext <;> simp [gaussianIDual, thetaDual] <;> ring

@[simp] theorem reduction_primeQOrder :
    reduction primeQOrder = (qJet : DualNumber F8) := by
  simp only [primeQOrder, map_sub, map_ofNat, map_mul, reduction_i, qJet,
    RamifiedDlog.unitOf_val]
  rw [dual_two_eq_zero, dual_three_eq_one]
  ext <;> simp [gaussianIDual]

/-! ## The ramified prime square -/

/-- The ramified Gaussian prime generator `π = 1-i`. -/
def pi : Order :=
  1 - i

theorem pi_sq_eq :
    pi ^ 2 = -(2 * i) := by
  calc
    pi ^ 2 = 1 - 2 * i + i ^ 2 := by
      rw [pi]
      ring
    _ = -(2 * i) := by rw [i_sq]; ring

@[simp] theorem reduction_pi :
    reduction pi = (0, 1) := by
  rw [pi, map_sub, map_one, reduction_i]
  ext
  · simp [gaussianIDual]
  · simp [gaussianIDual]

@[simp] theorem reduction_pi_sq :
    reduction (pi ^ 2) = 0 := by
  rw [map_pow, reduction_pi]
  ext <;> simp

/-! ## Structural surjectivity -/

/-- Every constant element of `𝔽₈` lies in the image.  The proof uses the
power-basis presentation of `𝔽₈`, not a list of its eight elements. -/
theorem constant_mem_reduction_range (a : F8) :
    inl a ∈ reduction.range := by
  have hscalar (c : ZMod 2) :
      inl (algebraMap (ZMod 2) F8 c) ∈ reduction.range := by
    obtain ⟨z, hz⟩ :=
      ZMod.ringHom_surjective PadicInt.toZMod c
    refine ⟨algebraMap Z2 Order z, ?_⟩
    rw [reduction_scalar]
    ext <;>
      simp [padicScalarDualHom, hz,
        TrivSqZeroExt.algebraMap_eq_inl']
  have halpha : inl alpha ∈ reduction.range := by
    exact ⟨theta, by simp [thetaDual]⟩
  induction a using AdjoinRoot.induction_on with
  | ih p =>
      have hp :
          inl (p.eval₂ (algebraMap (ZMod 2) F8) alpha) ∈
            reduction.range := by
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
            rw [eval₂_add]
            have hsum := reduction.range.add_mem hp hq
            convert hsum using 1
            ext <;> simp
        | monomial n c =>
            rw [eval₂_monomial]
            have hprod :=
              reduction.range.mul_mem
                (hscalar c) (reduction.range.pow_mem halpha n)
            convert hprod using 1
            ext <;> simp
      have heq :
          p.eval₂ (algebraMap (ZMod 2) F8) alpha =
            AdjoinRoot.mk residueCubic p := by
        simpa only [alpha, aeval_def] using
          AdjoinRoot.aeval_eq p
      rw [← heq]
      exact hp

/-- The fixed Gaussian cubic reduction is onto the full dual-number ring.
Constants give the residue field, while `π` supplies `ε`. -/
theorem reduction_surjective :
    Function.Surjective reduction := by
  intro z
  change z ∈ reduction.range
  have hz0 : inl (fst z) ∈ reduction.range :=
    constant_mem_reduction_range (fst z)
  have hz1 : inl (snd z) ∈ reduction.range :=
    constant_mem_reduction_range (snd z)
  have hepsilon : ((0, 1) : DualNumber F8) ∈ reduction.range :=
    ⟨pi, reduction_pi⟩
  have h :=
    reduction.range.add_mem hz0
      (reduction.range.mul_mem hz1 hepsilon)
  convert h using 1
  ext <;> simp

/-- The square of the ramified Gaussian prime in the fixed order. -/
def ramifiedSquareIdeal : Ideal Order :=
  Ideal.span ({pi ^ 2} : Set Order)

/-- In this Gaussian presentation `(1-i)²` differs from `2` by a unit.
Thus the ramified-prime square quotient is exactly reduction modulo two. -/
theorem ramifiedSquareIdeal_eq_two :
    ramifiedSquareIdeal =
      Ideal.span ({(2 : Order)} : Set Order) := by
  have hunit : IsUnit (-i) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨i, ?_⟩
    rw [neg_mul, show i * i = i ^ 2 by rw [pow_two], i_sq]
    simp
  rw [ramifiedSquareIdeal, pi_sq_eq]
  have hgen : -(2 * i) = (-i) * (2 : Order) := by ring
  rw [hgen]
  exact Ideal.span_singleton_mul_left_unit hunit 2

theorem ramifiedSquareIdeal_le_ker :
    ramifiedSquareIdeal ≤ RingHom.ker reduction := by
  rw [ramifiedSquareIdeal, Ideal.span_le]
  rintro x (rfl : x = pi ^ 2)
  exact RingHom.mem_ker.mpr reduction_pi_sq

theorem ker_reduction_le_ramifiedSquareIdeal :
    RingHom.ker reduction ≤ ramifiedSquareIdeal := by
  intro x hx
  have hred : reduction x = 0 :=
    RingHom.mem_ker.mp hx
  have hsnd : snd (reduction x) = 0 := by
    rw [hred]
    rfl
  rw [reduction_snd_eq] at hsnd
  obtain ⟨h10, h11, h12⟩ :=
    residue_coeffs_zero
      (residue (gaussianCoeff1 (cubicCoeff0 x)))
      (residue (gaussianCoeff1 (cubicCoeff1 x)))
      (residue (gaussianCoeff1 (cubicCoeff2 x)))
      (by simpa [residueF8] using hsnd)
  have hfst : fst (reduction x) = 0 := by
    rw [hred]
    rfl
  rw [reduction_fst_eq] at hfst
  obtain ⟨hs0, hs1, hs2⟩ :=
    residue_coeffs_zero
      (residue
        (gaussianCoeff0 (cubicCoeff0 x) +
          gaussianCoeff1 (cubicCoeff0 x)))
      (residue
        (gaussianCoeff0 (cubicCoeff1 x) +
          gaussianCoeff1 (cubicCoeff1 x)))
      (residue
        (gaussianCoeff0 (cubicCoeff2 x) +
          gaussianCoeff1 (cubicCoeff2 x)))
      (by simpa [residueF8] using hfst)
  have h00 :
      residue (gaussianCoeff0 (cubicCoeff0 x)) = 0 :=
    residue_coeff0_eq_zero (cubicCoeff0 x) hs0 h10
  have h01 :
      residue (gaussianCoeff0 (cubicCoeff1 x)) = 0 :=
    residue_coeff0_eq_zero (cubicCoeff1 x) hs1 h11
  have h02 :
      residue (gaussianCoeff0 (cubicCoeff2 x)) = 0 :=
    residue_coeff0_eq_zero (cubicCoeff2 x) hs2 h12
  obtain ⟨d0, hd0⟩ :=
    gaussian_exists_eq_two_mul (cubicCoeff0 x) h00 h10
  obtain ⟨d1, hd1⟩ :=
    gaussian_exists_eq_two_mul (cubicCoeff1 x) h01 h11
  obtain ⟨d2, hd2⟩ :=
    gaussian_exists_eq_two_mul (cubicCoeff2 x) h02 h12
  rw [ramifiedSquareIdeal_eq_two, Ideal.mem_span_singleton]
  refine ⟨algebraMap GaussianOrder Order d0 +
    algebraMap GaussianOrder Order d1 * theta +
    algebraMap GaussianOrder Order d2 * theta ^ 2, ?_⟩
  rw [cubic_recompose x, hd0, hd1, hd2]
  simp only [map_mul, map_ofNat]
  ring

theorem ker_reduction_eq_ramifiedSquareIdeal :
    RingHom.ker reduction = ramifiedSquareIdeal :=
  le_antisymm ker_reduction_le_ramifiedSquareIdeal
    ramifiedSquareIdeal_le_ker

/-- The fixed order modulo the square of its ramified Gaussian prime. -/
abbrev OrderModRamifiedSquare : Type :=
  Order ⧸ ramifiedSquareIdeal

/-- Reduction after quotienting by `(1-i)²`. -/
def quotientReduction :
    OrderModRamifiedSquare →+* DualNumber F8 :=
  Ideal.Quotient.lift ramifiedSquareIdeal reduction
    ramifiedSquareIdeal_le_ker

@[simp] theorem quotientReduction_mk (x : Order) :
    quotientReduction (Ideal.Quotient.mk ramifiedSquareIdeal x) =
      reduction x := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem quotientReduction_surjective :
    Function.Surjective quotientReduction := by
  intro z
  obtain ⟨x, rfl⟩ := reduction_surjective z
  exact ⟨Ideal.Quotient.mk ramifiedSquareIdeal x,
    quotientReduction_mk x⟩

theorem quotientReduction_injective :
    Function.Injective quotientReduction :=
  RingHom.lift_injective_of_ker_le_ideal
    ramifiedSquareIdeal
    (fun a ha =>
      RingHom.mem_ker.mp (ramifiedSquareIdeal_le_ker ha))
    ker_reduction_le_ramifiedSquareIdeal

/-- The fixed Gaussian order modulo the ramified-prime square is exactly
the dual-number ring over `𝔽₈`. -/
noncomputable def orderModRamifiedSquareEquiv :
    OrderModRamifiedSquare ≃+* DualNumber F8 :=
  RingEquiv.ofBijective quotientReduction
    ⟨quotientReduction_injective, quotientReduction_surjective⟩

@[simp] theorem orderModRamifiedSquareEquiv_mk (x : Order) :
    orderModRamifiedSquareEquiv
        (Ideal.Quotient.mk ramifiedSquareIdeal x) =
      reduction x :=
  quotientReduction_mk x

end

end MazurProof.N13GaussianOrderTwo


