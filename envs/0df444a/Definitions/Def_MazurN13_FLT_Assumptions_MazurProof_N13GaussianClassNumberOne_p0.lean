-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianClassNumberOne_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianClassNumberOne_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:18:44.919461+00:00
-- url     : https://prove2.me/theorems/d1c40503-3d8d-48a0-b07a-f3e81d328afa
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianClassNumberOne source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianClassNumberOne

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianClassNumberOne
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFieldEquiv_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianSignature_p0
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic

set_option autoImplicit false




/-!
# Class number one for the N13 number field

The field is a totally complex sextic of discriminant `-10816`, so its
Minkowski bound is strictly below four.  Prime ideals of norms two and
three are excluded by reducing the integral sextic satisfied by
`θ = α + 9`; the finite-field arguments use Frobenius, not enumeration.
-/

open Algebra Module Polynomial Nat
open scoped nonZeroDivisors Real

namespace MazurProof.N13GaussianClassNumberOne

noncomputable section

open N13GaussianGlobalArithmetic

abbrev K := N13GaussianCubicField.K

abbrev L : Type :=
  N13GaussianNumberField.L

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L

abbrev O : Type :=
  NumberField.RingOfIntegers L

/-- The integral sextic generator in the Gaussian-cubic presentation. -/
def theta : L :=
  N13GaussianCubicField.alpha + 9

private theorem alpha_root_h :
    eval₂ (algebraMap GI L)
      N13GaussianCubicField.alpha
      N13GaussianGlobalArithmetic.h = 0 := by
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  rw [hmap, ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root N13GaussianCubicField.hK

private theorem theta_root_g :
    eval₂ (algebraMap GI L) theta
      N13GaussianGlobalArithmetic.g = 0 := by
  have h := alpha_root_h
  rw [N13GaussianGlobalArithmetic.h,
    Polynomial.eval₂_comp] at h
  simpa only [theta, eval₂_add, eval₂_X,
    eval₂_ofNat, map_ofNat] using h

private theorem theta_root_n13F :
    eval₂ (algebraMap GI L) theta
      N13GaussianGlobalArithmetic.n13F = 0 := by
  rw [← N13GaussianGlobalArithmetic.g_mul_conj,
    Polynomial.eval₂_mul, theta_root_g, zero_mul]

theorem theta_root_rat :
    eval₂ (algebraMap ℚ L) theta
      (N13SexticIrreducible.fInt.map
        (algebraMap ℤ ℚ)) = 0 := by
  rw [N13SexticIrreducible.fInt_map_rat]
  simpa [N13Mumford.f,
    N13GaussianGlobalArithmetic.n13F] using
    theta_root_n13F

theorem theta_root_fInt :
    eval₂ (algebraMap ℤ L) theta
      N13SexticIrreducible.fInt = 0 := by
  simpa only [eval₂_map,
    IsScalarTower.algebraMap_eq ℤ ℚ L] using
    theta_root_rat

theorem theta_integral :
    IsIntegral ℤ theta :=
  ⟨N13SexticIrreducible.fInt,
    N13SexticIrreducible.fInt_monic,
    theta_root_fInt⟩

/-- The sextic generator as an element of Mathlib's ring-of-integers wrapper. -/
def thetaO : O :=
  ⟨theta, theta_integral⟩

@[simp] theorem coe_thetaO :
    (thetaO : L) = theta :=
  rfl

@[simp] theorem aeval_thetaO_fInt :
    aeval thetaO N13SexticIrreducible.fInt = 0 := by
  apply NumberField.RingOfIntegers.ext
  change
    algebraMap O L
      (aeval thetaO N13SexticIrreducible.fInt) = 0
  rw [aeval_def, Polynomial.hom_eval₂]
  simpa only [coe_thetaO,
    IsScalarTower.algebraMap_eq ℤ O L] using
      theta_root_fInt

/-- Uniform interface for excluding roots over a field of prescribed size. -/
def NoRootAtCard (q : ℕ) : Prop :=
  ∀ {k : Type} [Field k] [Fintype k],
    Fintype.card k = q →
      ∀ x : k,
        eval₂ (Int.castRingHom k) x
          N13SexticIrreducible.fInt ≠ 0

private theorem pow_pos_eq_self_of_sq_eq_self
    {k : Type*} [Monoid k] {x : k}
    (hx : x ^ 2 = x) :
    ∀ n : ℕ, x ^ (n + 1) = x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      simpa only [pow_two] using hx

/-- The N13 sextic has no root over any field with two elements. -/
theorem fInt_noRoot_card_two :
    NoRootAtCard 2 := by
  intro k _ _ hcard x hroot
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP k 2 := charP_of_card_eq_prime hcard
  have hx2 : x ^ 2 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have hxpow := pow_pos_eq_self_of_sq_eq_self hx2
  have htwo : (2 : k) = 0 :=
    CharP.cast_eq_zero k 2
  have hfour : (4 : k) = 0 := by
    linear_combination 2 * htwo
  have hsix : (6 : k) = 0 := by
    linear_combination 3 * htwo
  have heval :
      x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 +
          2 * x ^ 3 + x ^ 2 + 2 * x + 1 = 0 := by
    simpa [N13SexticIrreducible.fInt] using hroot
  rw [hxpow 5, hxpow 4, hxpow 3,
    hxpow 2, hxpow 1] at heval
  rw [htwo, hfour, hsix] at heval
  have hone : (1 : k) = 0 := by
    linear_combination heval - x * htwo
  exact one_ne_zero hone

/-- The N13 sextic has no root over any field with three elements. -/
theorem fInt_noRoot_card_three :
    NoRootAtCard 3 := by
  intro k _ _ hcard x hroot
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CharP k 3 := charP_of_card_eq_prime hcard
  have hx3 : x ^ 3 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have hx6 : x ^ 6 = x ^ 2 := by
    calc
      x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ = x ^ 2 := by rw [hx3]
  have hx5 : x ^ 5 = x := by
    calc
      x ^ 5 = x ^ 3 * x ^ 2 := by ring
      _ = x * x ^ 2 := by rw [hx3]
      _ = x ^ 3 := by ring
      _ = x := hx3
  have hthree : (3 : k) = 0 :=
    CharP.cast_eq_zero k 3
  have hfour : (4 : k) = 1 := by
    linear_combination hthree
  have hsix : (6 : k) = 0 := by
    linear_combination 2 * hthree
  have heval :
      x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 +
          2 * x ^ 3 + x ^ 2 + 2 * x + 1 = 0 := by
    simpa [N13SexticIrreducible.fInt] using hroot
  rw [hx6, hx5, hx3] at heval
  by_cases hx0 : x = 0
  · subst x
    norm_num at heval
  · have hx2 : x ^ 2 = 1 := by
      simpa [hcard] using
        FiniteField.pow_card_sub_one_eq_one x hx0
    rw [hx2] at heval
    rw [hfour, hsix] at heval
    have htwox : (2 : k) * x = 0 := by
      linear_combination heval - hthree - x * hthree
    have htwo_ne : (2 : k) ≠ 0 := by
      intro htwo
      have hdiv : 3 ∣ 2 :=
        (CharP.cast_eq_zero_iff k 3 2).mp htwo
      norm_num at hdiv
    exact hx0 ((mul_eq_zero.mp htwox).resolve_left htwo_ne)

/-! ## Minkowski's bound -/

/-- The numerical Minkowski expression for the N13 field is strictly
smaller than four. -/
private theorem minkowskiBound_lt_four :
    (4 / Real.pi) ^
          NumberField.InfinitePlace.nrComplexPlaces L *
        ((Module.finrank ℚ L)! /
            (Module.finrank ℚ L) ^
              (Module.finrank ℚ L) *
          Real.sqrt |NumberField.discr L|) < 4 := by
  have hsqrt :
      Real.sqrt (|(-10816 : ℤ)| : ℝ) = 104 := by
    norm_num
  have hpi : (4 / Real.pi : ℝ) < 4 / 3 := by
    rw [div_lt_div_iff₀ Real.pi_pos
      (by norm_num : (0 : ℝ) < 3)]
    nlinarith [Real.pi_gt_three]
  have hpi3 :
      (4 / Real.pi : ℝ) ^ 3 <
        (4 / 3 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi (by positivity) (by norm_num)
  calc
    (4 / Real.pi) ^
            NumberField.InfinitePlace.nrComplexPlaces L *
          ((Module.finrank ℚ L)! /
              (Module.finrank ℚ L) ^
                (Module.finrank ℚ L) *
            Real.sqrt |NumberField.discr L|) =
        (4 / Real.pi : ℝ) ^ 3 *
          ((((6 : ℕ)! : ℝ) / (6 : ℝ) ^ 6) * 104) := by
      rw [N13GaussianSignature.nrComplexPlaces_eq_three,
        N13GaussianNumberField.finrank_Q_L,
        N13GaussianNumberField.numberField_discr,
        hsqrt]
      norm_num
    _ = (4 / Real.pi : ℝ) ^ 3 *
          (130 / 81 : ℝ) := by
      norm_num [Nat.factorial]
    _ < (4 / 3 : ℝ) ^ 3 *
          (130 / 81 : ℝ) := by
      exact mul_lt_mul_of_pos_right hpi3 (by norm_num)
    _ < 4 := by
      norm_num

/-! ## Excluding small prime ideals -/

private theorem quotient_card_eq_absNorm
    (P : Ideal O) [Fintype (O ⧸ P)] :
    Fintype.card (O ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_eq_fintype_card]

/-- A prime ideal of norm `q` would make the image of `thetaO` a root of
the N13 sextic in a field with `q` elements. -/
private theorem no_prime_absNorm_eq_of_noRoot
    {q : ℕ}
    (hq0 : q ≠ 0)
    (hNoRoot : NoRootAtCard q)
    (P : Ideal O)
    (hP : P.IsPrime)
    (hP0 : P ≠ ⊥)
    (hN : Ideal.absNorm P = q) :
    False := by
  letI : P.IsMaximal := hP.isMaximal hP0
  letI : Field (O ⧸ P) := Ideal.Quotient.field P

  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [hN]
    exact hq0

  letI : Finite (O ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp hN0
  letI : Fintype (O ⧸ P) :=
    Fintype.ofFinite _

  have hcard : Fintype.card (O ⧸ P) = q := by
    rw [quotient_card_eq_absNorm, hN]

  let quot : O →+* (O ⧸ P) :=
    Ideal.Quotient.mk P
  let t : O ⧸ P :=
    quot thetaO

  have hcast :
      quot.comp (algebraMap ℤ O) =
        Int.castRingHom (O ⧸ P) := by
    ext z
    simp [quot]

  have ht :
      eval₂ (Int.castRingHom (O ⧸ P)) t
        N13SexticIrreducible.fInt = 0 := by
    calc
      eval₂ (Int.castRingHom (O ⧸ P)) t
            N13SexticIrreducible.fInt =
          quot
            (eval₂ (algebraMap ℤ O) thetaO
              N13SexticIrreducible.fInt) := by
        simpa only [t, hcast] using
          (Polynomial.hom_eval₂
            N13SexticIrreducible.fInt
            (algebraMap ℤ O) quot thetaO).symm
      _ = quot 0 := by
        rw [show
          eval₂ (algebraMap ℤ O) thetaO
              N13SexticIrreducible.fInt = 0 by
            simpa only [aeval_def] using
              aeval_thetaO_fInt]
      _ = 0 := map_zero quot

  exact (hNoRoot (k := O ⧸ P) hcard t) ht

/-- The N13 ring of integers is a PID.  The only possible prime norms under
the Minkowski bound are two and three, both excluded by Frobenius. -/
instance isPrincipalIdealRingO :
    IsPrincipalIdealRing O := by
  refine
    _root_.RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
      (K := L) ?_
  intro I hI hnorm
  exfalso

  have hI0 : (I : Ideal O) ≠ ⊥ := by
    simpa only [Ideal.zero_eq_bot] using
      nonZeroDivisors.coe_ne_zero I
  have hNpos : 0 < Ideal.absNorm (I : Ideal O) :=
    Ideal.absNorm_pos_of_nonZeroDivisors I
  have hNlt : Ideal.absNorm (I : Ideal O) < 4 := by
    exact_mod_cast
      (lt_of_le_of_lt hnorm minkowskiBound_lt_four)
  have hNneOne :
      Ideal.absNorm (I : Ideal O) ≠ 1 := by
    intro hN
    exact hI.ne_top
      (Ideal.absNorm_eq_one_iff.mp hN)
  have hNcases :
      Ideal.absNorm (I : Ideal O) = 2 ∨
        Ideal.absNorm (I : Ideal O) = 3 := by
    omega
  rcases hNcases with hN2 | hN3
  · exact no_prime_absNorm_eq_of_noRoot
      (q := 2) (by norm_num)
      fInt_noRoot_card_two
      (I : Ideal O) hI hI0 hN2
  · exact no_prime_absNorm_eq_of_noRoot
      (q := 3) (by norm_num)
      fInt_noRoot_card_three
      (I : Ideal O) hI hI0 hN3

theorem classNumber_eq_one :
    NumberField.classNumber L = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    isPrincipalIdealRingO

end

end MazurProof.N13GaussianClassNumberOne


