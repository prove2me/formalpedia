-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerIdentityFiber_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerIdentityFiber_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:30:59.508763+00:00
-- url     : https://prove2.me/theorems/6c00f359-ba21-45e6-89e6-7096ddba4992
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordOrientedFullKummer_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchLeading_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_QuadraticNormRigidity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_QuadraticAdjoinRootNorm_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_PadeZeroConstantSquare_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_LinearAdjoinRootScalar_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SquareRootUnitLift_p0
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false




/-!
# The remaining identity fibre of the N13 full Kummer map

The target algebra already shows that the N13 full Kummer map has one
kernel fibre.  This file unfolds that fibre instead of treating it as an
opaque equality:

* triviality in the full target is equivalent to an explicit full-gauge
  witness `(β,q)`;
* divisibility by two in the oriented Picard quotient is equivalent to an
  explicit square root of the raw oriented fractional ideal.

The remaining geometric seam is closed here by a dimension-theoretic Padé
numerator, homogeneous resultants, quadratic-algebra rigidity, and Cantor
ideal identities.  No representative enumeration or finite certificate is
used.
-/

namespace MazurProof.N13MumfordFullKummerIdentityFiber

noncomputable section

open Polynomial
open SexticMumford
open scoped nonZeroDivisors

abbrev M : SexticMumford.Model ℚ :=
  N13LowDegreeKummerHom.M

abbrev O : SexticMumford.InfinityOrder M :=
  N13LowDegreeKummerHom.O

abbrev G : Type :=
  N13LowDegreeKummerHom.G

abbrev L : Type :=
  N13FullNormPair.L

abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep

/-! ## Unfolding the full-gauge fibre -/

/-- Equality to one in the full target is exactly membership in the product
of the square/norm and scalar/cubic gauges. -/
theorem orientedMumfordFullClass_eq_one_iff_exists_gauge
    (D : LowRep) :
    N13MumfordOrientedFullKummer.orientedMumfordFullClass D = 1 ↔
      ∃ β : Lˣ, ∃ q : ℚˣ,
        N13MumfordOrientedFullKummer.orientedMumfordNormPair D =
          EvenSexticNormPair.chi
              N13FullNormPair.normUnits β *
            EvenSexticNormPair.iota
              N13FullNormPair.normUnits
              N13FullNormPair.scalarUnits
              N13FullNormPair.normUnits_scalarUnits q := by
  constructor
  · intro hD
    have hmem :
        N13MumfordOrientedFullKummer.orientedMumfordNormPair D ∈
          EvenSexticNormPair.fullGauge
            N13FullNormPair.normUnits
            N13FullNormPair.scalarUnits
            N13FullNormPair.normUnits_scalarUnits :=
      (QuotientGroup.eq_one_iff _).mp hD
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      Subgroup.mem_sup.mp hmem
    obtain ⟨β, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨β, q, hxy.symm⟩
  · rintro ⟨β, q, hD⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [hD]
    apply Subgroup.mul_mem_sup
    · exact ⟨β, rfl⟩
    · exact ⟨q, rfl⟩

/-- Coordinate form of the same witness.  The first equation is the
branch-algebra square relation; the second is the orientation/norm-root
compatibility which is lost by the fake target. -/
theorem orientedMumfordFullClass_eq_one_iff_exists_coordinates
    (D : LowRep) :
    N13MumfordOrientedFullKummer.orientedMumfordFullClass D = 1 ↔
      ∃ β : Lˣ, ∃ q : ℚˣ,
        N13MumfordKummerValue.uThetaUnit
              (N13LowDegreeKummerHom.asMumford D) =
            β ^ 2 * N13FullNormPair.scalarUnits q ∧
        N13MumfordOrientedFullKummer.orientationSignUnit D *
              N13MumfordKummerNorm.normRootUnit D =
            N13FullNormPair.normUnits β * q ^ 3 := by
  rw [orientedMumfordFullClass_eq_one_iff_exists_gauge]
  constructor
  · rintro ⟨β, q, hpair⟩
    refine ⟨β, q, ?_, ?_⟩
    · exact congrArg
        (EvenSexticNormPair.fstHom
          N13FullNormPair.normUnits) hpair
    · exact congrArg
        (EvenSexticNormPair.sndHom
          N13FullNormPair.normUnits) hpair
  · rintro ⟨β, q, hfst, hsnd⟩
    refine ⟨β, q, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hfst
    · exact hsnd

/-- The actual chosen full Kummer lift therefore supplies the same two
coordinate equations for its chosen low-degree representative. -/
theorem orientedFullKummer_eq_one_iff_exists_coordinates
    (P : G) :
    N13MumfordOrientedFullKummer.orientedFullKummer P = 1 ↔
      ∃ β : Lˣ, ∃ q : ℚˣ,
        N13MumfordKummerValue.uThetaUnit
              (N13LowDegreeKummerHom.asMumford
                (N13LowDegreeKummerHom.representative P)) =
            β ^ 2 * N13FullNormPair.scalarUnits q ∧
        N13MumfordOrientedFullKummer.orientationSignUnit
              (N13LowDegreeKummerHom.representative P) *
              N13MumfordKummerNorm.normRootUnit
                (N13LowDegreeKummerHom.representative P) =
            N13FullNormPair.normUnits β * q ^ 3 := by
  exact
    orientedMumfordFullClass_eq_one_iff_exists_coordinates
      (N13LowDegreeKummerHom.representative P)

private theorem scalarUnits_neg (q : ℚˣ) :
    N13FullNormPair.scalarUnits (-q) =
      -N13FullNormPair.scalarUnits q := by
  apply Units.ext
  change
    algebraMap ℚ L (-(q : ℚ)) =
      -algebraMap ℚ L (q : ℚ)
  exact map_neg (algebraMap ℚ L) (q : ℚ)

/-- Multiplying the branch square root by the Gaussian `i` and the scalar
by `-1` preserves the first gauge coordinate and flips the norm-root
coordinate.  Thus every full-gauge witness can be put in the sign convention
needed by the Padé resultant argument, independently of the representative's
original infinity integer. -/
theorem exists_negative_norm_gauge_coordinates
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      N13MumfordOrientedFullKummer.orientationSignUnit D *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    ∃ β' : Lˣ, ∃ q' : ℚˣ,
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
          β' ^ 2 * N13FullNormPair.scalarUnits q' ∧
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
          N13FullNormPair.normUnits β' * q' ^ 3 := by
  rcases
      N13FullNormPair.ratUnit_sq_eq_one
        (N13MumfordOrientedFullKummer.orientationSignUnit D)
        (N13MumfordOrientedFullKummer.orientationSignUnit_sq D) with
    hplus | hminus
  · refine
      ⟨N13FullNormPairGaussian.sexticIUnit * β,
        -q, ?_, ?_⟩
    · rw [hfst, mul_pow,
        N13FullNormPairGaussian.sexticIUnit_sq,
        scalarUnits_neg]
      simp only [neg_mul, mul_neg, neg_neg]
      simp
    · have hsnd' :
          N13MumfordKummerNorm.normRootUnit D =
            N13FullNormPair.normUnits β * q ^ 3 := by
        simpa only [hplus, one_mul] using hsnd
      rw [hsnd', map_mul,
        N13FullNormPairGaussian.normUnits_sexticIUnit,
        one_mul, neg_pow]
      norm_num
  · exact ⟨β, q, hfst, by
      simpa only [hminus] using hsnd⟩

/-! ## The canonical polynomial square-root witness -/

private theorem sextic_f_monic :
    N13SexticSquareclass.f.Monic := by
  exact N13Mumford.f_monic (K := ℚ)

/-- The degree-bounded polynomial representative of a full-gauge square
root in the sextic branch algebra. -/
def branchSquarePolynomial (β : Lˣ) : ℚ[X] :=
  AdjoinRoot.modByMonicHom
    sextic_f_monic (β : L)

@[simp] theorem mk_branchSquarePolynomial (β : Lˣ) :
    AdjoinRoot.mk N13SexticSquareclass.f
        (branchSquarePolynomial β) =
      (β : L) := by
  exact
    AdjoinRoot.mk_leftInverse
      sextic_f_monic (β : L)

/-- The canonical representative has degree strictly below the sextic. -/
theorem branchSquarePolynomial_natDegree_lt_six (β : Lˣ) :
    (branchSquarePolynomial β).natDegree < 6 := by
  obtain ⟨b, hb⟩ :=
    AdjoinRoot.mk_surjective (β : L)
  rw [branchSquarePolynomial, ← hb,
    AdjoinRoot.modByMonicHom_mk]
  have hfne :
      N13SexticSquareclass.f ≠ 1 := by
    intro hf
    have hdegree :=
      congrArg Polynomial.natDegree hf
    change
      (N13Mumford.f ℚ).natDegree =
        (1 : ℚ[X]).natDegree at hdegree
    rw [N13Mumford.f_natDegree, natDegree_one] at hdegree
    omega
  simpa [N13SexticSquareclass.f,
    N13Mumford.f_natDegree] using
      (Polynomial.natDegree_modByMonic_lt b
        sextic_f_monic hfne)

/-- The first full-gauge coordinate is equivalently an actual polynomial
congruence modulo the sextic.  This is the algebraic input from which the
missing curve ideal square root must be constructed. -/
theorem branchSquarePolynomial_congruence
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q) :
    N13Mumford.f ℚ ∣
      D.toSemi.u -
        Polynomial.C (q : ℚ) * branchSquarePolynomial β ^ 2 := by
  change N13SexticSquareclass.f ∣
    D.toSemi.u -
      Polynomial.C (q : ℚ) * branchSquarePolynomial β ^ 2
  apply AdjoinRoot.mk_eq_zero.mp
  rw [map_sub, map_mul, map_pow, AdjoinRoot.mk_C,
    mk_branchSquarePolynomial]
  have hval :=
    congrArg (fun z : Lˣ => (z : L)) hfst
  change
    N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) =
      (β : L) ^ 2 * algebraMap ℚ L (q : ℚ) at hval
  rw [N13MumfordKummerValue.uTheta_eq_mk] at hval
  change
    AdjoinRoot.mk N13SexticSquareclass.f D.toSemi.u =
      (β : L) ^ 2 * algebraMap ℚ L (q : ℚ) at hval
  rw [hval]
  rw [AdjoinRoot.algebraMap_eq]
  ring

/-! ## The structural Padé numerator -/

/-- Multiply a quadratic numerator by the chosen branch square root and
reduce modulo the sextic. -/
def padeRemainderMap (B : ℚ[X]) :
    Polynomial.degreeLT ℚ 3 →ₗ[ℚ] ℚ[X] :=
  (Polynomial.modByMonicHom N13SexticSquareclass.f).comp
    ((LinearMap.mulRight ℚ B).comp
      (Polynomial.degreeLT ℚ 3).subtype)

/-- Only the degree-four and degree-five coefficients obstruct a sextic
remainder from having degree at most three. -/
def padeHighCoeffMap (B : ℚ[X]) :
    Polynomial.degreeLT ℚ 3 →ₗ[ℚ] ℚ × ℚ :=
  (LinearMap.prod
      (Polynomial.lcoeff ℚ 4)
      (Polynomial.lcoeff ℚ 5)).comp
    (padeRemainderMap B)

@[simp] theorem padeRemainderMap_apply
    (B : ℚ[X]) (a : Polynomial.degreeLT ℚ 3) :
    padeRemainderMap B a =
      ((a : ℚ[X]) * B) %ₘ N13SexticSquareclass.f :=
  rfl

@[simp] theorem padeHighCoeffMap_apply
    (B : ℚ[X]) (a : Polynomial.degreeLT ℚ 3) :
    padeHighCoeffMap B a =
      (((((a : ℚ[X]) * B) %ₘ
          N13SexticSquareclass.f).coeff 4),
       ((((a : ℚ[X]) * B) %ₘ
          N13SexticSquareclass.f).coeff 5)) := by
  rfl

/-- The Padé numerator is a dimension argument: a three-dimensional space
maps to the two high coefficients, so its kernel contains a nonzero
quadratic numerator.  This is the structural replacement for searching
over coefficient tuples. -/
theorem exists_pade_numerator (B : ℚ[X]) :
    ∃ a : Polynomial.degreeLT ℚ 3,
      a ≠ 0 ∧ padeHighCoeffMap B a = 0 := by
  have hdim :
      Module.finrank ℚ (ℚ × ℚ) <
        Module.finrank ℚ (Polynomial.degreeLT ℚ 3) := by
    rw [Module.finrank_prod,
      Module.finrank_self,
      Module.finrank_eq_card_basis
        (Polynomial.degreeLT.basis ℚ 3),
      Fintype.card_fin]
    norm_num
  have hker :
      LinearMap.ker (padeHighCoeffMap B) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨a, haKer, ha0⟩ :=
    (Submodule.ne_bot_iff
      (LinearMap.ker (padeHighCoeffMap B))).mp hker
  exact ⟨a, ha0, LinearMap.mem_ker.mp haKer⟩

/-- A nonzero Padé numerator has degree at most two. -/
theorem padeNumerator_natDegree_le_two
    (a : Polynomial.degreeLT ℚ 3) (ha : a ≠ 0) :
    (a : ℚ[X]).natDegree ≤ 2 := by
  have haPoly : (a : ℚ[X]) ≠ 0 := by
    exact fun h => ha (Subtype.ext h)
  have hlt :
      (a : ℚ[X]).natDegree < 3 :=
    (natDegree_lt_iff_degree_lt haPoly).mpr
      (Polynomial.mem_degreeLT.mp a.property)
  omega

/-- Killing the two high coefficients leaves a remainder of degree at most
three, since reduction modulo the monic sextic already kills every
coefficient from degree six upward. -/
theorem padeRemainder_natDegree_le_three
    (B : ℚ[X]) (a : Polynomial.degreeLT ℚ 3)
    (haKer : padeHighCoeffMap B a = 0) :
    (padeRemainderMap B a).natDegree ≤ 3 := by
  have hcoeff :=
    congrArg (fun z : ℚ × ℚ => z) haKer
  have h4 :
      (padeRemainderMap B a).coeff 4 = 0 := by
    exact congrArg Prod.fst hcoeff
  have h5 :
      (padeRemainderMap B a).coeff 5 = 0 := by
    exact congrArg Prod.snd hcoeff
  have hfne :
      N13SexticSquareclass.f ≠ 1 := by
    intro hf
    have hdegree :=
      congrArg Polynomial.natDegree hf
    change
      (N13Mumford.f ℚ).natDegree =
        (1 : ℚ[X]).natDegree at hdegree
    rw [N13Mumford.f_natDegree, natDegree_one] at hdegree
    omega
  have hrem :
      (padeRemainderMap B a).natDegree < 6 := by
    simpa only [padeRemainderMap_apply,
      N13SexticSquareclass.f,
      N13Mumford.f_natDegree] using
        (Polynomial.natDegree_modByMonic_lt
          ((a : ℚ[X]) * B) sextic_f_monic hfne)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn4 : n = 4
  · simpa only [hn4] using h4
  by_cases hn5 : n = 5
  · simpa only [hn5] using h5
  have hn6 : 6 ≤ n := by omega
  exact coeff_eq_zero_of_natDegree_lt
    (hrem.trans_le hn6)

/-- The Padé kernel turns the branch-algebra congruence into a single
sextic polynomial identity.  Degree at most six makes the quotient by the
monic sextic a scalar. -/
theorem exists_pade_sextic_scalar
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0) :
    ∃ c : ℚ,
      Polynomial.C (q : ℚ) *
            (padeRemainderMap
              (branchSquarePolynomial β) a) ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ := by
  let f : ℚ[X] := N13Mumford.f ℚ
  let B : ℚ[X] := branchSquarePolynomial β
  let l : ℚ[X] := padeRemainderMap B a
  have hcong :
      f ∣ D.toSemi.u -
        Polynomial.C (q : ℚ) * B ^ 2 := by
    exact branchSquarePolynomial_congruence D β q hfst
  have hu :
      AdjoinRoot.mk f D.toSemi.u =
        AdjoinRoot.mk f
          (Polynomial.C (q : ℚ) * B ^ 2) :=
    (AdjoinRoot.mk_eq_mk).2 hcong
  have hl :
      AdjoinRoot.mk f l =
        AdjoinRoot.mk f ((a : ℚ[X]) * B) := by
    apply (AdjoinRoot.mk_eq_mk).2
    exact Polynomial.dvd_modByMonic_sub
      ((a : ℚ[X]) * B) f
  have hdiv :
      f ∣
        Polynomial.C (q : ℚ) * l ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u := by
    apply AdjoinRoot.mk_eq_zero.mp
    simp only [map_sub, map_mul, map_pow,
      AdjoinRoot.mk_C]
    rw [hl, hu]
    simp only [map_mul, map_pow, AdjoinRoot.mk_C]
    ring
  have haDegree :
      (a : ℚ[X]).natDegree ≤ 2 :=
    padeNumerator_natDegree_le_two a ha0
  have hlDegree :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three B a haKer
  have huDegree :
      D.toSemi.u.natDegree ≤ 2 :=
    D.degree_le_two
  have hleftDegree :
      (Polynomial.C (q : ℚ) * l ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u).natDegree ≤ 6 := by
    have hq :
        (Polynomial.C (q : ℚ)).natDegree ≤ 0 :=
      by rw [Polynomial.natDegree_C]
    have hl2 :
        (l ^ 2).natDegree ≤ 6 := by
      rw [Polynomial.natDegree_pow]
      omega
    have ha2 :
        ((a : ℚ[X]) ^ 2).natDegree ≤ 4 := by
      rw [Polynomial.natDegree_pow]
      omega
    have hfirst :
        (Polynomial.C (q : ℚ) * l ^ 2).natDegree ≤ 6 :=
      (Polynomial.natDegree_mul_le).trans
        (by omega)
    have hsecond :
        ((a : ℚ[X]) ^ 2 *
          D.toSemi.u).natDegree ≤ 6 :=
      (Polynomial.natDegree_mul_le).trans
        (by omega)
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hfirst hsecond)
  obtain ⟨t, ht⟩ := hdiv
  have htDegree : t.natDegree ≤ 0 := by
    by_cases ht0 : t = 0
    · simp [ht0]
    have hf0 : f ≠ 0 := by
      exact (N13Mumford.f_monic (K := ℚ)).ne_zero
    have hdegree :
        6 + t.natDegree =
          (Polynomial.C (q : ℚ) * l ^ 2 -
            (a : ℚ[X]) ^ 2 * D.toSemi.u).natDegree := by
      rw [ht, Polynomial.natDegree_mul hf0 ht0]
      simp only [f, N13Mumford.f_natDegree]
    omega
  let c : ℚ := t.coeff 0
  have htC : t = Polynomial.C c :=
    Polynomial.eq_C_of_natDegree_le_zero htDegree
  refine ⟨c, ?_⟩
  change
    Polynomial.C (q : ℚ) * l ^ 2 -
        (a : ℚ[X]) ^ 2 * D.toSemi.u =
      Polynomial.C c * f
  rw [ht, htC]
  ring

/-! ## The Cantor square behind a Padé half -/

universe u

variable {K : Type u} [Field K]

/-- Multiplicativity of the homogeneous resultant with independent upper
bounds on the two right-hand factors.  Mathlib's primitive theorem uses
their actual degrees; padding contributes the same leading-coefficient
power on both sides. -/
theorem resultant_mul_right_padded
    (f g h : K[X]) (m n k : ℕ)
    (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n)
    (hh : h.natDegree ≤ k) :
    f.resultant (g * h) m (n + k) =
      f.resultant g m n * f.resultant h m k := by
  have hsum :
      n + k =
        (g.natDegree + h.natDegree) +
          ((n - g.natDegree) +
            (k - h.natDegree)) := by
    omega
  have hmuldeg :
      (g * h).natDegree ≤
        g.natDegree + h.natDegree :=
    Polynomial.natDegree_mul_le
  have hpadg :
      f.resultant g m n =
        f.coeff m ^ (n - g.natDegree) *
          f.resultant g m g.natDegree := by
    conv_lhs =>
      rw [show n =
        g.natDegree + (n - g.natDegree) by omega]
    exact Polynomial.resultant_add_right_deg
      f g m g.natDegree
        (n - g.natDegree) le_rfl
  have hpadh :
      f.resultant h m k =
        f.coeff m ^ (k - h.natDegree) *
          f.resultant h m h.natDegree := by
    conv_lhs =>
      rw [show k =
        h.natDegree + (k - h.natDegree) by omega]
    exact Polynomial.resultant_add_right_deg
      f h m h.natDegree
        (k - h.natDegree) le_rfl
  calc
    f.resultant (g * h) m (n + k) =
        f.resultant (g * h) m
          ((g.natDegree + h.natDegree) +
            ((n - g.natDegree) +
              (k - h.natDegree))) := by
                rw [hsum]
    _ =
        f.coeff m ^
            ((n - g.natDegree) +
              (k - h.natDegree)) *
          f.resultant (g * h) m
            (g.natDegree + h.natDegree) := by
              exact Polynomial.resultant_add_right_deg
                f (g * h) m
                  (g.natDegree + h.natDegree)
                  ((n - g.natDegree) +
                    (k - h.natDegree)) hmuldeg
    _ =
        f.coeff m ^
            ((n - g.natDegree) +
              (k - h.natDegree)) *
          (f.resultant g m *
            f.resultant h m) := by
              rw [Polynomial.resultant_mul_right
                f g h m hf]
    _ =
        (f.coeff m ^ (n - g.natDegree) *
            f.resultant g m g.natDegree) *
          (f.coeff m ^ (k - h.natDegree) *
            f.resultant h m h.natDegree) := by
              rw [pow_add]
              ring
    _ =
        f.resultant g m n *
          f.resultant h m k := by
            rw [hpadg, hpadh]

/-- The two fixed-degree homogeneous resultant identities attached to the
Padé equation.  Formal degrees `(2,3,6)` make the statement uniform when
the actual numerator or remainder degree drops; no case split on leading
coefficients is needed. -/
theorem pade_resultant_identities
    (D : LowRep) (a l : ℚ[X]) (q c : ℚ)
    (ha : a.natDegree ≤ 2)
    (hl : l.natDegree ≤ 3)
    (hrelation :
      Polynomial.C q * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ) :
    q ^ 2 * (a.resultant l 2 3) ^ 2 =
        c ^ 2 *
          (N13Mumford.f ℚ).resultant a 6 2 ∧
      -((a.resultant l 2 3) ^ 2) *
          D.toSemi.u.resultant l 2 3 =
        c ^ 3 *
          (N13Mumford.f ℚ).resultant l 6 3 := by
  have hu : D.toSemi.u.natDegree ≤ 2 :=
    D.degree_le_two
  have ha2 : (a ^ 2).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_pow]
    omega
  have hfirstCorrection :
      (-(a * D.toSemi.u)).natDegree + 2 ≤ 6 := by
    rw [Polynomial.natDegree_neg]
    exact Nat.add_le_add_right
      (Polynomial.natDegree_mul_le.trans (by omega)) 2
  have hsecondCorrection :
      (Polynomial.C q * l).natDegree + 3 ≤ 6 := by
    have hq :
        (Polynomial.C q).natDegree = 0 :=
      Polynomial.natDegree_C q
    exact Nat.add_le_add_right
      (Polynomial.natDegree_mul_le.trans (by omega)) 3
  have hresA :=
    congrArg
      (fun p : ℚ[X] => a.resultant p 2 6)
      hrelation
  have hleftA :
      a.resultant
          (Polynomial.C q * l ^ 2 -
            a ^ 2 * D.toSemi.u) 2 6 =
        q ^ 2 * (a.resultant l 2 3) ^ 2 := by
    have hll :
        a.resultant (l * l) 2 6 =
          a.resultant l 2 3 *
            a.resultant l 2 3 := by
      simpa only [Nat.reduceAdd] using
        (resultant_mul_right_padded
          a l l 2 3 3 ha hl hl)
    calc
      a.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 2 6 =
          a.resultant
            (Polynomial.C q * l ^ 2 +
              a * (-(a * D.toSemi.u))) 2 6 := by
                congr 2
                ring
      _ =
          a.resultant
            (Polynomial.C q * l ^ 2) 2 6 := by
              exact Polynomial.resultant_add_mul_right
                a (Polynomial.C q * l ^ 2)
                  (-(a * D.toSemi.u)) 2 6
                  hfirstCorrection ha
      _ =
          q ^ 2 * a.resultant (l ^ 2) 2 6 := by
              exact Polynomial.resultant_C_mul_right
                a (l ^ 2) 2 6 q
      _ =
          q ^ 2 *
            (a.resultant l 2 3 *
              a.resultant l 2 3) := by
                rw [show l ^ 2 = l * l by ring, hll]
      _ =
          q ^ 2 * (a.resultant l 2 3) ^ 2 := by
            ring
  have hrightA :
      a.resultant
          (Polynomial.C c * N13Mumford.f ℚ) 2 6 =
        c ^ 2 *
          (N13Mumford.f ℚ).resultant a 6 2 := by
    rw [Polynomial.resultant_C_mul_right,
      Polynomial.resultant_comm]
    norm_num
  have hresL :=
    congrArg
      (fun p : ℚ[X] => l.resultant p 3 6)
      hrelation
  have hleftL :
      l.resultant
          (Polynomial.C q * l ^ 2 -
            a ^ 2 * D.toSemi.u) 3 6 =
        -((a.resultant l 2 3) ^ 2) *
          D.toSemi.u.resultant l 2 3 := by
    have haa :
        l.resultant (a * a) 3 4 =
          l.resultant a 3 2 *
            l.resultant a 3 2 := by
      simpa only [Nat.reduceAdd] using
        (resultant_mul_right_padded
          l a a 3 2 2 hl ha ha)
    have hla :
        l.resultant a 3 2 =
          a.resultant l 2 3 := by
      rw [Polynomial.resultant_comm]
      norm_num
    have hlu :
        l.resultant D.toSemi.u 3 2 =
          D.toSemi.u.resultant l 2 3 := by
      rw [Polynomial.resultant_comm]
      norm_num
    calc
      l.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 3 6 =
          l.resultant
            (-(a ^ 2 * D.toSemi.u) +
              l * (Polynomial.C q * l)) 3 6 := by
                congr 2
                ring
      _ =
          l.resultant
            (-(a ^ 2 * D.toSemi.u)) 3 6 := by
              exact Polynomial.resultant_add_mul_right
                l (-(a ^ 2 * D.toSemi.u))
                  (Polynomial.C q * l) 3 6
                  hsecondCorrection hl
      _ =
          (-1 : ℚ) ^ 3 *
            l.resultant
              (a ^ 2 * D.toSemi.u) 3 6 := by
                rw [show -(a ^ 2 * D.toSemi.u) =
                  Polynomial.C (-1 : ℚ) *
                    (a ^ 2 * D.toSemi.u) by simp]
                exact Polynomial.resultant_C_mul_right
                  l (a ^ 2 * D.toSemi.u) 3 6 (-1)
      _ =
          (-1 : ℚ) ^ 3 *
            (l.resultant (a ^ 2) 3 4 *
              l.resultant D.toSemi.u 3 2) := by
                rw [resultant_mul_right_padded
                  l (a ^ 2) D.toSemi.u
                    3 4 2 hl ha2 hu]
      _ =
          (-1 : ℚ) ^ 3 *
            ((l.resultant a 3 2 *
                l.resultant a 3 2) *
              l.resultant D.toSemi.u 3 2) := by
                rw [show a ^ 2 = a * a by ring, haa]
      _ =
          -((a.resultant l 2 3) ^ 2) *
            D.toSemi.u.resultant l 2 3 := by
              rw [hla, hlu]
              ring
  have hrightL :
      l.resultant
          (Polynomial.C c * N13Mumford.f ℚ) 3 6 =
        c ^ 3 *
          (N13Mumford.f ℚ).resultant l 6 3 := by
    rw [Polynomial.resultant_C_mul_right,
      Polynomial.resultant_comm]
    norm_num
  constructor
  · calc
      q ^ 2 * (a.resultant l 2 3) ^ 2 =
          a.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 2 6 :=
        hleftA.symm
      _ =
          a.resultant
            (Polynomial.C c * N13Mumford.f ℚ) 2 6 :=
        hresA
      _ = _ := hrightA
  · calc
      -((a.resultant l 2 3) ^ 2) *
            D.toSemi.u.resultant l 2 3 =
          l.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 3 6 :=
        hleftL.symm
      _ =
          l.resultant
            (Polynomial.C c * N13Mumford.f ℚ) 3 6 :=
        hresL
      _ = _ := hrightL

/-! ## From the sextic norm to the quadratic norm -/

/-- The sextic norm--resultant formula with a fixed formal right degree.
The sextic is monic, so padding a lower-degree polynomial contributes only
a power of its leading coefficient `1`. -/
theorem sextic_norm_mk_eq_resultant_padded
    (p : ℚ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    Algebra.norm ℚ
        (AdjoinRoot.mk N13SexticSquareclass.f p) =
      (N13Mumford.f ℚ).resultant p 6 n := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :
      Algebra.norm ℚ
          (AdjoinRoot.mk N13SexticSquareclass.f p) =
        (N13Mumford.f ℚ).resultant p := by
    rw [← AdjoinRoot.aeval_eq]
    exact
      PowerBasisDiscriminant.norm_aeval_adjoinRoot_eq_resultant
        (N13Mumford.f_monic (K := ℚ))
        N13SexticIrreducible.n13Mumford_f_irreducible
        p
  have hfcoeff :
      (N13Mumford.f ℚ).coeff 6 = 1 := by
    simpa only [N13Mumford.f_natDegree] using
      (N13Mumford.f_monic (K := ℚ)).coeff_natDegree
  have hpad :=
    Polynomial.resultant_add_right_deg
      (N13Mumford.f ℚ) p 6 p.natDegree
        (n - p.natDegree) le_rfl
  have hadd :
      p.natDegree + (n - p.natDegree) = n :=
    Nat.add_sub_of_le hp
  rw [hadd, hfcoeff, one_pow, one_mul] at hpad
  calc
    Algebra.norm ℚ
          (AdjoinRoot.mk N13SexticSquareclass.f p) =
        (N13Mumford.f ℚ).resultant p :=
      hnorm
    _ =
        (N13Mumford.f ℚ).resultant
          p 6 p.natDegree := by
            change
              (N13Mumford.f ℚ).resultant
                  p (N13Mumford.f ℚ).natDegree
                    p.natDegree =
                (N13Mumford.f ℚ).resultant
                  p 6 p.natDegree
            rw [N13Mumford.f_natDegree]
    _ = (N13Mumford.f ℚ).resultant p 6 n :=
      hpad.symm

/-- A nonzero polynomial of degree below six is coprime to the irreducible
N13 sextic.  Hence every monic-padded version of its resultant is nonzero. -/
theorem sextic_resultant_padded_ne_zero
    (p : ℚ[X]) (n : ℕ)
    (hp : p.natDegree ≤ n)
    (hp0 : p ≠ 0)
    (hp6 : p.natDegree < 6) :
    (N13Mumford.f ℚ).resultant p 6 n ≠ 0 := by
  have hcop :
      IsCoprime (N13Mumford.f ℚ) p := by
    rcases
        dvd_or_isCoprime
          (N13Mumford.f ℚ) p
          N13SexticIrreducible.n13Mumford_f_irreducible with
      hdiv | hcop
    · have hdegree :=
        Polynomial.natDegree_le_of_dvd hdiv hp0
      rw [N13Mumford.f_natDegree] at hdegree
      omega
    · exact hcop
  have hdefault :
      (N13Mumford.f ℚ).resultant p ≠ 0 :=
    Polynomial.resultant_ne_zero
      (N13Mumford.f ℚ) p hcop
  have hfcoeff :
      (N13Mumford.f ℚ).coeff 6 = 1 := by
    simpa only [N13Mumford.f_natDegree] using
      (N13Mumford.f_monic (K := ℚ)).coeff_natDegree
  have hpad :=
    Polynomial.resultant_add_right_deg
      (N13Mumford.f ℚ) p 6 p.natDegree
        (n - p.natDegree) le_rfl
  have hadd :
      p.natDegree + (n - p.natDegree) = n :=
    Nat.add_sub_of_le hp
  rw [hadd, hfcoeff, one_pow, one_mul] at hpad
  intro hzero
  apply hdefault
  change
    (N13Mumford.f ℚ).resultant p
      (N13Mumford.f ℚ).natDegree p.natDegree = 0
  rw [N13Mumford.f_natDegree]
  rw [← hpad, hzero]

/-- Reduction modulo the sextic does not alter the Padé product:
the chosen cubic remainder still represents `a(θ)β`. -/
theorem mk_padeRemainderMap
    (β : Lˣ) (a : Polynomial.degreeLT ℚ 3) :
    AdjoinRoot.mk N13SexticSquareclass.f
        (padeRemainderMap
          (branchSquarePolynomial β) a) =
      AdjoinRoot.mk N13SexticSquareclass.f
          (a : ℚ[X]) * (β : L) := by
  have hleft :
      AdjoinRoot.mk N13SexticSquareclass.f
          (((a : ℚ[X]) * branchSquarePolynomial β) %ₘ
            N13SexticSquareclass.f) =
        AdjoinRoot.mk N13SexticSquareclass.f
          ((a : ℚ[X]) * branchSquarePolynomial β) := by
    simpa only [AdjoinRoot.modByMonicHom_mk] using
      (AdjoinRoot.mk_leftInverse sextic_f_monic
        (AdjoinRoot.mk N13SexticSquareclass.f
          ((a : ℚ[X]) * branchSquarePolynomial β)))
  calc
    AdjoinRoot.mk N13SexticSquareclass.f
          (padeRemainderMap
            (branchSquarePolynomial β) a) =
        AdjoinRoot.mk N13SexticSquareclass.f
          (((a : ℚ[X]) * branchSquarePolynomial β) %ₘ
            N13SexticSquareclass.f) := by
              rfl
    _ =
        AdjoinRoot.mk N13SexticSquareclass.f
          ((a : ℚ[X]) * branchSquarePolynomial β) :=
      hleft
    _ =
        AdjoinRoot.mk N13SexticSquareclass.f
            (a : ℚ[X]) * (β : L) := by
          rw [map_mul, mk_branchSquarePolynomial]

/-- Multiplicativity of the sextic norm converts the Padé remainder into
the product of the numerator resultant and the norm of the branch square
root. -/
theorem pade_sextic_resultant_factorization
    (β : Lˣ) (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0) :
    (N13Mumford.f ℚ).resultant
          (padeRemainderMap
            (branchSquarePolynomial β) a) 6 3 =
      (N13Mumford.f ℚ).resultant
          (a : ℚ[X]) 6 2 *
        (N13FullNormPair.normUnits β : ℚ) := by
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have ha :
      (a : ℚ[X]).natDegree ≤ 2 :=
    padeNumerator_natDegree_le_two a ha0
  have hl :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three
      (branchSquarePolynomial β) a haKer
  have hnormA :=
    sextic_norm_mk_eq_resultant_padded
      (a : ℚ[X]) 2 ha
  have hnormL :=
    sextic_norm_mk_eq_resultant_padded l 3 hl
  calc
    (N13Mumford.f ℚ).resultant l 6 3 =
        Algebra.norm ℚ
          (AdjoinRoot.mk
            N13SexticSquareclass.f l) :=
      hnormL.symm
    _ =
        Algebra.norm ℚ
          (AdjoinRoot.mk N13SexticSquareclass.f
              (a : ℚ[X]) * (β : L)) := by
            rw [mk_padeRemainderMap β a]
    _ =
        Algebra.norm ℚ
            (AdjoinRoot.mk N13SexticSquareclass.f
              (a : ℚ[X])) *
          Algebra.norm ℚ (β : L) := by
            rw [map_mul]
    _ =
        (N13Mumford.f ℚ).resultant
              (a : ℚ[X]) 6 2 *
          (N13FullNormPair.normUnits β : ℚ) := by
            change
              Algebra.norm ℚ
                    (AdjoinRoot.mk N13SexticSquareclass.f
                      (a : ℚ[X])) *
                  Algebra.norm ℚ (β : L) =
                (N13Mumford.f ℚ).resultant
                    (a : ℚ[X]) 6 2 *
                  Algebra.norm ℚ (β : L)
            rw [hnormA]

/-- On the nondegenerate Padé branch, the two homogeneous resultant
identities and the oriented norm equation force the quadratic norm ratio
`Res(u,l) / Res(u,v)` to equal `c/q`.  All cancellations occur only after
the sextic norm proves the Padé cross-resultant nonzero. -/
theorem pade_quadratic_resultant_relation
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0)
    (c : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) *
            (padeRemainderMap
              (branchSquarePolynomial β) a) ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3)
    (hc : c ≠ 0) :
    (q : ℚ) *
          D.toSemi.u.resultant
            (padeRemainderMap
              (branchSquarePolynomial β) a) 2 3 =
      c * N13MumfordKummerNorm.normRoot D := by
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have ha :
      (a : ℚ[X]).natDegree ≤ 2 :=
    padeNumerator_natDegree_le_two a ha0
  have hl :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three
      (branchSquarePolynomial β) a haKer
  obtain ⟨hfirst, hsecond⟩ :=
    pade_resultant_identities
      D (a : ℚ[X]) l (q : ℚ) c
        ha hl hrelation
  have hfactor :=
    pade_sextic_resultant_factorization
      β a ha0 haKer
  have haPoly : (a : ℚ[X]) ≠ 0 := by
    exact fun h => ha0 (Subtype.ext h)
  have hresA :
      (N13Mumford.f ℚ).resultant
          (a : ℚ[X]) 6 2 ≠ 0 :=
    sextic_resultant_padded_ne_zero
      (a : ℚ[X]) 2 ha haPoly (by omega)
  have hcross :
      (a : ℚ[X]).resultant l 2 3 ≠ 0 := by
    intro hzero
    have hbad :
        c ^ 2 *
            (N13Mumford.f ℚ).resultant
              (a : ℚ[X]) 6 2 = 0 := by
      rw [← hfirst, hzero]
      ring
    exact
      (mul_ne_zero (pow_ne_zero 2 hc) hresA) hbad
  rw [hfactor] at hsecond
  have hcancel :
      ((a : ℚ[X]).resultant l 2 3) ^ 2 *
          (-D.toSemi.u.resultant l 2 3 -
            c * (q : ℚ) ^ 2 *
              (N13FullNormPair.normUnits β : ℚ)) = 0 := by
    linear_combination
      hsecond -
        c * (N13FullNormPair.normUnits β : ℚ) *
          hfirst
  have hscalar :
      -D.toSemi.u.resultant l 2 3 -
          c * (q : ℚ) ^ 2 *
            (N13FullNormPair.normUnits β : ℚ) = 0 :=
    (mul_eq_zero.mp hcancel).resolve_left
      (pow_ne_zero 2 hcross)
  have hS :
      D.toSemi.u.resultant l 2 3 =
        -c * (q : ℚ) ^ 2 *
          (N13FullNormPair.normUnits β : ℚ) := by
    linear_combination -hscalar
  have hsndVal :=
    congrArg (fun z : ℚˣ => (z : ℚ)) hsnd
  change
    (-1 : ℚ) * N13MumfordKummerNorm.normRoot D =
      (N13FullNormPair.normUnits β : ℚ) *
        (q : ℚ) ^ 3 at hsndVal
  have hroot :
      N13MumfordKummerNorm.normRoot D =
        -(N13FullNormPair.normUnits β : ℚ) *
          (q : ℚ) ^ 3 := by
    linear_combination -hsndVal
  change
    (q : ℚ) * D.toSemi.u.resultant l 2 3 =
      c * N13MumfordKummerNorm.normRoot D
  rw [hS, hroot]
  ring

/-- The Padé equation in the quotient by `u`, divided by the unit
represented by `v`, always gives `(l/v)² = c/q`.  This uses only the curve
congruence `f ≡ v² (mod u)` and is independent of the degree or
factorization type of `u`. -/
theorem adjoinRoot_pade_quotient_sq
    (D : LowRep) (a l : ℚ[X]) (q : ℚˣ) (c : ℚ)
    (V : (AdjoinRoot D.toSemi.u)ˣ)
    (hV :
      (V : AdjoinRoot D.toSemi.u) =
        AdjoinRoot.mk D.toSemi.u D.toSemi.v)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ) :
    (AdjoinRoot.mk D.toSemi.u l *
          ((V⁻¹ : (AdjoinRoot D.toSemi.u)ˣ) :
            AdjoinRoot D.toSemi.u)) ^ 2 =
      algebraMap ℚ (AdjoinRoot D.toSemi.u)
        (c / (q : ℚ)) := by
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  let E : Type := AdjoinRoot u
  have hq : (q : ℚ) ≠ 0 :=
    Units.ne_zero q
  have hcurveMk :
      AdjoinRoot.mk u (N13Mumford.f ℚ) =
        AdjoinRoot.mk u (v ^ 2) := by
    apply (AdjoinRoot.mk_eq_mk).2
    exact D.toSemi.curve_dvd
  have hmapped :=
    congrArg (AdjoinRoot.mk u) hrelation
  have hbase :
      algebraMap ℚ E (q : ℚ) *
            (AdjoinRoot.mk u l) ^ 2 =
        algebraMap ℚ E c * (V : E) ^ 2 := by
    dsimp only [u] at hmapped
    simp only [map_sub, map_mul, map_pow,
      AdjoinRoot.mk_C, AdjoinRoot.mk_self,
      mul_zero, sub_zero] at hmapped
    rw [hcurveMk, map_pow, ← hV] at hmapped
    simpa only [E, u,
      AdjoinRoot.algebraMap_eq] using hmapped
  have hqCancel :
      algebraMap ℚ E ((q : ℚ)⁻¹) *
          algebraMap ℚ E (q : ℚ) = 1 := by
    rw [← map_mul]
    simp [hq]
  have hVCancel :
      (V : E) *
          ((V⁻¹ : (AdjoinRoot u)ˣ) : E) = 1 := by
    rw [← Units.val_mul]
    simp
  change
    (AdjoinRoot.mk u l *
          ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 =
      algebraMap ℚ E (c / (q : ℚ))
  calc
    (AdjoinRoot.mk u l *
          ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 =
        1 *
          (AdjoinRoot.mk u l *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 := by
              rw [one_mul]
    _ =
        (algebraMap ℚ E ((q : ℚ)⁻¹) *
            algebraMap ℚ E (q : ℚ)) *
          (AdjoinRoot.mk u l *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 := by
              rw [hqCancel]
    _ =
        algebraMap ℚ E ((q : ℚ)⁻¹) *
          (algebraMap ℚ E (q : ℚ) *
            (AdjoinRoot.mk u l) ^ 2) *
          (((V⁻¹ : (AdjoinRoot u)ˣ) : E) ^ 2) := by
              ring
    _ =
        algebraMap ℚ E ((q : ℚ)⁻¹) *
          (algebraMap ℚ E c * (V : E) ^ 2) *
          (((V⁻¹ : (AdjoinRoot u)ˣ) : E) ^ 2) := by
              rw [hbase]
    _ =
        (algebraMap ℚ E ((q : ℚ)⁻¹) *
            algebraMap ℚ E c) *
          ((V : E) *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 := by
              ring
    _ =
        algebraMap ℚ E ((q : ℚ)⁻¹) *
          algebraMap ℚ E c := by
            rw [hVCancel]
            ring
    _ =
        algebraMap ℚ E
          (((q : ℚ)⁻¹) * c) := by
            rw [map_mul]
    _ =
        algebraMap ℚ E (c / (q : ℚ)) := by
          congr 1
          rw [div_eq_mul_inv]
          ring

/-- If the scalar `c` is nonzero and `u` has its generic quadratic degree,
the Padé quotient `l/v` is rigid.  Its square and its algebra norm both
equal `c/q`, so Cayley--Hamilton forces it to be a rational scalar `b`.
Equivalently, `l ≡ b v (mod u)`. -/
theorem exists_pade_graph_scalar_of_c_ne_zero
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0)
    (c : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) *
            (padeRemainderMap
              (branchSquarePolynomial β) a) ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3)
    (hu2 : D.toSemi.u.natDegree = 2)
    (hc : c ≠ 0) :
    ∃ b : ℚ,
      b ≠ 0 ∧
      b ^ 2 = c / (q : ℚ) ∧
      D.toSemi.u ∣
        padeRemainderMap
              (branchSquarePolynomial β) a -
          Polynomial.C b * D.toSemi.v := by
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have hu : u.Monic := D.toSemi.u_monic
  have hu2' : u.natDegree = 2 := hu2
  have hl :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three
      (branchSquarePolynomial β) a haKer
  have huOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu2'
    omega
  have hvlt : v.natDegree < u.natDegree := by
    have hmod :=
      Polynomial.natDegree_modByMonic_lt v hu huOne
    rw [Polynomial.modByMonic_eq_mod v hu,
      D.toSemi.v_reduced] at hmod
    exact hmod
  have hv : v.natDegree ≤ 1 := by
    omega
  have hres :
      Polynomial.resultant u v ≠ 0 := by
    exact N13MumfordKummerNorm.normRoot_ne_zero D
  let E : Type := AdjoinRoot u
  letI : Nontrivial E := by
    apply AdjoinRoot.nontrivial
    rw [Polynomial.degree_eq_natDegree hu.ne_zero,
      hu2']
    norm_num
  let basis :
      Module.Basis (Fin 2) ℚ E :=
    (AdjoinRoot.powerBasisAux' hu).reindex
      (finCongr hu2')
  letI : Module.Free ℚ E :=
    Module.Free.of_basis basis
  letI : Module.Finite ℚ E :=
    Module.Finite.of_basis basis
  obtain ⟨V, hV, hnorm⟩ :=
    QuadraticAdjoinRootNorm.exists_mk_unit_norm_mul_inv
      u l v hu hu2' hl hv hres
  let t : E :=
    AdjoinRoot.mk u l *
      ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u)
  have hq : (q : ℚ) ≠ 0 :=
    Units.ne_zero q
  have hresultant :=
    pade_quadratic_resultant_relation
      D β q a ha0 haKer c hrelation hsnd hc
  have hratio :
      Polynomial.resultant u l 2 3 /
            Polynomial.resultant u v =
        c / (q : ℚ) := by
    apply (div_eq_div_iff hres hq).2
    simpa only [u, v, l,
      N13MumfordKummerNorm.normRoot,
      mul_comm] using hresultant
  have hnorm' :
      Algebra.norm ℚ t = c / (q : ℚ) := by
    exact hnorm.trans hratio
  have hsq :
      t ^ 2 =
        algebraMap ℚ E (c / (q : ℚ)) := by
    exact
      adjoinRoot_pade_quotient_sq
        D (a : ℚ[X]) l q c V hV hrelation
  have hs : c / (q : ℚ) ≠ 0 :=
    div_ne_zero hc hq
  obtain ⟨b, ht, hbSq⟩ :=
    QuadraticNormRigidity.exists_scalar_square_root
      basis t (c / (q : ℚ)) hs hsq hnorm'
  have hb : b ≠ 0 := by
    intro hb
    apply hs
    rw [← hbSq, hb]
    norm_num
  have hlEq :
      AdjoinRoot.mk u l =
        AdjoinRoot.mk u
          (Polynomial.C b * v) := by
    calc
      AdjoinRoot.mk u l =
          t * (V : E) := by
            dsimp only [t]
            calc
              AdjoinRoot.mk u l =
                  AdjoinRoot.mk u l * 1 := by
                    rw [mul_one]
              _ =
                  AdjoinRoot.mk u l *
                    (((V⁻¹ : (AdjoinRoot u)ˣ) : E) *
                      (V : E)) := by
                        rw [← Units.val_mul]
                        simp
              _ =
                  (AdjoinRoot.mk u l *
                    ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) *
                      (V : E) := by
                        ring
      _ =
          algebraMap ℚ E b * (V : E) := by
            rw [ht]
      _ =
          AdjoinRoot.mk u
            (Polynomial.C b * v) := by
              rw [map_mul, AdjoinRoot.mk_C, hV,
                AdjoinRoot.algebraMap_eq]
  refine ⟨b, hb, hbSq, ?_⟩
  exact (AdjoinRoot.mk_eq_mk).mp hlEq

/-- When `u` has degree one, the same graph scalar follows from the fact
that a monic linear quotient is the ground field itself.  No norm
calculation is needed in this degeneration. -/
theorem exists_pade_graph_scalar_of_c_ne_zero_degree_one
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X]) (c : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hu1 : D.toSemi.u.natDegree = 1)
    (hc : c ≠ 0) :
    ∃ b : ℚ,
      b ≠ 0 ∧
      b ^ 2 = c / (q : ℚ) ∧
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v := by
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  have hu : u.Monic := D.toSemi.u_monic
  have hu1' : u.natDegree = 1 := hu1
  have hres :
      Polynomial.resultant u v ≠ 0 := by
    exact N13MumfordKummerNorm.normRoot_ne_zero D
  have hvUnit :
      IsUnit (AdjoinRoot.mk u v) :=
    QuadraticAdjoinRootNorm.isUnit_mk_of_resultant_ne_zero
      u v hu.ne_zero hres
  let V : (AdjoinRoot u)ˣ := hvUnit.unit
  have hV :
      (V : AdjoinRoot u) = AdjoinRoot.mk u v :=
    hvUnit.unit_spec
  let t : AdjoinRoot u :=
    AdjoinRoot.mk u l *
      ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u)
  have hsq :
      t ^ 2 =
        algebraMap ℚ (AdjoinRoot u)
          (c / (q : ℚ)) := by
    exact
      adjoinRoot_pade_quotient_sq
        D a l q c V hV hrelation
  obtain ⟨b, ht, hbSq⟩ :=
    LinearAdjoinRootScalar.exists_scalar_square_root
      u hu hu1' t (c / (q : ℚ)) hsq
  have hs : c / (q : ℚ) ≠ 0 :=
    div_ne_zero hc (Units.ne_zero q)
  have hb : b ≠ 0 := by
    intro hb
    apply hs
    rw [← hbSq, hb]
    norm_num
  have hlEq :
      AdjoinRoot.mk u l =
        AdjoinRoot.mk u
          (Polynomial.C b * v) := by
    calc
      AdjoinRoot.mk u l =
          t * (V : AdjoinRoot u) := by
            dsimp only [t]
            calc
              AdjoinRoot.mk u l =
                  AdjoinRoot.mk u l * 1 := by
                    rw [mul_one]
              _ =
                  AdjoinRoot.mk u l *
                    (((V⁻¹ : (AdjoinRoot u)ˣ) :
                        AdjoinRoot u) *
                      (V : AdjoinRoot u)) := by
                        rw [← Units.val_mul]
                        simp
              _ =
                  (AdjoinRoot.mk u l *
                    ((V⁻¹ : (AdjoinRoot u)ˣ) :
                      AdjoinRoot u)) *
                      (V : AdjoinRoot u) := by
                        ring
      _ =
          algebraMap ℚ (AdjoinRoot u) b *
            (V : AdjoinRoot u) := by
              rw [ht]
      _ =
          AdjoinRoot.mk u
            (Polynomial.C b * v) := by
              rw [map_mul, AdjoinRoot.mk_C, hV,
                AdjoinRoot.algebraMap_eq]
  refine ⟨b, hb, hbSq, ?_⟩
  exact (AdjoinRoot.mk_eq_mk).mp hlEq

/-- A rational graph scalar rescales the Padé cubic into the actual graph
polynomial used by Cantor's identity.  The same construction works for
both the linear and quadratic quotient branches. -/
theorem exists_scaled_pade_graph
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X])
    (c b : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hb : b ≠ 0)
    (hbSq : b ^ 2 = c / (q : ℚ))
    (hgraph :
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v)
    (hc : c ≠ 0) :
    ∃ L₀ : ℚ[X], ∃ κ : ℚˣ,
      N13Mumford.f ℚ - L₀ ^ 2 =
          a ^ 2 *
            (Polynomial.C (κ : ℚ) * D.toSemi.u) ∧
      D.toSemi.u ∣ L₀ - D.toSemi.v := by
  let L₀ : ℚ[X] :=
    Polynomial.C (b⁻¹) * l
  let κ : ℚˣ :=
    Units.mk0 (-c⁻¹)
      (neg_ne_zero.mpr (inv_ne_zero hc))
  have hscale :
      (b⁻¹) ^ 2 = (q : ℚ) / c := by
    rw [inv_pow, hbSq]
    field_simp [hc, Units.ne_zero q]
  have hcScale :
      c * (b⁻¹) ^ 2 = (q : ℚ) := by
    rw [hscale]
    field_simp [hc]
  have hCb :
      Polynomial.C (b⁻¹) * Polynomial.C b = 1 := by
    rw [← Polynomial.C_mul]
    simp [hb]
  have hgraphScaled :
      D.toSemi.u ∣ L₀ - D.toSemi.v := by
    obtain ⟨t, ht⟩ := hgraph
    refine
      ⟨Polynomial.C (b⁻¹) * t, ?_⟩
    calc
      L₀ - D.toSemi.v =
          Polynomial.C (b⁻¹) *
            (l - Polynomial.C b * D.toSemi.v) := by
              dsimp only [L₀]
              rw [mul_sub]
              rw [← mul_assoc, hCb, one_mul]
      _ =
          Polynomial.C (b⁻¹) *
            (D.toSemi.u * t) := by
              rw [ht]
      _ =
          D.toSemi.u *
            (Polynomial.C (b⁻¹) * t) := by
              ring
  have hscaledSquare :
      Polynomial.C c * L₀ ^ 2 =
        Polynomial.C (q : ℚ) * l ^ 2 := by
    calc
      Polynomial.C c * L₀ ^ 2 =
          (Polynomial.C c *
              Polynomial.C ((b⁻¹) ^ 2)) *
            l ^ 2 := by
              dsimp only [L₀]
              rw [mul_pow, ← Polynomial.C_pow]
              ring
      _ =
          Polynomial.C (q : ℚ) * l ^ 2 := by
            rw [← Polynomial.C_mul, hcScale]
  have hscaledFactor :
      Polynomial.C c *
          (a ^ 2 *
            (Polynomial.C (κ : ℚ) *
              D.toSemi.u)) =
        -(a ^ 2 * D.toSemi.u) := by
    have hcInv :
        c * (-c⁻¹) = (-1 : ℚ) := by
      field_simp [hc]
    calc
      Polynomial.C c *
            (a ^ 2 *
              (Polynomial.C (κ : ℚ) *
                D.toSemi.u)) =
          (Polynomial.C c *
              Polynomial.C (-c⁻¹)) *
            (a ^ 2 * D.toSemi.u) := by
              change
                Polynomial.C c *
                    (a ^ 2 *
                      (Polynomial.C (-c⁻¹) *
                        D.toSemi.u)) =
                  (Polynomial.C c *
                      Polynomial.C (-c⁻¹)) *
                    (a ^ 2 * D.toSemi.u)
              ring
      _ =
          Polynomial.C (-1 : ℚ) *
            (a ^ 2 * D.toSemi.u) := by
              rw [← Polynomial.C_mul, hcInv]
      _ = -(a ^ 2 * D.toSemi.u) := by
        simp
  refine ⟨L₀, κ, ?_, hgraphScaled⟩
  apply mul_left_cancel₀
    (Polynomial.C_ne_zero.mpr hc)
  rw [mul_sub, hscaledSquare, hscaledFactor]
  linear_combination -hrelation

/-- If `f - L² = a w`, the complementary graph ideal is contained in
`(a,Y-L)` whenever `a ∣ w`.  Cantor's product formula then supplies the
missing generator `Y-L` of the square.  Thus no factorization of `a` is
needed. -/
theorem curveFactor_bezout
    (C : SexticMumford.Model K) (u₀ w L₀ : K[X])
    (hu₀ : u₀ ≠ 0)
    (hcurve : C.f - L₀ ^ 2 = u₀ * w) :
    ∃ A B E : K[X],
      A * u₀ + B * (2 * L₀) + E * w = 1 := by
  classical
  have hcop :
      IsCoprime u₀
        (EuclideanDomain.gcd (2 * L₀) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact hu₀ hzero.1
    · intro z hz hzu hzg
      have hz2L : z ∣ 2 * L₀ :=
        hzg.trans
          (EuclideanDomain.gcd_dvd_left (2 * L₀) w)
      have hzw : z ∣ w :=
        hzg.trans
          (EuclideanDomain.gcd_dvd_right (2 * L₀) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq :
            Polynomial.C (2 : K) = (2 : K[X]) := by
          exact map_natCast
            (Polynomial.C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr C.two_ne_zero)
      have hzL : z ∣ L₀ := by
        rcases hz.prime.dvd_mul.mp hz2L with hz2 | hzL
        · exact
            (hz.not_isUnit
              (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzL
      have hzzSub : z * z ∣ C.f - L₀ ^ 2 := by
        rw [hcurve]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ L₀ ^ 2 := by
        simpa only [pow_two] using
          mul_dvd_mul hzL hzL
      have hzzF : z * z ∣ C.f := by
        simpa only [sub_add_cancel] using
          dvd_add hzzSub hzzSq
      exact
        ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
          C.ne_zero).mp C.squarefree z hz) hzzF
  obtain ⟨A, T, hAT⟩ := hcop
  refine
    ⟨A,
      T * EuclideanDomain.gcdA (2 * L₀) w,
      T * EuclideanDomain.gcdB (2 * L₀) w, ?_⟩
  rw [← hAT, EuclideanDomain.gcd_eq_gcd_ab]
  ring

theorem mumfordIdeal_sq_eq_square_generator
    (C : SexticMumford.Model K) (a w L₀ : K[X])
    (hcurve : C.f - L₀ ^ 2 = a * w)
    (haw : a ∣ w)
    (hbezout :
      ∃ A B E : K[X],
        A * a + B * (2 * L₀) + E * w = 1) :
    mumfordIdeal C a L₀ ^ 2 =
      mumfordIdeal C (a ^ 2) L₀ := by
  rw [pow_two]
  apply le_antisymm
  · rw [mumfordIdeal, mumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [← xClass_mul, ← pow_two]
      exact xClass_mem_mumfordIdeal C (a ^ 2) L₀
    · exact Ideal.mul_mem_left _
        (xClass C a)
        (ySubClass_mem_mumfordIdeal C (a ^ 2) L₀)
    · rw [mul_comm]
      exact Ideal.mul_mem_left _
        (xClass C a)
        (ySubClass_mem_mumfordIdeal C (a ^ 2) L₀)
    · exact Ideal.mul_mem_left _
        (ySubClass C L₀)
        (ySubClass_mem_mumfordIdeal C (a ^ 2) L₀)
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have ha :
          xClass C a ∈ mumfordIdeal C a L₀ :=
        xClass_mem_mumfordIdeal C a L₀
      have haa :
          xClass C a * xClass C a ∈
            mumfordIdeal C a L₀ * mumfordIdeal C a L₀ :=
        Ideal.mul_mem_mul ha ha
      rw [xClass_pow, pow_two]
      exact haa
    · have hwa :
          mumfordIdeal C w L₀ ≤ mumfordIdeal C a L₀ := by
        apply Ideal.span_le.2
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · obtain ⟨t, rfl⟩ := haw
          rw [xClass_mul]
          exact Ideal.mul_mem_right
            (xClass C t)
            (mumfordIdeal C a L₀)
            (xClass_mem_mumfordIdeal C a L₀)
        · exact ySubClass_mem_mumfordIdeal C a L₀
      have hproduct :
          mumfordIdeal C a L₀ * mumfordIdeal C w L₀ ≤
            mumfordIdeal C a L₀ * mumfordIdeal C a L₀ := by
        apply Ideal.mul_le.mpr
        intro x hx y hy
        exact Ideal.mul_mem_mul hx (hwa hy)
      apply hproduct
      rw [mumfordIdeal_mul_cantor C a w L₀ hcurve hbezout]
      exact Ideal.subset_span (Set.mem_singleton _)

/-- A nonzero scalar on the polynomial generator does not change the graph
ideal. -/
theorem mumfordIdeal_C_mul
    (C : SexticMumford.Model K) (κ : Kˣ) (u₀ L₀ : K[X]) :
    mumfordIdeal C
        (Polynomial.C (κ : K) * u₀) L₀ =
      mumfordIdeal C u₀ L₀ := by
  apply mumfordIdeal_eq_of_dvd_dvd
  · refine ⟨Polynomial.C ((κ⁻¹ : Kˣ) : K), ?_⟩
    symm
    calc
      Polynomial.C (κ : K) * u₀ *
            Polynomial.C ((κ⁻¹ : Kˣ) : K) =
          (Polynomial.C (κ : K) *
              Polynomial.C ((κ⁻¹ : Kˣ) : K)) * u₀ := by
            ring
      _ = u₀ := by
        rw [← Polynomial.C_mul]
        simp [Units.ne_zero κ]
  · refine ⟨Polynomial.C (κ : K), ?_⟩
    ring

/-- The exact finite-ideal identity produced by a Padé half.  The two
Bézout hypotheses are the smooth Cantor transversality conditions for the
intermediate graph ideals.  The conclusion already identifies the target
Mumford ideal with a square up to the principal graph function `Y-L`. -/
theorem mumfordIdeal_pade_half
    (C : SexticMumford.Model K)
    (a u₀ v₀ L₀ : K[X]) (κ : Kˣ)
    (hcurve :
      C.f - L₀ ^ 2 =
        a ^ 2 * (Polynomial.C (κ : K) * u₀))
    (hgraph : u₀ ∣ L₀ - v₀)
    (ha : a ≠ 0) :
    mumfordIdeal C a L₀ ^ 2 *
        mumfordIdeal C u₀ v₀ =
      Ideal.span
        ({ySubClass C L₀} :
          Set (SexticMumford.CoordinateRing C)) := by
  have hcurveSquare :
      C.f - L₀ ^ 2 =
        a * (Polynomial.C (κ : K) * a * u₀) := by
    rw [hcurve]
    ring
  have hdiv :
      a ∣ Polynomial.C (κ : K) * a * u₀ := by
    refine ⟨Polynomial.C (κ : K) * u₀, ?_⟩
    ring
  have hbezoutSquare :
      ∃ A B E : K[X],
        A * a + B * (2 * L₀) +
            E * (Polynomial.C (κ : K) * a * u₀) = 1 :=
    curveFactor_bezout C a
      (Polynomial.C (κ : K) * a * u₀) L₀
      ha hcurveSquare
  have hbezoutCantor :
      ∃ A B E : K[X],
        A * a ^ 2 + B * (2 * L₀) +
            E * (Polynomial.C (κ : K) * u₀) = 1 :=
    curveFactor_bezout C (a ^ 2)
      (Polynomial.C (κ : K) * u₀) L₀
      (pow_ne_zero 2 ha) hcurve
  have hsquare :
      mumfordIdeal C a L₀ ^ 2 =
        mumfordIdeal C (a ^ 2) L₀ :=
    mumfordIdeal_sq_eq_square_generator
      C a (Polynomial.C (κ : K) * a * u₀) L₀
      hcurveSquare hdiv hbezoutSquare
  have hscale :
      mumfordIdeal C
          (Polynomial.C (κ : K) * u₀) L₀ =
        mumfordIdeal C u₀ L₀ :=
    mumfordIdeal_C_mul C κ u₀ L₀
  have hgraphIdeal :
      mumfordIdeal C u₀ L₀ =
        mumfordIdeal C u₀ v₀ :=
    mumfordIdeal_eq_of_dvd_sub C u₀ v₀ L₀ hgraph
  calc
    mumfordIdeal C a L₀ ^ 2 *
          mumfordIdeal C u₀ v₀ =
        mumfordIdeal C (a ^ 2) L₀ *
          mumfordIdeal C
            (Polynomial.C (κ : K) * u₀) L₀ := by
              rw [hsquare, hscale, hgraphIdeal]
    _ =
        Ideal.span
          ({ySubClass C L₀} :
            Set (SexticMumford.CoordinateRing C)) :=
      mumfordIdeal_mul_cantor C
        (a ^ 2) (Polynomial.C (κ : K) * u₀) L₀
        hcurve hbezoutCantor

private def PadeRootIdeal (C : SexticMumford.Model K) : Type u :=
  Ideal (SexticMumford.CoordinateRing C)

private def PadeRootUnit (C : SexticMumford.Model K) : Type u :=
  SexticMumford.InvFrac C

private def PadeRootCoeEq (C : SexticMumford.Model K)
    (a L₀ : K[X]) (root : PadeRootUnit C) : Prop :=
  ((root⁻¹ : SexticMumford.InvFrac C) :
      FractionalIdeal
        (SexticMumford.CoordinateRing C)⁰
        (SexticMumford.FunctionField C)) =
    ((mumfordIdeal C a L₀ : PadeRootIdeal C) :
      FractionalIdeal
        (SexticMumford.CoordinateRing C)⁰
        (SexticMumford.FunctionField C))

private def PadeRootSquareEq (C : SexticMumford.Model K)
    (D : SexticMumford.SemiMumford C)
    (L₀ : K[X]) (root : PadeRootUnit C) : Prop :=
  mumfordIdealUnit C D *
      toPrincipalIdeal
        (SexticMumford.CoordinateRing C)
        (SexticMumford.FunctionField C)
        (ySubFunctionUnit C L₀)⁻¹ =
    (show SexticMumford.InvFrac C from root) ^ 2

section
attribute [local irreducible] PadeRootIdeal PadeRootUnit
/-- The exact graph geometry retained by the Padé square root.  The inverse
of `root` is literally the auxiliary graph ideal `(a,Y-L₀)`, while
`square_eq` is the finite ideal identity used by the quotient proof. -/
structure PadeIdealRootData
    (C : SexticMumford.Model K)
    (D : SexticMumford.SemiMumford C)
    (a L₀ : K[X]) where
  root : PadeRootUnit C
  inverseRoot_coe : PadeRootCoeEq C a L₀ root
  square_eq : PadeRootSquareEq C D L₀ root
end
attribute [reducible] PadeRootIdeal PadeRootUnit PadeRootCoeEq PadeRootSquareEq

/-- The integral Padé identity already makes the auxiliary graph ideal
invertible: an explicit inverse is `J · I_D · (Y-L)⁻¹`.  Hence the target
Mumford fractional ideal is the square of `J⁻¹` after multiplying by the
inverse graph function.  This version retains the literal graph ideal. -/
def padeIdealRootData
    (C : SexticMumford.Model K)
    (D : SexticMumford.SemiMumford C)
    (a L₀ : K[X])
    (hideal :
      mumfordIdeal C a L₀ ^ 2 *
          mumfordIdeal C D.u D.v =
        Ideal.span
          ({ySubClass C L₀} :
            Set (SexticMumford.CoordinateRing C))) :
    PadeIdealRootData C D a L₀ := by
  let J₀ :
      FractionalIdeal
        (SexticMumford.CoordinateRing C)⁰
        (SexticMumford.FunctionField C) :=
    (mumfordIdeal C a L₀ :
      FractionalIdeal
        (SexticMumford.CoordinateRing C)⁰
        (SexticMumford.FunctionField C))
  let Dᵤ : SexticMumford.InvFrac C :=
    mumfordIdealUnit C D
  let Pᵤ : SexticMumford.InvFrac C :=
    toPrincipalIdeal
      (SexticMumford.CoordinateRing C)
      (SexticMumford.FunctionField C)
      (ySubFunctionUnit C L₀)
  have hfrac :
      J₀ * J₀ *
          (Dᵤ :
            FractionalIdeal
              (SexticMumford.CoordinateRing C)⁰
              (SexticMumford.FunctionField C)) =
        (Pᵤ :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)) := by
    dsimp only [J₀, Dᵤ, Pᵤ]
    simp only [coe_mumfordIdealUnit,
      coe_toPrincipalIdeal, coe_ySubFunctionUnit]
    rw [← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul,
      ← pow_two, hideal,
      FractionalIdeal.coeIdeal_span_singleton]
  have hJmul :
      J₀ *
          (J₀ *
            (Dᵤ :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) *
            ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C))) =
        1 := by
    calc
      J₀ *
            (J₀ *
              (Dᵤ :
                FractionalIdeal
                  (SexticMumford.CoordinateRing C)⁰
                  (SexticMumford.FunctionField C)) *
              ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
                FractionalIdeal
                  (SexticMumford.CoordinateRing C)⁰
                  (SexticMumford.FunctionField C))) =
          (J₀ * J₀ *
              (Dᵤ :
                FractionalIdeal
                  (SexticMumford.CoordinateRing C)⁰
                  (SexticMumford.FunctionField C))) *
            ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) := by
                  ac_rfl
      _ =
          (Pᵤ :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) *
            ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) := by
                  rw [hfrac]
      _ = 1 := by
        rw [← Units.val_mul]
        simp
  let Jᵤ : SexticMumford.InvFrac C :=
    Units.mkOfMulEqOne
      J₀
      (J₀ *
        (Dᵤ :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)) *
        ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)))
      hJmul
  have hunit :
      Jᵤ ^ 2 * Dᵤ = Pᵤ := by
    apply Units.ext
    change
      J₀ ^ 2 *
          (Dᵤ :
            FractionalIdeal
              (SexticMumford.CoordinateRing C)⁰
              (SexticMumford.FunctionField C)) =
        (Pᵤ :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C))
    simpa only [pow_two] using hfrac
  refine
    { root := Jᵤ⁻¹
      inverseRoot_coe := ?_
      square_eq := ?_ }
  · change
      (((Jᵤ⁻¹)⁻¹ : SexticMumford.InvFrac C) :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)) =
        J₀
    rw [inv_inv]
    rfl
  · dsimp only [PadeRootSquareEq]
    rw [map_inv]
    change Dᵤ * Pᵤ⁻¹ = Jᵤ⁻¹ ^ 2
    rw [← hunit]
    simp only [mul_inv_rev, pow_two]
    rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- Existential compatibility wrapper for the original finite-square
interface. -/
theorem exists_invFrac_square_of_pade_identity
    (C : SexticMumford.Model K)
    (D : SexticMumford.SemiMumford C)
    (a L₀ : K[X])
    (hideal :
      mumfordIdeal C a L₀ ^ 2 *
          mumfordIdeal C D.u D.v =
        Ideal.span
          ({ySubClass C L₀} :
            Set (SexticMumford.CoordinateRing C))) :
    ∃ R : SexticMumford.InvFrac C,
      mumfordIdealUnit C D *
          toPrincipalIdeal
            (SexticMumford.CoordinateRing C)
            (SexticMumford.FunctionField C)
            (ySubFunctionUnit C L₀)⁻¹ =
        R ^ 2 :=
  let R := padeIdealRootData C D a L₀ hideal
  ⟨R.root, R.square_eq⟩

/-! ## Closing the finite ideal square -/

/-- The full nondegenerate Padé graph retained before passage to the
fractional-ideal quotient.  Besides the exact square root, this records the
scaled graph polynomial and its literal compatibility with the original
Mumford representative. -/
structure FinitePadeGraphRootData
    (D : LowRep) (a : ℚ[X]) where
  L₀ : ℚ[X]
  κ : ℚˣ
  curve_eq :
    N13Mumford.f ℚ - L₀ ^ 2 =
      a ^ 2 * (Polynomial.C (κ : ℚ) * D.toSemi.u)
  graph_eq :
    D.toSemi.u ∣ L₀ - D.toSemi.v
  rootData :
    PadeIdealRootData M D.toSemi a L₀

/-- A uniform finite square root together with a literal graph-ideal
presentation.  `inverseOrientation = false` means that `idealRoot` itself is
the graph ideal; `true` means that its inverse is the graph ideal. -/
structure FiniteIdealGraphRootData (D : LowRep) where
  idealRoot : InvFrac M
  principalCorrection : (FunctionField M)ˣ
  square_eq :
    mumfordIdealUnit M D.toSemi *
        toPrincipalIdeal
          (CoordinateRing M) (FunctionField M)
          principalCorrection =
      idealRoot ^ 2
  graphU : ℚ[X]
  graphV : ℚ[X]
  graphU_ne_zero : graphU ≠ 0
  graphU_degree_le_two : graphU.natDegree ≤ 2
  graph_curve_dvd :
    graphU ∣ N13Mumford.f ℚ - graphV ^ 2
  inverseOrientation : Bool
  graph_eq :
    (((if inverseOrientation then idealRoot⁻¹ else idealRoot) :
        InvFrac M) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        (mumfordIdeal M graphU graphV :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

namespace FinitePadeGraphRootData

/-- Forget the extra Padé equations while retaining the exact graph ideal
which presents the chosen root. -/
def toFiniteIdealGraphRootData
    {D : LowRep} {a : ℚ[X]}
    (R : FinitePadeGraphRootData D a)
    (ha : a ≠ 0)
    (hdegree : a.natDegree ≤ 2) :
    FiniteIdealGraphRootData D where
  idealRoot := R.rootData.root
  principalCorrection :=
    (ySubFunctionUnit M R.L₀)⁻¹
  square_eq := R.rootData.square_eq
  graphU := a
  graphV := R.L₀
  graphU_ne_zero := ha
  graphU_degree_le_two := hdegree
  graph_curve_dvd := by
    refine
      ⟨a *
        (Polynomial.C (R.κ : ℚ) * D.toSemi.u), ?_⟩
    rw [R.curve_eq]
    ring
  inverseOrientation := true
  graph_eq := by
    simpa using R.rootData.inverseRoot_coe

end FinitePadeGraphRootData

namespace FiniteIdealGraphRootData

private theorem normalize_dvd_sub_mod
    (p q : ℚ[X]) :
    normalize q ∣ p - p % normalize q := by
  refine ⟨p / normalize q, ?_⟩
  have hdiv :=
    EuclideanDomain.mod_add_div p (normalize q)
  calc
    p - p % normalize q =
        (p % normalize q +
            normalize q * (p / normalize q)) -
          p % normalize q := by
      rw [hdiv]
    _ = normalize q * (p / normalize q) := by
      ring

/-- Canonical monic/remainder Mumford data presenting the retained graph.
This is a generic-fibre normalization only; it makes no two-adic
integrality assertion. -/
def normalizedGraphMumford
    {D : LowRep} (R : FiniteIdealGraphRootData D) :
    SexticMumford.Mumford M where
  u := normalize R.graphU
  v := R.graphV % normalize R.graphU
  nInf := 0
  u_monic := monic_normalize R.graphU_ne_zero
  deg_u := by
    have hdegree :
        (normalize R.graphU).natDegree =
          R.graphU.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated
          (associated_normalize R.graphU).symm)
    rw [hdegree]
    exact R.graphU_degree_le_two
  v_reduced := by
    apply
      (mod_eq_self_iff
        (monic_normalize R.graphU_ne_zero).ne_zero).mpr
    exact
      degree_mod_lt _
        (monic_normalize R.graphU_ne_zero).ne_zero
  curve_dvd := by
    have hnBase :
        normalize R.graphU ∣
          M.f - R.graphV ^ 2 :=
      (associated_normalize R.graphU).symm.dvd.trans
        R.graph_curve_dvd
    have hnGraph :
        normalize R.graphU ∣
          R.graphV -
            R.graphV % normalize R.graphU :=
      normalize_dvd_sub_mod R.graphV R.graphU
    obtain ⟨a, ha⟩ := hnBase
    obtain ⟨b, hb⟩ := hnGraph
    refine
      ⟨a + b *
        (R.graphV +
          R.graphV % normalize R.graphU), ?_⟩
    calc
      M.f -
            (R.graphV % normalize R.graphU) ^ 2 =
          (M.f - R.graphV ^ 2) +
            (R.graphV -
                R.graphV % normalize R.graphU) *
              (R.graphV +
                R.graphV % normalize R.graphU) := by
            ring
      _ =
          normalize R.graphU * a +
            (normalize R.graphU * b) *
              (R.graphV +
                R.graphV % normalize R.graphU) := by
            rw [ha, hb]
      _ =
          normalize R.graphU *
            (a + b *
              (R.graphV +
                R.graphV % normalize R.graphU)) := by
            ring
  infinity_bound := by
    have hdegree :
        (normalize R.graphU).natDegree =
          R.graphU.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated
          (associated_normalize R.graphU).symm)
    rw [hdegree]
    exact R.graphU_degree_le_two

/-- The canonical normalized Mumford pair gives exactly the same graph
ideal as the retained Padé presentation. -/
theorem mumfordIdeal_normalizedGraphMumford
    {D : LowRep} (R : FiniteIdealGraphRootData D) :
    mumfordIdeal M
        (normalizedGraphMumford R).u
        (normalizedGraphMumford R).v =
      mumfordIdeal M R.graphU R.graphV := by
  calc
    mumfordIdeal M
          (normalize R.graphU)
          (R.graphV % normalize R.graphU) =
        mumfordIdeal M
          (normalize R.graphU) R.graphV := by
      apply mumfordIdeal_eq_of_dvd_sub
      obtain ⟨q, hq⟩ :=
        normalize_dvd_sub_mod R.graphV R.graphU
      refine ⟨-q, ?_⟩
      calc
        R.graphV % normalize R.graphU - R.graphV =
            -(R.graphV -
              R.graphV % normalize R.graphU) := by
                ring
        _ = -(normalize R.graphU * q) := by
              rw [hq]
        _ = normalize R.graphU * (-q) := by
              ring
    _ = mumfordIdeal M R.graphU R.graphV := by
      exact
        mumfordIdeal_eq_of_dvd_dvd
          M (normalize R.graphU) R.graphU R.graphV
            (associated_normalize R.graphU).symm.dvd
            (associated_normalize R.graphU).dvd

/-- A retained graph of degree zero is the unit ideal.  Consequently the
selected fractional root is itself trivial, independently of which
orientation presents the graph. -/
theorem idealRoot_eq_one_of_graphU_natDegree_eq_zero
    {D : LowRep} (R : FiniteIdealGraphRootData D)
    (hdeg : R.graphU.natDegree = 0) :
    R.idealRoot = 1 := by
  have hconstant :
      R.graphU =
        Polynomial.C (R.graphU.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff :
      R.graphU.coeff 0 ≠ 0 := by
    intro hzero
    apply R.graphU_ne_zero
    rw [hconstant, hzero, Polynomial.C_0]
  let κ : ℚˣ :=
    Units.mk0 (R.graphU.coeff 0) hcoeff
  have hscaled :
      R.graphU =
        Polynomial.C (κ : ℚ) * 1 := by
    rw [hconstant, mul_one]
    rfl
  have hgraphTop :
      mumfordIdeal M R.graphU R.graphV = ⊤ := by
    calc
      mumfordIdeal M R.graphU R.graphV =
          mumfordIdeal M
            (Polynomial.C (κ : ℚ) * 1) R.graphV := by
        rw [hscaled]
      _ = mumfordIdeal M 1 R.graphV :=
        mumfordIdeal_C_mul M κ 1 R.graphV
      _ = ⊤ := by
        rw [mumfordIdeal, Ideal.eq_top_iff_one]
        exact Ideal.subset_span (by simp [xClass_one])
  by_cases hOrientation : R.inverseOrientation = true
  · have h := R.graph_eq
    simp only [hOrientation, if_pos] at h
    rw [hgraphTop] at h
    have hinv : R.idealRoot⁻¹ = 1 :=
      Units.ext h
    simpa using congrArg Inv.inv hinv
  · have hFalse :
        R.inverseOrientation = false :=
      Bool.eq_false_of_not_eq_true hOrientation
    have h := R.graph_eq
    simp only [hFalse, Bool.false_eq_true, if_false] at h
    rw [hgraphTop] at h
    exact Units.ext h

end FiniteIdealGraphRootData

/-- Construct the exact nondegenerate Padé graph together with the
fractional-ideal root whose inverse is that graph ideal. -/
def finitePadeGraphRootData
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X])
    (c b : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hb : b ≠ 0)
    (hbSq : b ^ 2 = c / (q : ℚ))
    (hgraph :
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v)
    (hc : c ≠ 0)
    (ha : a ≠ 0) :
    FinitePadeGraphRootData D a := by
  let hscaled :=
    exists_scaled_pade_graph
      D q a l c b hrelation hb hbSq hgraph hc
  let L₀ := Classical.choose hscaled
  let hκ := Classical.choose_spec hscaled
  let κ := Classical.choose hκ
  have hscaled_spec := Classical.choose_spec hκ
  have hcurve := hscaled_spec.1
  have hgraphScaled := hscaled_spec.2
  have hideal :
      mumfordIdeal M a L₀ ^ 2 *
          mumfordIdeal M D.toSemi.u D.toSemi.v =
        Ideal.span
          ({ySubClass M L₀} :
            Set (CoordinateRing M)) :=
    mumfordIdeal_pade_half
      M a D.toSemi.u D.toSemi.v L₀ κ
        hcurve hgraphScaled ha
  exact
    { L₀ := L₀
      κ := κ
      curve_eq := hcurve
      graph_eq := hgraphScaled
      rootData :=
        padeIdealRootData M D.toSemi a L₀ hideal }

/-- Once the quotient argument supplies a rational graph scalar, the
uniform scaling lemma and Cantor identity produce the required finite
fractional-ideal square. -/
theorem exists_finiteIdealSquareRoot_of_pade_graph
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X])
    (c b : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hb : b ≠ 0)
    (hbSq : b ^ 2 = c / (q : ℚ))
    (hgraph :
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v)
    (hc : c ≠ 0)
    (ha : a ≠ 0) :
    ∃ I : InvFrac M,
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 :=
  let R :=
    finitePadeGraphRootData
      D q a l c b hrelation hb hbSq hgraph hc ha
  ⟨R.rootData.root,
    (ySubFunctionUnit M R.L₀)⁻¹,
    R.rootData.square_eq⟩

/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
def finiteIdealGraphRootData_of_zero_pade_scalar
    (D : LowRep) (q : ℚˣ)
    (a l : ℚ[X])
    (ha : a ≠ 0)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 =
        a ^ 2 * D.toSemi.u) :
    FiniteIdealGraphRootData D := by
  have hl : l ≠ 0 := by
    intro hl
    have hzero :
        a ^ 2 * D.toSemi.u = 0 := by
      rw [← hrelation, hl]
      simp
    exact
      (mul_ne_zero (pow_ne_zero 2 ha)
        D.toSemi.u_monic.ne_zero) hzero
  have hq :
      IsUnit (Polynomial.C (q : ℚ)) :=
    Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (Units.ne_zero q))
  let hbExists :=
    PadeZeroConstantSquare.exists_monic_square_root_of_relation
      hq hl D.toSemi.u_monic D.degree_le_two hrelation
  let b := Classical.choose hbExists
  have hbSpec := Classical.choose_spec hbExists
  have hbMonic := hbSpec.1
  have hub := hbSpec.2.2
  have hbDegree : b.natDegree ≤ 2 :=
    hbSpec.2.1.trans (by norm_num)
  let hwExists := D.toSemi.curve_dvd
  let w := Classical.choose hwExists
  have hw := Classical.choose_spec hwExists
  have hcurve :
      M.f - D.toSemi.v ^ 2 =
        b * (b * w) := by
    calc
      M.f - D.toSemi.v ^ 2 =
          D.toSemi.u * w := hw
      _ = b * (b * w) := by
        rw [hub]
        ring
  have hbezout :
      ∃ A B E : ℚ[X],
        A * b + B * (2 * D.toSemi.v) +
            E * (b * w) = 1 :=
    curveFactor_bezout
      M b (b * w) D.toSemi.v
        hbMonic.ne_zero hcurve
  have hideal :
      mumfordIdeal M b D.toSemi.v ^ 2 =
        mumfordIdeal M D.toSemi.u D.toSemi.v := by
    have hsquare :=
      mumfordIdeal_sq_eq_square_generator
        M b (b * w) D.toSemi.v
          hcurve ⟨w, rfl⟩ hbezout
    rw [← hub] at hsquare
    exact hsquare
  let J₀ :
      FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M) :=
    (mumfordIdeal M b D.toSemi.v :
      FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M))
  have hfrac :
      J₀ ^ 2 =
        ((mumfordIdealUnit M D.toSemi :
          InvFrac M) :
            FractionalIdeal
              (CoordinateRing M)⁰
              (FunctionField M)) := by
    dsimp only [J₀]
    simp only [coe_mumfordIdealUnit]
    rw [pow_two, ← FractionalIdeal.coeIdeal_mul,
      ← pow_two, hideal]
  let hroot :=
    SquareRootUnitLift.exists_unit_val_eq_and_sq_eq
      J₀ (mumfordIdealUnit M D.toSemi) hfrac
  let J := Classical.choose hroot
  have hJ := Classical.choose_spec hroot
  exact
    { idealRoot := J
      principalCorrection := 1
      square_eq := by
        simpa only [map_one, mul_one] using hJ.2.symm
      graphU := b
      graphV := D.toSemi.v
      graphU_ne_zero := hbMonic.ne_zero
      graphU_degree_le_two := hbDegree
      graph_curve_dvd := ⟨b * w, hcurve⟩
      inverseOrientation := false
      graph_eq := by
        change
          (J :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) =
            J₀
        exact hJ.1 }

/-- Compatibility wrapper which forgets the retained direct graph
presentation in the zero-`c` branch. -/
theorem exists_finiteIdealSquareRoot_of_zero_pade_scalar
    (D : LowRep) (q : ℚˣ)
    (a l : ℚ[X])
    (ha : a ≠ 0)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 =
        a ^ 2 * D.toSemi.u) :
    ∃ I : InvFrac M,
      mumfordIdealUnit M D.toSemi = I ^ 2 := by
  let R :=
    finiteIdealGraphRootData_of_zero_pade_scalar
      D q a l ha hrelation
  refine ⟨R.idealRoot, ?_⟩
  have hR := R.square_eq
  have hcorrection : R.principalCorrection = 1 := by
    rfl
  rw [hcorrection] at hR
  simpa only [map_one, mul_one] using hR

/-- A constant monic Mumford polynomial is `1`, so its finite ideal is
already trivial. -/
def finiteIdealGraphRootData_of_natDegree_zero
    (D : LowRep)
    (hu0 : D.toSemi.u.natDegree = 0) :
    FiniteIdealGraphRootData D := by
  have huOne : D.toSemi.u = 1 :=
    D.toSemi.u_monic.natDegree_eq_zero.mp hu0
  have hvZero : D.toSemi.v = 0 := by
    have hred := D.toSemi.v_reduced
    have hmod :
        D.toSemi.v % (1 : ℚ[X]) = 0 :=
      EuclideanDomain.mod_one D.toSemi.v
    rw [huOne, hmod] at hred
    exact hred.symm
  have hunit :
      mumfordIdealUnit M D.toSemi = 1 := by
    apply Units.ext
    change
      (mumfordIdeal M D.toSemi.u D.toSemi.v :
        FractionalIdeal
          (CoordinateRing M)⁰ (FunctionField M)) = 1
    rw [huOne, hvZero,
      show mumfordIdeal M 1 0 = ⊤ from
        zero_mumfordIdeal M]
    rfl
  exact
    { idealRoot := 1
      principalCorrection := 1
      square_eq := by
        rw [hunit]
        simp
      graphU := 1
      graphV := 0
      graphU_ne_zero := one_ne_zero
      graphU_degree_le_two := by simp
      graph_curve_dvd := one_dvd _
      inverseOrientation := false
      graph_eq := by
        change
          ((⊤ : Ideal (CoordinateRing M)) :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) =
            (mumfordIdeal M 1 0 :
              FractionalIdeal
                (CoordinateRing M)⁰ (FunctionField M))
        exact congrArg
          (fun I : Ideal (CoordinateRing M) ↦
            (I :
              FractionalIdeal
                (CoordinateRing M)⁰ (FunctionField M)))
          (zero_mumfordIdeal M).symm }

/-- Compatibility wrapper for the trivial graph-root branch. -/
theorem exists_finiteIdealSquareRoot_of_natDegree_zero
    (D : LowRep)
    (hu0 : D.toSemi.u.natDegree = 0) :
    ∃ I : InvFrac M,
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 :=
  let R :=
    finiteIdealGraphRootData_of_natDegree_zero D hu0
  ⟨R.idealRoot, R.principalCorrection, R.square_eq⟩

/-- The zero-`c` UFD square is a finite ideal square with trivial
principal correction. -/
theorem exists_finiteIdealSquareRoot_of_zero_pade_scalar'
    (D : LowRep) (q : ℚˣ)
    (a l : ℚ[X])
    (ha : a ≠ 0)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 =
        a ^ 2 * D.toSemi.u) :
    ∃ I : InvFrac M,
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 := by
  obtain ⟨I, hI⟩ :=
    exists_finiteIdealSquareRoot_of_zero_pade_scalar
      D q a l ha hrelation
  refine ⟨I, 1, ?_⟩
  simpa only [map_one, mul_one] using hI

/-! ## Squares in the oriented fractional-ideal quotient -/

/-- A raw square root is precisely the divisor-theoretic object that a
full-gauge witness must construct: an oriented invertible fractional ideal
whose square differs from the Mumford ideal by one principal oriented
factor. -/
def HasOrientedIdealSquareRoot (D : LowRep) : Prop :=
  ∃ R : OrientedFrac M,
    ∃ α : (FunctionField M)ˣ,
      semiMumfordRaw M D.toSemi *
          principalOriented M O α =
        R ^ 2

/-- Component form of a raw oriented square root.  It displays separately
the finite fractional-ideal square and the exact evenness equation at the
chosen positive infinity. -/
theorem hasOrientedIdealSquareRoot_iff_exists_components
    (D : LowRep) :
    HasOrientedIdealSquareRoot D ↔
      ∃ I : InvFrac M,
        ∃ α : (FunctionField M)ˣ,
          ∃ k : ℤ,
            mumfordIdealUnit M D.toSemi *
                toPrincipalIdeal
                  (CoordinateRing M) (FunctionField M) α =
              I ^ 2 ∧
            D.toSemi.nInf - 1 +
                Multiplicative.toAdd (O.ordPlus α) =
              2 * k := by
  constructor
  · rintro ⟨R, α, hraw⟩
    refine
      ⟨R.1, α, Multiplicative.toAdd R.2, ?_, ?_⟩
    · exact congrArg Prod.fst hraw
    · have hinf :=
        congrArg
          (fun z : OrientedFrac M =>
            Multiplicative.toAdd z.2) hraw
      have hsum :
          D.toSemi.nInf - 1 +
              Multiplicative.toAdd (O.ordPlus α) =
            Multiplicative.toAdd R.2 +
              Multiplicative.toAdd R.2 := by
        simpa [semiMumfordRaw, principalOriented,
          pow_two] using hinf
      omega
  · rintro ⟨I, α, k, hIdeal, hInf⟩
    refine
      ⟨(I, Multiplicative.ofAdd k), α, ?_⟩
    apply Prod.ext
    · exact hIdeal
    · have hInf' :
          D.toSemi.nInf - 1 +
              Multiplicative.toAdd (O.ordPlus α) =
            k + k := by
        omega
      simpa [semiMumfordRaw, principalOriented,
        pow_two] using
          congrArg Multiplicative.ofAdd hInf'

/-- A raw oriented ideal square root gives a half in the concrete Picard
group. -/
theorem isDouble_of_hasOrientedIdealSquareRoot
    (D : LowRep) (hD : HasOrientedIdealSquareRoot D) :
    ∃ Q : G, N13LowDegreeKummerHom.lowClass D = 2 • Q := by
  obtain ⟨R, α, hraw⟩ := hD
  let H : Subgroup (OrientedFrac M) :=
    (principalOriented M O).range
  let Q : G :=
    Additive.ofMul (QuotientGroup.mk' H R)
  refine ⟨Q, ?_⟩
  have hprincipal :
      QuotientGroup.mk' H (principalOriented M O α) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr
      (MonoidHom.mem_range.mpr ⟨α, rfl⟩)
  change
    Additive.ofMul
        (QuotientGroup.mk' H (semiMumfordRaw M D.toSemi)) =
      2 • Additive.ofMul (QuotientGroup.mk' H R)
  rw [two_nsmul]
  apply congrArg Additive.ofMul
  calc
    QuotientGroup.mk' H (semiMumfordRaw M D.toSemi) =
        QuotientGroup.mk' H (semiMumfordRaw M D.toSemi) * 1 := by
          exact
            (mul_one
              (QuotientGroup.mk' H
                (semiMumfordRaw M D.toSemi))).symm
    _ =
        QuotientGroup.mk' H (semiMumfordRaw M D.toSemi) *
          QuotientGroup.mk' H (principalOriented M O α) := by
          rw [hprincipal]
    _ =
        QuotientGroup.mk' H
          (semiMumfordRaw M D.toSemi *
            principalOriented M O α) := by
          rw [map_mul]
    _ = QuotientGroup.mk' H (R ^ 2) := by
          rw [hraw]
    _ =
        QuotientGroup.mk' H R * QuotientGroup.mk' H R := by
          rw [pow_two, map_mul]

/-- Conversely, every half in the quotient has a raw oriented fractional
ideal representative, so the preceding criterion is exact rather than only
sufficient. -/
theorem isDouble_iff_hasOrientedIdealSquareRoot
    (D : LowRep) :
    (∃ Q : G, N13LowDegreeKummerHom.lowClass D = 2 • Q) ↔
      HasOrientedIdealSquareRoot D := by
  constructor
  · rintro ⟨Q, hQ⟩
    let H : Subgroup (OrientedFrac M) :=
      (principalOriented M O).range
    obtain ⟨R, hR⟩ :=
      QuotientGroup.mk'_surjective H (Additive.toMul Q)
    have hquot :
        QuotientGroup.mk' H (semiMumfordRaw M D.toSemi) =
          QuotientGroup.mk' H (R ^ 2) := by
      have hQ' := congrArg Additive.toMul hQ
      change
        QuotientGroup.mk' H (semiMumfordRaw M D.toSemi) =
          Additive.toMul (2 • Q) at hQ'
      rw [two_nsmul] at hQ'
      change
        QuotientGroup.mk' H (semiMumfordRaw M D.toSemi) =
          Additive.toMul Q * Additive.toMul Q at hQ'
      rw [← hR, ← map_mul, ← pow_two] at hQ'
      exact hQ'
    rw [QuotientGroup.mk'_eq_mk'] at hquot
    obtain ⟨z, hz, hmul⟩ := hquot
    obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨R, α, hmul⟩
  · exact isDouble_of_hasOrientedIdealSquareRoot D

/-! ## Absorbing the remaining infinity coordinate -/

/-- The class with trivial finite ideal and prescribed integer infinity
coordinate. -/
def pureInfinityClass (z : ℤ) : G :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented M O).range
      ((1, Multiplicative.ofAdd z) : OrientedFrac M)

private theorem mumfordIdealUnit_infinityMinus_eq_one :
    mumfordIdealUnit M
        (infinityMinusMumford M).toSemi = 1 := by
  apply Units.ext
  change
    (mumfordIdeal M 1 0 :
      FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M)) = 1
  rw [show mumfordIdeal M 1 0 = ⊤ from zero_mumfordIdeal M]
  rfl

@[simp] theorem pureInfinityClass_neg_one :
    pureInfinityClass (-1) =
      N13KummerKernelAssembly.infinityClass := by
  have hraw :
      mumfordRaw M (infinityMinusMumford M) =
        ((1, Multiplicative.ofAdd (-1)) :
          OrientedFrac M) := by
    apply Prod.ext
    · exact mumfordIdealUnit_infinityMinus_eq_one
    · rfl
  change
    Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M O).range
          (mumfordRaw M (infinityMinusMumford M)))
  rw [hraw]

/-- Every pure integer infinity class is an integral multiple of the
difference of the two infinity points. -/
theorem pureInfinityClass_eq_zsmul_infinityClass
    (z : ℤ) :
    pureInfinityClass z =
      (-z) • N13KummerKernelAssembly.infinityClass := by
  rw [← pureInfinityClass_neg_one]
  change
    Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd z) :
            OrientedFrac M)) =
      Additive.ofMul
        ((QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M)) ^ (-z))
  apply congrArg Additive.ofMul
  have hraw :
      ((1, Multiplicative.ofAdd z) :
          OrientedFrac M) =
        ((1, Multiplicative.ofAdd (-1)) :
          OrientedFrac M) ^ (-z) := by
    apply Prod.ext
    · simp
    · apply Multiplicative.toAdd.injective
      simp
  calc
    QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd z) :
            OrientedFrac M) =
        QuotientGroup.mk'
          (principalOriented M O).range
          (((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M) ^ (-z)) := by
              rw [hraw]
    _ =
        (QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M)) ^ (-z) := by
              exact
                map_zpow
                  (QuotientGroup.mk'
                    (principalOriented M O).range)
                  ((1, Multiplicative.ofAdd (-1)) :
                    OrientedFrac M) (-z)

/-- A finite fractional-ideal square is sufficient for N13.  Whatever
integer remains at infinity is a multiple of `infinityClass`, and the
already constructed N13 half of that class absorbs it. -/
theorem isDouble_of_finiteIdealSquareRoot
    (D : LowRep)
    (hfinite :
      ∃ I : InvFrac M,
        ∃ α : (FunctionField M)ˣ,
          mumfordIdealUnit M D.toSemi *
              toPrincipalIdeal
                (CoordinateRing M) (FunctionField M) α =
            I ^ 2) :
    ∃ Q : G,
      N13LowDegreeKummerHom.lowClass D = 2 • Q := by
  obtain ⟨I, α, hIdeal⟩ := hfinite
  let H : Subgroup (OrientedFrac M) :=
    (principalOriented M O).range
  let e : ℤ :=
    D.toSemi.nInf - 1 +
      Multiplicative.toAdd (O.ordPlus α)
  let R₀ : OrientedFrac M :=
    (I, Multiplicative.ofAdd 0)
  have hraw :
      semiMumfordRaw M D.toSemi *
          principalOriented M O α =
        R₀ ^ 2 *
          ((1, Multiplicative.ofAdd e) :
            OrientedFrac M) := by
    apply Prod.ext
    · change
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 * 1
      rw [hIdeal, mul_one]
    · change
        Multiplicative.ofAdd (D.toSemi.nInf - 1) *
            O.ordPlus α =
          (Multiplicative.ofAdd 0) ^ 2 *
            Multiplicative.ofAdd e
      apply Multiplicative.toAdd.injective
      change
        D.toSemi.nInf - 1 +
            Multiplicative.toAdd (O.ordPlus α) =
          0 * 2 + e
      simp only [zero_mul, zero_add]
      rfl
  have hprincipal :
      QuotientGroup.mk' H
          (principalOriented M O α) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr
      (MonoidHom.mem_range.mpr ⟨α, rfl⟩)
  have hquot :
      QuotientGroup.mk' H
          (semiMumfordRaw M D.toSemi) =
        (QuotientGroup.mk' H R₀) ^ 2 *
          QuotientGroup.mk' H
            ((1, Multiplicative.ofAdd e) :
              OrientedFrac M) := by
    calc
      QuotientGroup.mk' H
            (semiMumfordRaw M D.toSemi) =
          QuotientGroup.mk' H
              (semiMumfordRaw M D.toSemi) * 1 := by
                exact
                  (mul_one
                    (QuotientGroup.mk' H
                      (semiMumfordRaw M D.toSemi))).symm
      _ =
          QuotientGroup.mk' H
              (semiMumfordRaw M D.toSemi) *
            QuotientGroup.mk' H
              (principalOriented M O α) := by
                rw [hprincipal]
      _ =
          QuotientGroup.mk' H
            (semiMumfordRaw M D.toSemi *
              principalOriented M O α) := by
                rw [map_mul]
      _ =
          QuotientGroup.mk' H
            (R₀ ^ 2 *
              ((1, Multiplicative.ofAdd e) :
                OrientedFrac M)) := by
                  rw [hraw]
      _ =
          (QuotientGroup.mk' H R₀) ^ 2 *
            QuotientGroup.mk' H
              ((1, Multiplicative.ofAdd e) :
                OrientedFrac M) := by
                rw [map_mul, map_pow]
  let Q₀ : G :=
    Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M O).range R₀)
  dsimp only [H] at hquot
  have hclass :
      N13LowDegreeKummerHom.lowClass D =
        2 • Q₀ + pureInfinityClass e := by
    change
      Additive.ofMul
          (QuotientGroup.mk'
            (principalOriented M O).range
            (semiMumfordRaw M D.toSemi)) =
        2 •
            Additive.ofMul
              (QuotientGroup.mk'
                (principalOriented M O).range R₀) +
          Additive.ofMul
            (QuotientGroup.mk'
              (principalOriented M O).range
              ((1, Multiplicative.ofAdd e) :
                OrientedFrac M))
    simpa only [ofMul_mul,
      ofMul_pow, two_nsmul] using
        congrArg Additive.ofMul hquot
  refine
    ⟨Q₀ +
      (-e) • N13KummerKernelAssembly.infinityHalfClass, ?_⟩
  rw [hclass,
    pureInfinityClass_eq_zsmul_infinityClass,
    ← N13KummerKernelAssembly.two_nsmul_infinityHalfClass]
  simp only [two_nsmul, zsmul_add]
  abel

/-- Constructive generic output retained from one finite fractional-ideal
square root.  It records the exact root and principal correction together
with its literal graph presentation and the half selected by the existing
quotient proof.  No two-adic integrality assertion is included. -/
structure FiniteIdealHalfData (D : LowRep)
    extends FiniteIdealGraphRootData D where
  half : G
  half_spec :
    N13LowDegreeKummerHom.lowClass D = 2 • half

/-- Retain the graph-presented square root when selecting the half furnished by
`isDouble_of_finiteIdealSquareRoot`. -/
def finiteIdealHalfData
    (D : LowRep)
    (R : FiniteIdealGraphRootData D) :
    FiniteIdealHalfData D := by
  let hhalf :=
    isDouble_of_finiteIdealSquareRoot D
      ⟨R.idealRoot, R.principalCorrection, R.square_eq⟩
  exact
    { toFiniteIdealGraphRootData := R
      half := Classical.choose hhalf
      half_spec := Classical.choose_spec hhalf }

/-! ## The structural full-gauge bridge -/

/-- A negatively normalized full-gauge witness always yields a finite
ideal square.  The proof chooses a Padé numerator by dimension, separates
the genuine UFD branch `c = 0`, and otherwise treats the quotient algebra
according to its rank `0`, `1`, or `2`.  The chosen square root retains a
literal graph-ideal presentation in every branch. -/
def finiteIdealGraphRootData_of_negative_norm_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    FiniteIdealGraphRootData D := by
  let haExists :=
    exists_pade_numerator
      (branchSquarePolynomial β)
  let a := Classical.choose haExists
  have haSpec := Classical.choose_spec haExists
  have ha0 := haSpec.1
  have haKer := haSpec.2
  let hcExists :=
    exists_pade_sextic_scalar
      D β q hfst a ha0 haKer
  let c := Classical.choose hcExists
  have hrelation := Classical.choose_spec hcExists
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have haPoly : (a : ℚ[X]) ≠ 0 := by
    exact fun h => ha0 (Subtype.ext h)
  by_cases hc : c = 0
  · have hzeroRelation :
        Polynomial.C (q : ℚ) * l ^ 2 =
          (a : ℚ[X]) ^ 2 * D.toSemi.u := by
      have h := hrelation
      change Classical.choose hcExists = 0 at hc
      rw [hc] at h
      simp only [Polynomial.C_0, zero_mul] at h
      exact sub_eq_zero.mp h
    exact
      finiteIdealGraphRootData_of_zero_pade_scalar
        D q (a : ℚ[X]) l haPoly hzeroRelation
  · by_cases hu0 : D.toSemi.u.natDegree = 0
    · exact
        finiteIdealGraphRootData_of_natDegree_zero
          D hu0
    · by_cases hu1 : D.toSemi.u.natDegree = 1
      · let hbExists :=
          exists_pade_graph_scalar_of_c_ne_zero_degree_one
            D q (a : ℚ[X]) l c hrelation hu1 hc
        let b := Classical.choose hbExists
        have hbSpec := Classical.choose_spec hbExists
        have hb := hbSpec.1
        have hbSq := hbSpec.2.1
        have hgraph := hbSpec.2.2
        exact
          (finitePadeGraphRootData
              D q (a : ℚ[X]) l c b
                hrelation hb hbSq hgraph hc haPoly).toFiniteIdealGraphRootData
            haPoly (padeNumerator_natDegree_le_two a ha0)
      · have hu2 : D.toSemi.u.natDegree = 2 := by
          have hle := D.degree_le_two
          omega
        let hbExists :=
          exists_pade_graph_scalar_of_c_ne_zero
            D β q a ha0 haKer c
              hrelation hsnd hu2 hc
        let b := Classical.choose hbExists
        have hbSpec := Classical.choose_spec hbExists
        have hb := hbSpec.1
        have hbSq := hbSpec.2.1
        have hgraph := hbSpec.2.2
        exact
          (finitePadeGraphRootData
              D q (a : ℚ[X]) l c b
                hrelation hb hbSq hgraph hc haPoly).toFiniteIdealGraphRootData
            haPoly (padeNumerator_natDegree_le_two a ha0)

/-- Compatibility wrapper which forgets the retained graph presentation. -/
theorem exists_finiteIdealSquareRoot_of_negative_norm_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    ∃ I : InvFrac M,
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 :=
  let R :=
    finiteIdealGraphRootData_of_negative_norm_gauge
      D β q hfst hsnd
  ⟨R.idealRoot, R.principalCorrection, R.square_eq⟩

/-- The original orientation sign can first be normalized by the Gaussian
unit `i`; the preceding theorem then supplies the finite ideal square. -/
def finiteIdealGraphRootData_of_full_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      N13MumfordOrientedFullKummer.orientationSignUnit D *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    FiniteIdealGraphRootData D := by
  let hcoordinates :=
    exists_negative_norm_gauge_coordinates
      D β q hfst hsnd
  let β' := Classical.choose hcoordinates
  let hq := Classical.choose_spec hcoordinates
  let q' := Classical.choose hq
  have hcoordinates_spec := Classical.choose_spec hq
  exact
    finiteIdealGraphRootData_of_negative_norm_gauge
      D β' q' hcoordinates_spec.1 hcoordinates_spec.2

/-- Compatibility wrapper which forgets the graph presentation after
normalizing the orientation sign. -/
theorem exists_finiteIdealSquareRoot_of_full_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      N13MumfordOrientedFullKummer.orientationSignUnit D *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    ∃ I : InvFrac M,
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 :=
  let R :=
    finiteIdealGraphRootData_of_full_gauge
      D β q hfst hsnd
  ⟨R.idealRoot, R.principalCorrection, R.square_eq⟩

/-- The full-gauge coordinate equations therefore imply divisibility by
two in the concrete oriented Picard group. -/
theorem isDouble_of_full_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      N13MumfordOrientedFullKummer.orientationSignUnit D *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    ∃ Q : G,
      N13LowDegreeKummerHom.lowClass D = 2 • Q :=
  isDouble_of_finiteIdealSquareRoot D
    (exists_finiteIdealSquareRoot_of_full_gauge
      D β q hfst hsnd)

/-- Unconditional identity-fibre theorem for the oriented full Kummer
map. -/
theorem identityFiber :
    ∀ P : G,
      N13MumfordOrientedFullKummer.orientedFullKummer P = 1 →
        ∃ Q : G, P = 2 • Q := by
  intro P hP
  obtain ⟨β, q, hfst, hsnd⟩ :=
    (orientedFullKummer_eq_one_iff_exists_coordinates P).mp hP
  obtain ⟨Q, hQ⟩ :=
    isDouble_of_full_gauge
      (N13LowDegreeKummerHom.representative P)
      β q hfst hsnd
  exact
    ⟨Q,
      (N13LowDegreeKummerHom.lowClass_representative P).symm.trans hQ⟩

/-- The structural N13 Kummer kernel is exactly the subgroup of doubles. -/
theorem kernel_eq_doubles :
    ∀ P : G,
      N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
        ∃ Q : G, P = 2 • Q :=
  N13MumfordOrientedFullKummer.kernel_eq_doubles_of_full_identity_fiber
    identityFiber

/-! ## Compatibility with the earlier abstract bridge interface -/

/-- Earlier abstract bridge interface, retained for compatibility.  The
unconditional theorem `identityFiber` above no longer depends on it. -/
def FullGaugeLiftsToOrientedIdealSquareRoot : Prop :=
  ∀ (D : LowRep) (β : Lˣ) (q : ℚˣ),
    N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q →
    N13MumfordOrientedFullKummer.orientationSignUnit D *
          N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3 →
    HasOrientedIdealSquareRoot D

/-- The geometric bridge gives the complete identity-fibre halving theorem. -/
theorem identityFiber_of_fullGaugeLift
    (hLift : FullGaugeLiftsToOrientedIdealSquareRoot) :
    ∀ P : G,
      N13MumfordOrientedFullKummer.orientedFullKummer P = 1 →
        ∃ Q : G, P = 2 • Q := by
  intro P hP
  obtain ⟨β, q, hfst, hsnd⟩ :=
    (orientedFullKummer_eq_one_iff_exists_coordinates P).mp hP
  obtain ⟨Q, hQ⟩ :=
    isDouble_of_hasOrientedIdealSquareRoot
      (N13LowDegreeKummerHom.representative P)
      (hLift (N13LowDegreeKummerHom.representative P)
        β q hfst hsnd)
  exact ⟨Q,
    (N13LowDegreeKummerHom.lowClass_representative P).symm.trans hQ⟩

/-- Once the bridge is proved, the structural Kummer kernel is exactly the
subgroup of doubles. -/
theorem kernel_eq_doubles_of_fullGaugeLift
    (hLift : FullGaugeLiftsToOrientedIdealSquareRoot) :
    ∀ P : G,
      N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
        ∃ Q : G, P = 2 • Q :=
  N13MumfordOrientedFullKummer.kernel_eq_doubles_of_full_identity_fiber
    (identityFiber_of_fullGaugeLift hLift)

end

end MazurProof.N13MumfordFullKummerIdentityFiber


