-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerNorm_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerNorm_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:18:49.729453+00:00
-- url     : https://prove2.me/theorems/7894d4fe-c8ae-4c96-bf13-239d73ed685b
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordKummerNorm source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordKummerNorm

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordKummerNorm
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LowDegreeKummerHom_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FullNormPair_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_PowerBasisDiscriminant_p0

set_option autoImplicit false




/-!
# The square norm of an N13 Mumford Kummer value

For a Mumford pair `(u,v)`, the relation

`f - v² = u w`

implies structurally that

`Norm(u(θ)) = Res(f,u) = Res(u,v)²`.

This is the global norm condition used by the weak two-descent.  The proof
uses functorial identities of the resultant; it neither splits `u` nor
separates its possible degrees.
-/

open Polynomial

namespace MazurProof.N13MumfordKummerNorm

noncomputable section

abbrev L : Type :=
  N13SexticSquareclass.SexticAlgebra

abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep

/-- The canonical rational square root supplied by the Mumford congruence. -/
def normRoot (D : LowRep) : ℚ :=
  D.toSemi.u.resultant D.toSemi.v

private theorem v_sq_natDegree_lt_six (D : LowRep) :
    (D.toSemi.v ^ 2).natDegree < 6 := by
  by_cases hu0 : D.toSemi.u.natDegree = 0
  · have huone : D.toSemi.u = 1 :=
      D.toSemi.u_monic.natDegree_eq_zero.mp hu0
    have hvzero : D.toSemi.v = 0 := by
      have hred := D.toSemi.v_reduced
      have hzero : D.toSemi.v % (1 : ℚ[X]) = 0 := by
        exact EuclideanDomain.mod_one _
      rw [huone, hzero] at hred
      exact hred.symm
    rw [hvzero]
    norm_num
  · have huone : D.toSemi.u ≠ 1 := by
      intro h
      apply hu0
      rw [h, natDegree_one]
    have hvlt :
        D.toSemi.v.natDegree < D.toSemi.u.natDegree := by
      have hmod :=
        natDegree_modByMonic_lt D.toSemi.v
          D.toSemi.u_monic huone
      rw [modByMonic_eq_mod D.toSemi.v D.toSemi.u_monic,
        D.toSemi.v_reduced] at hmod
      exact hmod
    calc
      (D.toSemi.v ^ 2).natDegree =
          2 * D.toSemi.v.natDegree :=
        Polynomial.natDegree_pow _ _
      _ < 6 := by
        have hdu := D.degree_le_two
        omega

/-- The cofactor has the complementary degree.  This will later turn the
principal ideal of `u(θ)` into a square away from the discriminant. -/
theorem exists_curveFactor_degree (D : LowRep) :
    ∃ w : ℚ[X],
      N13Mumford.f ℚ - D.toSemi.v ^ 2 =
          D.toSemi.u * w ∧
      D.toSemi.u.natDegree + w.natDegree = 6 := by
  obtain ⟨w, hw⟩ := D.toSemi.curve_dvd
  change
    N13Mumford.f ℚ - D.toSemi.v ^ 2 =
      D.toSemi.u * w at hw
  have hleft :
      (N13Mumford.f ℚ - D.toSemi.v ^ 2).natDegree = 6 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt
      (by
        rw [N13Mumford.f_natDegree]
        exact v_sq_natDegree_lt_six D)]
    exact N13Mumford.f_natDegree (K := ℚ)
  have hprod : D.toSemi.u * w ≠ 0 := by
    intro hzero
    have := congrArg Polynomial.natDegree hzero
    rw [← hw, hleft, natDegree_zero] at this
    omega
  have hwzero : w ≠ 0 := fun hw0 => hprod (by rw [hw0, mul_zero])
  refine ⟨w, hw, ?_⟩
  calc
    D.toSemi.u.natDegree + w.natDegree =
        (D.toSemi.u * w).natDegree := by
      rw [Polynomial.natDegree_mul
        D.toSemi.u_monic.ne_zero hwzero]
    _ = 6 := by rw [← hw, hleft]

/-- The norm resultant is a square before passing to square classes. -/
theorem resultant_f_u_eq_normRoot_sq (D : LowRep) :
    (N13Mumford.f ℚ).resultant D.toSemi.u =
      normRoot D ^ 2 := by
  obtain ⟨w, hw, hdegree⟩ :=
    exists_curveFactor_degree D
  let f : ℚ[X] := N13Mumford.f ℚ
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  have hfdeg : f.natDegree = 6 :=
    by
      simpa only [f] using
        (N13Mumford.f_natDegree (K := ℚ))
  have hudeg : u.natDegree ≤ 2 :=
    D.degree_le_two
  have hv2le : (v ^ 2).natDegree ≤ 6 :=
    (v_sq_natDegree_lt_six D).le
  have hwdeg : w.natDegree + u.natDegree ≤ 6 := by
    rw [add_comm, hdegree]
  have hdecomp : f = v ^ 2 + u * w := by
    dsimp only [f, u, v]
    linear_combination hw
  have hsign :
      (-1 : ℚ) ^ (f.natDegree * u.natDegree) = 1 := by
    rw [hfdeg]
    conv_lhs => rw [show 6 * u.natDegree = 2 * (3 * u.natDegree) by omega]
    rw [pow_mul]
    norm_num
  have hpad :
      u.resultant (v ^ 2) u.natDegree 6 =
        u.resultant (v ^ 2) u.natDegree
          (v ^ 2).natDegree := by
    calc
      u.resultant (v ^ 2) u.natDegree 6 =
          u.resultant (v ^ 2) u.natDegree
            ((v ^ 2).natDegree +
              (6 - (v ^ 2).natDegree)) := by
        rw [Nat.add_sub_of_le hv2le]
      _ =
          u.coeff u.natDegree ^
              (6 - (v ^ 2).natDegree) *
            u.resultant (v ^ 2) u.natDegree
              (v ^ 2).natDegree := by
        rw [Polynomial.resultant_add_right_deg
          u (v ^ 2) u.natDegree (v ^ 2).natDegree
          (6 - (v ^ 2).natDegree) le_rfl]
      _ = _ := by
        simp only [u, D.toSemi.u_monic.coeff_natDegree,
          one_pow, one_mul]
  have hsquare :
      u.resultant (v ^ 2) u.natDegree
          (v ^ 2).natDegree =
        (u.resultant v u.natDegree v.natDegree) ^ 2 := by
    have hvpow :
        (v ^ 2).natDegree =
          v.natDegree + v.natDegree := by
      rw [Polynomial.natDegree_pow]
      omega
    rw [hvpow, pow_two]
    simpa only [pow_two] using
      (Polynomial.resultant_mul_right
        u v v u.natDegree le_rfl)
  change
    f.resultant u f.natDegree u.natDegree =
      (u.resultant v u.natDegree v.natDegree) ^ 2
  calc
    f.resultant u f.natDegree u.natDegree =
        (-1 : ℚ) ^ (f.natDegree * u.natDegree) *
          u.resultant f u.natDegree f.natDegree :=
      Polynomial.resultant_comm f u f.natDegree u.natDegree
    _ = u.resultant f u.natDegree 6 := by
      rw [hsign, one_mul, hfdeg]
    _ =
        u.resultant (v ^ 2 + u * w) u.natDegree 6 := by
      rw [← hdecomp]
    _ = u.resultant (v ^ 2) u.natDegree 6 := by
      exact Polynomial.resultant_add_mul_right
        u (v ^ 2) w u.natDegree 6 hwdeg le_rfl
    _ =
        u.resultant (v ^ 2) u.natDegree
          (v ^ 2).natDegree := hpad
    _ = _ := hsquare

/-- The actual low-degree Kummer value has rational square norm. -/
theorem norm_uTheta_eq_normRoot_sq (D : LowRep) :
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
      normRoot D ^ 2 := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :=
    PowerBasisDiscriminant.norm_aeval_adjoinRoot_eq_resultant
      (N13Mumford.f_monic (K := ℚ))
      N13SexticIrreducible.n13Mumford_f_irreducible
      D.toSemi.u
  calc
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
        (N13Mumford.f ℚ).resultant D.toSemi.u := by
      rw [N13MumfordKummerValue.uTheta_eq_mk]
      change
        Algebra.norm ℚ
            (AdjoinRoot.mk (N13Mumford.f ℚ) D.toSemi.u) =
          (N13Mumford.f ℚ).resultant D.toSemi.u
      rw [← AdjoinRoot.aeval_eq]
      exact hnorm
    _ = normRoot D ^ 2 :=
      resultant_f_u_eq_normRoot_sq D

theorem normRoot_ne_zero (D : LowRep) :
    normRoot D ≠ 0 := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :
      Algebra.norm ℚ
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr
      (N13MumfordKummerValue.uTheta_ne_zero
        (N13LowDegreeKummerHom.asMumford D))
  intro hzero
  apply hnorm
  calc
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
        normRoot D ^ 2 :=
      norm_uTheta_eq_normRoot_sq D
    _ = 0 := by rw [hzero]; simp

/-- The chosen square root of the norm, as a rational unit. -/
def normRootUnit (D : LowRep) : ℚˣ :=
  Units.mk0 (normRoot D) (normRoot_ne_zero D)

@[simp] theorem normRootUnit_val (D : LowRep) :
    (normRootUnit D : ℚ) = normRoot D :=
  rfl

/-- The genuine full norm pair attached to a low-degree Mumford
representative. -/
def mumfordNormPair (D : LowRep) :
    N13FullNormPair.NormPair :=
  ⟨(N13MumfordKummerValue.uThetaUnit
      (N13LowDegreeKummerHom.asMumford D),
    normRootUnit D), by
    apply Units.ext
    exact norm_uTheta_eq_normRoot_sq D⟩

@[simp] theorem mumfordNormPair_fst (D : LowRep) :
    EvenSexticNormPair.fstHom N13FullNormPair.normUnits
        (mumfordNormPair D) =
      N13MumfordKummerValue.uThetaUnit
        (N13LowDegreeKummerHom.asMumford D) :=
  rfl

@[simp] theorem mumfordNormPair_snd (D : LowRep) :
    EvenSexticNormPair.sndHom N13FullNormPair.normUnits
        (mumfordNormPair D) =
      normRootUnit D :=
  rfl

/-- Its class in the full even-sextic descent target. -/
def mumfordFullClass (D : LowRep) :
    N13FullNormPair.FullTarget :=
  QuotientGroup.mk'
    (EvenSexticNormPair.fullGauge
      N13FullNormPair.normUnits
      N13FullNormPair.scalarUnits
      N13FullNormPair.normUnits_scalarUnits)
    (mumfordNormPair D)

/-- Forgetting the norm root recovers exactly the existing raw fake Kummer
coordinate. -/
theorem forget_mumfordFullClass (D : LowRep) :
    N13FullNormPair.forget (mumfordFullClass D) =
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) :
          N13FullNormPair.Lˣ) :
        N13FullNormPair.FakeTarget) := by
  rfl

end

end MazurProof.N13MumfordKummerNorm


