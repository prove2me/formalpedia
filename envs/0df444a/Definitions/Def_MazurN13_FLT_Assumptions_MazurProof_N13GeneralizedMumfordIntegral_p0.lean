-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:53:03.51399+00:00
-- url     : https://prove2.me/theorems/89c1198b-f725-48be-9469-a6f610213dcc
-- title:
--   FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false




/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordIntegral

noncomputable section

universe u

variable {R : Type u} [CommRing R]

def hPoly : R[X] :=
  X ^ 3 + X + 1

def rhsPoly : R[X] :=
  X ^ 5 + X ^ 4

def curvePoly : R[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem curvePoly_monic : (curvePoly : R[X][X]).Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree [Nontrivial R] :
    (curvePoly : R[X][X]).natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

abbrev CoordinateRing : Type u :=
  AdjoinRoot (curvePoly : R[X][X])

noncomputable instance instAlgebraCoordinateRing : Algebra R (CoordinateRing (R := R)) :=
  inferInstance

noncomputable instance instAlgebraPolynomialCoordinateRing : Algebra R[X] (CoordinateRing (R := R)) :=
  inferInstance

def mk : R[X][X] →+* CoordinateRing (R := R) :=
  AdjoinRoot.mk (curvePoly (R := R))

def xClass (p : R[X]) : CoordinateRing (R := R) :=
  mk (R := R) (C p)

def yClass : CoordinateRing (R := R) :=
  mk (R := R) X

def xClassHom : R[X] →+* CoordinateRing (R := R) :=
  AdjoinRoot.of (curvePoly (R := R))

@[simp] theorem xClassHom_apply (p : R[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass (0 : R[X]) = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass (1 : R[X]) = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : R[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : R[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : R[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : R[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

def normalPoly :
    CoordinateRing (R := R) →ₗ[R[X]] R[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic (R := R))

def coeff0 :
    CoordinateRing (R := R) →ₗ[R[X]] R[X] :=
  (Polynomial.lcoeff R[X] 0).comp (normalPoly (R := R))

def coeffY :
    CoordinateRing (R := R) →ₗ[R[X]] R[X] :=
  (Polynomial.lcoeff R[X] 1).comp (normalPoly (R := R))

private theorem curvePoly_degree [Nontrivial R] :
    (curvePoly : R[X][X]).degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X
    [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    xClass (coeff0 z) + xClass (coeffY z) * yClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass (coeff0 (mk g)) +
              xClass (coeffY (mk g)) * yClass =
            mk
              (C (coeff0 (mk g)) +
                C (coeffY (mk g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = mk (normalPoly (mk g)) := by
              rw [normalPoly_eq_C_add_C_mul_X]
        _ = mk g :=
          AdjoinRoot.mk_leftInverse curvePoly_monic (mk g)

@[simp] theorem coeff0_xClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)

@[simp] theorem coeffY_xClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)

@[simp] theorem coeff0_yClass [Nontrivial R] :
    coeff0 (yClass (R := R)) = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num

@[simp] theorem coeffY_yClass [Nontrivial R] :
    coeffY (yClass (R := R)) = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num

@[simp] theorem coeff0_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem coeffY_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = p
  rw [← Algebra.smul_def]
  simp

/-- Equality in the generalized affine coordinate ring is coefficientwise
with respect to the basis `1, Y` over `R[X]`. -/
theorem eq_iff_coeff [Nontrivial R]
    (z w : CoordinateRing (R := R)) :
    z = w ↔ coeff0 z = coeff0 w ∧ coeffY z = coeffY w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose z, ← recompose w, h0, hY]

/-- The generalized graph relation; no smoothness assumption is needed for
the evaluation-kernel and saturation theorems. -/
structure SemiMumford where
  u : R[X]
  v : R[X]
  w : R[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : R[X]) : R[X] :=
  -hPoly - v

def ySubClass (v : R[X]) : CoordinateRing (R := R) :=
  yClass - xClass v

def mumfordIdeal (u v : R[X]) :
    Ideal (CoordinateRing (R := R)) :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : R[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : R[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

@[simp] theorem yClass_relation :
    yClass (R := R) ^ 2 +
        xClass (R := R) (hPoly (R := R)) *
          yClass (R := R) =
      xClass (R := R) (rhsPoly (R := R)) := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

/-- The product of the two raw graph functions is the negative substituted
curve equation.  No divisibility or smoothness hypothesis is needed. -/
theorem ySubClass_mul_conjugateV_raw
    (v : R[X]) :
    ySubClass v * ySubClass (conjugateV v) =
      -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
  calc
    ySubClass v * ySubClass (conjugateV v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass v ^ 2 + xClass hPoly * xClass v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (v ^ 2 + hPoly * v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
      rw [xClass_sub]
      ring

/-- The two conjugate graph functions multiply to the negative Cantor
quotient.  This identity is valid integrally, before reduction modulo two. -/
theorem ySubClass_mul_conjugate
    (D : SemiMumford (R := R)) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) :=
      ySubClass_mul_conjugateV_raw D.v
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

/-- A smooth generalized Mumford graph and its hyperelliptic conjugate
multiply to the principal ideal `(u)`.  The only smoothness input is the
displayed Bézout identity, so the theorem works over an arbitrary
commutative base ring. -/
theorem mumfordIdeal_mul_conj_integral
    (D : SemiMumford (R := R))
    (hbez :
      ∃ a b c : R[X],
        a * D.u + b * (2 * D.v + hPoly) + c * D.w = 1) :
    mumfordIdeal D.u D.v *
        mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span
        ({xClass D.u} :
          Set (CoordinateRing (R := R))) := by
  let I := mumfordIdeal D.u D.v
  let J := mumfordIdeal D.u (conjugateV D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine ⟨p₀ * q₀ * xClass D.u +
        p₀ * qY * ySubClass (conjugateV D.v) +
        pY * q₀ * ySubClass D.v -
        pY * qY * xClass D.w, ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination pY * qY * ySubClass_mul_conjugate D
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, habc⟩ := hbez
    have huI : xClass D.u ∈ I :=
      xClass_mem_mumfordIdeal D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hvI : ySubClass D.v ∈ I :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hvJ : ySubClass (conjugateV D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv :
        xClass D.u * xClass (2 * D.v + hPoly) ∈ I * J := by
      have hp :
          xClass D.u * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [two_mul, ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add]
      ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass D.v * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b *
          (xClass D.u * xClass (2 * D.v + hPoly)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b *
              (xClass D.u * xClass (2 * D.v + hPoly)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + hPoly) + c * D.w) := by
          simp only [two_mul, xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [habc, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

abbrev MumfordResidue
    (D : SemiMumford (R := R)) : Type u :=
  R[X] ⧸ Ideal.span ({D.u} : Set R[X])

private theorem mumford_root_relation
    (D : SemiMumford (R := R)) :
    curvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v) = 0 := by
  change (X ^ 2 + C hPoly * X - C rhsPoly).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
    (D.v ^ 2 + hPoly * D.v - rhsPoly) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

def mumfordEval (D : SemiMumford (R := R)) :
    CoordinateRing (R := R) →+* MumfordResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v)
    (mumford_root_relation D)

@[simp] theorem mumfordEval_xClass
    (D : SemiMumford (R := R)) (p : R[X]) :
    mumfordEval D (xClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p := by
  change mumfordEval D (AdjoinRoot.of curvePoly p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation D)

@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)

@[simp] theorem mumfordEval_ySubClass
    (D : SemiMumford (R := R)) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker
    (D : SemiMumford (R := R)) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D

theorem ker_mumfordEval
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : R[X] := coeff0 z
    let q : R[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass D.u ∈ mumfordIdeal D.u D.v :=
      xClass_mem_mumfordIdeal D.u D.v
    have hyv : ySubClass D.v ∈ mumfordIdeal D.u D.v :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hbase : xClass (p + q * D.v) ∈
        mumfordIdeal D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass s) hu
    have hgraph : xClass q * ySubClass D.v ∈
        mumfordIdeal D.u D.v :=
      Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass q) hyv
    rw [← recompose z]
    have hdecomp :
        xClass p + xClass q * yClass =
          xClass (p + q * D.v) +
            xClass q * ySubClass D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker D

/-- Membership in a generalized Mumford graph ideal is the single monic
divisibility condition obtained by substituting `Y = v`. -/
theorem mem_mumfordIdeal_iff
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    z ∈ mumfordIdeal D.u D.v ↔
      D.u ∣ coeff0 z + coeffY z * D.v := by
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  conv_lhs =>
    rw [← recompose z]
  simp only [map_add, map_mul, mumfordEval_xClass,
    mumfordEval_yClass]
  change
    Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
        (coeff0 z + coeffY z * D.v) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem mumfordEval_surjective
    (D : SemiMumford (R := R)) :
    Function.Surjective (mumfordEval D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass p, mumfordEval_xClass D p⟩

noncomputable def mumfordQuotientEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))

/-- The graph quotient equivalence sends a quotient class to its graph
evaluation. -/
@[simp] theorem mumfordQuotientEquiv_apply_mk
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient algebra. -/
noncomputable def mumfordQuotientAlgEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[R]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set R[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

/-- A monic graph quotient is free over the base. -/
noncomputable instance mumfordResidueFree
    (D : SemiMumford (R := R)) :
    Module.Free R (MumfordResidue D) :=
  D.u_monic.free_quotient

/-- A generalized Mumford graph ideal is saturated with respect to every
nonzero scalar from a domain base. -/
theorem scalar_saturated
    [IsDomain R]
    (D : SemiMumford (R := R))
    (r : R) (hr : r ≠ 0)
    (z : CoordinateRing (R := R))
    (hz : xClass (C r) * z ∈ mumfordIdeal D.u D.v) :
    z ∈ mumfordIdeal D.u D.v := by
  have hker :
      xClass (C r) * z ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval]
    exact hz
  have hmap :
      mumfordEval D (xClass (C r) * z) = 0 :=
    hker
  have hscalar :
      r • mumfordEval D z =
        Ideal.Quotient.mk
          (Ideal.span ({D.u} : Set R[X])) (C r) *
            mumfordEval D z := by
    obtain ⟨p, hp⟩ :=
      Ideal.Quotient.mk_surjective (mumfordEval D z)
    rw [← hp]
    change
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (r • p) =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (C r) *
          Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p
    rw [Polynomial.smul_eq_C_mul]
    exact
      (Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))).map_mul (C r) p
  have hsmul : r • mumfordEval D z = 0 := by
    rw [hscalar]
    simpa only [map_mul, mumfordEval_xClass] using hmap
  have heval : mumfordEval D z = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hr
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  exact heval

namespace TwoAdic

abbrev R₂ : Type := ℤ_[2]

abbrev CoordinateRing₂ : Type :=
  CoordinateRing (R := R₂)

abbrev SemiMumford₂ : Type :=
  SemiMumford (R := R₂)

/-- In particular, integral graph ideals over `ℤ₂` are vertically
two-saturated. -/
theorem two_saturated
    (D : SemiMumford₂)
    (z : CoordinateRing₂)
    (hz :
      xClass (R := R₂) (C (2 : R₂)) * z ∈
        mumfordIdeal D.u D.v) :
    z ∈ mumfordIdeal D.u D.v :=
  scalar_saturated D 2 (by norm_num) z hz

end TwoAdic

end

end MazurProof.N13GeneralizedMumfordIntegral


