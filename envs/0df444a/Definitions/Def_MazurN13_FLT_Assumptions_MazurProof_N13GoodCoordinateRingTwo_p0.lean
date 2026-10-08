-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodCoordinateRingTwo_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodCoordinateRingTwo_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:52:29.948099+00:00
-- url     : https://prove2.me/theorems/70454182-e8ed-404a-9882-485354faf7c3
-- title:
--   FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
import Mathlib.RingTheory.FractionalIdeal.Inverse

set_option autoImplicit false




/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.N13GoodCoordinateRingTwo

noncomputable section

abbrev K := N13GoodModelTwo.F2

/-- The coefficient of `Y` in polynomial form. -/
def hPoly : K[X] :=
  X ^ 3 + X + 1

/-- The right-hand side in polynomial form. -/
def rhsPoly : K[X] :=
  X ^ 5 + X ^ 4

/-- The outer variable is `Y`, with coefficients in `F₂[X]`. -/
def curvePoly : K[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem hPoly_monic : hPoly.Monic := by
  unfold hPoly
  (monicity; norm_num)

theorem hPoly_natDegree : hPoly.natDegree = 3 := by
  unfold hPoly
  (compute_degree; norm_num)

theorem rhsPoly_monic : rhsPoly.Monic := by
  unfold rhsPoly
  monicity <;> norm_num

theorem rhsPoly_natDegree : rhsPoly.natDegree = 5 := by
  unfold rhsPoly
  compute_degree <;> norm_num

theorem curvePoly_monic : curvePoly.Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree : curvePoly.natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

private theorem zmod_two_nonzero_eq_one (z : K) (hz : z ≠ 0) :
    z = 1 := by
  simpa [K] using ZMod.pow_card_sub_one_eq_one hz

private theorem artinSchreier_degree_le_three
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    q.natDegree ≤ 3 := by
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    have : (rhsPoly : K[X]) = 0 := by simpa using heq.symm
    exact rhsPoly_monic.ne_zero this
  by_contra hdeg
  have h4 : 4 ≤ q.natDegree := by omega
  have hlt :
      (hPoly * q).natDegree < (q ^ 2).natDegree := by
    rw [natDegree_mul hPoly_monic.ne_zero hq0, hPoly_natDegree,
      natDegree_pow]
    omega
  have hsum :
      (q ^ 2 + hPoly * q).natDegree = (q ^ 2).natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  rw [heq, rhsPoly_natDegree, natDegree_pow] at hsum
  omega

private theorem artinSchreier_reduce_degree
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    ∃ r : K[X],
      r.natDegree ≤ 2 ∧
      r ^ 2 + hPoly * r = rhsPoly := by
  have hdeg := artinSchreier_degree_le_three q heq
  by_cases hq3 : q.natDegree = 3
  · have hq0 : q ≠ 0 := by
      intro hq
      subst q
      norm_num at hq3
    have hlead : q.leadingCoeff = 1 :=
      zmod_two_nonzero_eq_one q.leadingCoeff
        (leadingCoeff_ne_zero.mpr hq0)
    have hqMonic : q.Monic := hlead
    have hqDegree : IsMonicOfDegree q 3 := ⟨hq3, hqMonic⟩
    have hhDegree : IsMonicOfDegree hPoly 3 :=
      ⟨hPoly_natDegree, hPoly_monic⟩
    refine ⟨q - hPoly, ?_, ?_⟩
    · have hlt :
          (q - hPoly).natDegree < 3 :=
        hqDegree.natDegree_sub_lt (n := 3) (by norm_num) hhDegree
      omega
    · have htwo : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      calc
        (q - hPoly) ^ 2 + hPoly * (q - hPoly) =
            q ^ 2 + hPoly * q - 2 * (q * hPoly) := by ring
        _ = q ^ 2 + hPoly * q := by rw [htwo, zero_mul, sub_zero]
        _ = rhsPoly := heq
  · refine ⟨q, ?_, heq⟩
    omega

private theorem no_artinSchreier_polynomial_root
    (q : K[X]) :
    q ^ 2 + hPoly * q ≠ rhsPoly := by
  intro heq
  obtain ⟨r, hrdeg, hre⟩ := artinSchreier_reduce_degree q heq
  have hr :
      r =
        C (r.coeff 2) * X ^ 2 +
          C (r.coeff 1) * X +
            C (r.coeff 0) := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    by_cases hn2 : n = 2
    · subst n
      simp
    have hn : 2 < n := by omega
    have hrzero : r.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hrdeg.trans_lt hn)
    have h1n : 1 ≠ n := by omega
    rw [hrzero]
    simp [coeff_X, coeff_C, hn0, h1n, hn2]
  rw [hr] at hre
  simp only [hPoly, rhsPoly] at hre
  ring_nf at hre
  have hcoeffFive :=
    congrArg (fun p : K[X] => p.coeff 5) hre
  have hcoeffTwo :=
    congrArg (fun p : K[X] => p.coeff 2) hre
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  simp only [← C_pow] at hcoeffFive hcoeffTwo
  simp [coeff_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, htwoK] at hcoeffFive hcoeffTwo
  have hbb : r.coeff 1 + r.coeff 1 = 0 := by
    rw [← two_mul, htwoK, zero_mul]
  have hzero : r.coeff 2 = 0 := by
    linear_combination hcoeffTwo - hbb
  rw [hzero] at hcoeffFive
  exact zero_ne_one hcoeffFive

private theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot curvePoly q := by
  intro hq
  have heq :
      q ^ 2 + hPoly * q = rhsPoly := by
    have hzero :
        q ^ 2 + hPoly * q - rhsPoly = 0 := by
      simpa only [IsRoot.def, curvePoly, eval_sub, eval_add, eval_pow,
        eval_X, eval_C, eval_mul] using hq
    exact sub_eq_zero.mp hzero
  exact no_artinSchreier_polynomial_root q heq

theorem curvePoly_irreducible : Irreducible curvePoly := by
  rw [curvePoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot q
      ((mem_roots curvePoly_monic.ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩

/-- The affine coordinate ring of the special fibre. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot curvePoly

/-- Its fraction field. -/
abbrev FunctionField : Type :=
  FractionRing CoordinateRing

instance instIsDomainCoordinateRing : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime

noncomputable instance instAlgebraKCoordinateRing : Algebra K CoordinateRing :=
  inferInstance

noncomputable instance instAlgebraPolynomialKCoordinateRing : Algebra K[X] CoordinateRing :=
  inferInstance

/-- Quotient map to the affine coordinate ring. -/
def mk : K[X][X] →+* CoordinateRing :=
  AdjoinRoot.mk curvePoly

/-- Embed a polynomial in the `X` coordinate. -/
def xClass (p : K[X]) : CoordinateRing :=
  mk (C p)

/-- The class of the `Y` coordinate. -/
def yClass : CoordinateRing :=
  mk X

/-- The polynomial-coordinate embedding. -/
def xClassHom : K[X] →+* CoordinateRing :=
  AdjoinRoot.of curvePoly

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass 0 = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass 1 = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : K[X]) = (n : CoordinateRing) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

/-- The canonical degree-less-than-two polynomial representative. -/
def normalPoly : CoordinateRing →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom curvePoly_monic

/-- Constant coefficient in the `1,Y` basis. -/
def coeff0 : CoordinateRing →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp normalPoly

/-- `Y` coefficient in the `1,Y` basis. -/
def coeffY : CoordinateRing →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp normalPoly

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly (mk g) = g %ₘ curvePoly := rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 (mk g) = (g %ₘ curvePoly).coeff 0 := rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY (mk g) = (g %ₘ curvePoly).coeff 1 := rfl

private theorem curvePoly_degree : curvePoly.degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing) :
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

/-- Every coordinate-ring element has a unique rank-two expression. -/
theorem recompose (z : CoordinateRing) :
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

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)

@[simp] theorem coeff0_yClass :
    coeff0 yClass = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num

@[simp] theorem coeffY_yClass :
    coeffY yClass = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num

@[simp] theorem coeff0_xClass_mul_yClass (p : K[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0 ((algebraMap K[X] CoordinateRing p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem coeffY_xClass_mul_yClass (p : K[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY ((algebraMap K[X] CoordinateRing p) * yClass) = p
  rw [← Algebra.smul_def]
  simp

/-- Equality in the special-fibre coordinate ring is coefficientwise in
the rank-two basis `1,Y`. -/
theorem eq_iff_coeff (z w : CoordinateRing) :
    z = w ↔ coeff0 z = coeff0 w ∧ coeffY z = coeffY w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose z, ← recompose w, h0, hY]

@[simp] theorem yClass_relation :
    yClass ^ 2 + xClass hPoly * yClass = xClass rhsPoly := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt curvePoly_monic
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Generalized Mumford graph ideals -/

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : K[X]) : K[X] :=
  -hPoly - v

/-- Integral generalized Mumford data, including the Cantor quotient and
the precise smoothness Bézout identity needed for ideal invertibility. -/
structure SemiMumford where
  u : K[X]
  v : K[X]
  w : K[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w
  bezout :
    ∃ a b c : K[X],
      a * u + b * (2 * v + hPoly) + c * w = 1

/-- The graph function `Y-v(X)`. -/
def ySubClass (v : K[X]) : CoordinateRing :=
  yClass - xClass v

/-- The integral graph ideal `(u,Y-v)`. -/
def mumfordIdeal (u v : K[X]) : Ideal CoordinateRing :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

/-! ## Evaluation at a generalized Mumford graph -/

abbrev MumfordResidue (D : SemiMumford) : Type :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

private theorem mumford_root_relation (D : SemiMumford) :
    curvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 + C hPoly * X - C rhsPoly).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 + hPoly * D.v - rhsPoly) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

/-- Evaluation `X ↦ X mod u`, `Y ↦ v mod u`. -/
def mumfordEval (D : SemiMumford) :
    CoordinateRing →+* MumfordResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation D)

@[simp] theorem mumfordEval_xClass
    (D : SemiMumford) (p : K[X]) :
    mumfordEval D (xClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval D (AdjoinRoot.of curvePoly p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D

/-- The generalized Mumford graph ideal is exactly the evaluation kernel. -/
theorem ker_mumfordEval (D : SemiMumford) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 z
    let q : K[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set K[X]))
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

theorem mumfordEval_surjective (D : SemiMumford) :
    Function.Surjective (mumfordEval D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass p, mumfordEval_xClass D p⟩

/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))

@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford) (z : CoordinateRing) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[K]
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
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

/-- The two graph generators multiply to the negative Cantor quotient. -/
theorem ySubClass_mul_conjugate (D : SemiMumford) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass D.v ^ 2 + xClass hPoly * xClass D.v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (D.v ^ 2 + hPoly * D.v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) := by
      rw [xClass_sub]
      ring
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

/-- The characteristic-two generalized graph ideal satisfies
`(u,Y-v)(u,Y+h+v)=(u)`. -/
theorem mumfordIdeal_mul_conj_integral (D : SemiMumford) :
    mumfordIdeal D.u D.v * mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span ({xClass D.u} : Set CoordinateRing) := by
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
    obtain ⟨a, b, c, hbez⟩ := D.bezout
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
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add, xClass_mul]
      have htwoPoly : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      have htwoCoord : (2 : CoordinateRing) = 0 := by
        calc
          (2 : CoordinateRing) = xClass (2 : K[X]) :=
            (xClass_natCast 2).symm
          _ = xClass 0 := by rw [htwoPoly]
          _ = 0 := xClass_zero
      rw [htwoPoly, xClass_zero, zero_mul, zero_add]
      have hvadd : xClass D.v + xClass D.v = 0 := by
        rw [← two_mul, htwoCoord, zero_mul]
      calc
        xClass D.u * xClass hPoly =
            xClass D.u * xClass hPoly +
              xClass D.u * (xClass D.v + xClass D.v) := by
          rw [hvadd, mul_zero, add_zero]
        _ = xClass D.u *
              (yClass - (-xClass hPoly - xClass D.v)) -
            (yClass - xClass D.v) * xClass D.u := by ring
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
          simp only [xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford) :
    (mumfordIdeal D.u D.v :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) =
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

/-- Invertible fractional ideals of the special affine coordinate ring. -/
abbrev InvFrac :=
  (FractionalIdeal CoordinateRing⁰ FunctionField)ˣ

/-- A generalized Mumford graph ideal as a unit fractional ideal. -/
def mumfordIdealUnit (D : SemiMumford) : InvFrac :=
  Units.mkOfMulEqOne
    (mumfordIdeal D.u D.v :
      FractionalIdeal CoordinateRing⁰ FunctionField)
    ((mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField)⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        FunctionField (xClass_ne_zero D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford) :
    (mumfordIdealUnit D :
      FractionalIdeal CoordinateRing⁰ FunctionField) =
      mumfordIdeal D.u D.v := rfl

end

end MazurProof.N13GoodCoordinateRingTwo


