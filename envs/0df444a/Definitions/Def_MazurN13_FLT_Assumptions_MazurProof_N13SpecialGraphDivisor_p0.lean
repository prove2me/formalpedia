-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisor_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisor_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:09:32.779691+00:00
-- url     : https://prove2.me/theorems/aa5d76d6-fd40-4bd6-8753-d8d900a5e254
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialGraphDivisor source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialGraphDivisor

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialGraphDivisor
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuotientBasis_p0

set_option autoImplicit false




/-!
# Degree-two Mumford graphs as effective divisors on the N13 special fibre

A monic quadratic generalized Mumford graph on the good characteristic-two
model splits over `F₂`.  Indeed, an irreducible quadratic would produce an
affine point over its quadratic root field, while the structural Frobenius
classification forces that root back into `F₂`.

The two roots, with their graph values, therefore define an effective
degree-two divisor.  If that divisor is the selected nonspecial base divisor,
its two distinct points force `u = X² + X` and `u ∣ v`; hence its graph ideal
is literally the fixed special ideal.  No finite table or representative
enumeration is used.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialGraphDivisor

noncomputable section

open MazurProof.N13GoodCoordinateRingTwo

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem degreeTwo_splits
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    D.u.Splits := by
  by_contra hnot
  have hnoRoot (a : K) : D.u.eval a ≠ 0 := by
    intro ha
    exact hnot (Polynomial.Splits.of_natDegree_eq_two hdeg ha)
  have hroots : D.u.roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    exact hnoRoot a ((Polynomial.mem_roots D.u_monic.ne_zero).mp ha)
  have hirr : Irreducible D.u := by
    apply (D.u_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)).mpr
    exact hroots
  letI : Fact (Irreducible D.u) := ⟨hirr⟩
  letI : Module.Finite K (AdjoinRoot D.u) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  letI : Finite (AdjoinRoot D.u) :=
    Module.finite_of_finite K
  letI : Fintype (AdjoinRoot D.u) :=
    Fintype.ofFinite (AdjoinRoot D.u)
  letI : CharP (AdjoinRoot D.u) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (AdjoinRoot D.u)).injective 2
  have hcard : Fintype.card (AdjoinRoot D.u) = 4 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := AdjoinRoot D.u),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let alpha : AdjoinRoot D.u := AdjoinRoot.root D.u
  let beta : AdjoinRoot D.u := Polynomial.aeval alpha D.v
  have hfour (z : AdjoinRoot D.u) : z ^ 4 = z := by
    rw [← hcard]
    exact FiniteField.pow_card z
  have hroot : Polynomial.aeval alpha D.u = 0 := by
    simp [alpha, Polynomial.aeval_def, AdjoinRoot.eval₂_root]
  have hcurve :
      N13GoodModelTwo.AffineEquation alpha beta := by
    have hc := congrArg (Polynomial.aeval alpha) D.curve_eq
    simp only [map_sub, map_add, map_pow, map_mul] at hc
    rw [hroot, zero_mul] at hc
    change
      beta ^ 2 + N13GoodModelTwo.h alpha * beta =
        N13GoodModelTwo.rhs alpha
    simpa [beta, N13GoodModelTwo.h, N13GoodModelTwo.rhs,
      hPoly, rhsPoly, Polynomial.aeval_def] using sub_eq_zero.mp hc
  have halpha : alpha ^ 2 = alpha :=
    ((N13GoodModelTwo.affineEquation_iff_fixed hfour alpha beta).mp hcurve).1
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one alpha halpha with ha | ha
  · have hz : D.u.eval 0 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have hzmap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 0) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [ha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using hzmap
    exact hnoRoot 0 hz
  · have ho : D.u.eval 1 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have homap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 1) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 1) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 1) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [ha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using homap
    exact hnoRoot 1 ho

theorem exists_rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    ∃ z : Sym2 K, z.toMultiset = D.u.roots := by
  have hcard : D.u.roots.card = 2 := by
    rw [← (degreeTwo_splits D hdeg).natDegree_eq_card_roots]
    exact hdeg
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨s(a, b), ?_⟩
  change ({a, b} : Multiset K) = D.u.roots
  exact hab.symm

noncomputable def rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    Sym2 K :=
  Classical.choose (exists_rootPair D hdeg)

theorem rootPair_toMultiset
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    (rootPair D hdeg).toMultiset = D.u.roots := by
  exact Classical.choose_spec (exists_rootPair D hdeg)

theorem mem_rootPair_iff_isRoot
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) (a : K) :
    a ∈ rootPair D hdeg ↔ D.u.IsRoot a := by
  rw [← Sym2.mem_toMultiset, rootPair_toMultiset,
    Polynomial.mem_roots D.u_monic.ne_zero]

theorem curveEquationAtRoot
    (D : SemiMumford) {a : K} (ha : D.u.IsRoot a) :
    N13GoodModelTwo.AffineEquation a (D.v.eval a) := by
  have hc := congrArg (Polynomial.eval a) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at hc
  rw [ha, zero_mul] at hc
  change
    D.v.eval a ^ 2 +
        N13GoodModelTwo.h a * D.v.eval a =
      N13GoodModelTwo.rhs a
  simpa [N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    hPoly, rhsPoly] using sub_eq_zero.mp hc

noncomputable def rootPoint
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (a : K) (ha : a ∈ rootPair D hdeg) :
    N13AbelFiberTwoModel.CurvePoint :=
  Sum.inl
    ⟨(a, D.v.eval a),
      curveEquationAtRoot D ((mem_rootPair_iff_isRoot D hdeg a).mp ha)⟩

noncomputable def graphDivisor
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  Sym2.pmap (rootPoint D hdeg) (rootPair D hdeg)
    (fun _ ha => ha)

/-- Abel equality with the selected nonspecial divisor already forces
literal equality of effective divisors.  The only other degree-two Abel
fibre is the canonical pencil, and the selected base divisor is not in it. -/
theorem graphDivisor_eq_special_of_abel_eq
    {J : Type*}
    (G : N13AbelFiberTwoModel.GeometricAbelCriterion J)
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      G.abel (graphDivisor D hdeg) =
        G.abel N13AbelChartBase.specialBaseDivisor) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor := by
  rcases
      (G.eq_iff
        (graphDivisor D hdeg)
        N13AbelChartBase.specialBaseDivisor).mp habel with
    h | ⟨_, hbase⟩
  · exact h
  · exact
      (N13AbelChartBase.specialBaseDivisor_not_canonical hbase).elim

/-- The same rigidity statement in the canonical nineteen-element
set-valued Abel quotient. -/
theorem graphDivisor_eq_special_of_setAbel_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor :=
  graphDivisor_eq_special_of_abel_eq
    N13AbelFiberTwoModel.picTwoSetModelCriterion D hdeg habel

theorem zero_one_roots_and_values_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    D.u.IsRoot 0 ∧ D.u.IsRoot 1 ∧
      D.v.eval 0 = 0 ∧ D.v.eval 1 = 0 := by
  have hp00 :
      N13AbelChartBase.p00 ∈ graphDivisor D hdeg := by
    rw [hgraph]
    exact Sym2.mem_mk_left _ _
  have hp10 :
      N13AbelChartBase.p10 ∈ graphDivisor D hdeg := by
    rw [hgraph]
    exact Sym2.mem_mk_right _ _
  rw [graphDivisor, Sym2.mem_pmap_iff] at hp00 hp10
  obtain ⟨a, ha, hpa⟩ := hp00
  obtain ⟨b, hb, hpb⟩ := hp10
  have hca := congrArg N13AbelFiberTwoModel.curvePointEquiv hpa
  have hcb := congrArg N13AbelFiberTwoModel.curvePointEquiv hpb
  have ha0 : a = 0 := by
    symm
    simpa [N13AbelChartBase.p00, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.fst hca
  have hva0 : D.v.eval a = 0 := by
    symm
    simpa [N13AbelChartBase.p00, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.snd hca
  have hb1 : b = 1 := by
    symm
    simpa [N13AbelChartBase.p10, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.fst hcb
  have hvb0 : D.v.eval b = 0 := by
    symm
    simpa [N13AbelChartBase.p10, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.snd hcb
  subst a
  subst b
  exact
    ⟨(mem_rootPair_iff_isRoot D hdeg 0).mp ha,
      (mem_rootPair_iff_isRoot D hdeg 1).mp hb,
      hva0, hvb0⟩

theorem u_eq_base_and_dvd_v_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by
  obtain ⟨hu0, hu1, hv0, hv1⟩ :=
    zero_one_roots_and_values_of_graphDivisor_eq D hdeg hgraph
  have htwo : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have hunit : IsUnit ((0 : K) - 1) := by
    have hnegOne : (-1 : K) = 1 := by
      change (-1 : ZMod 2) = 1
      decide
    rw [zero_sub, hnegOne]
    exact isUnit_one
  have hcop :
      IsCoprime (X - C (0 : K)) (X - C (1 : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub hunit
  have hfactor :
      (X - C (0 : K)) * (X - C (1 : K)) =
        (X ^ 2 + X : K[X]) := by
    simp only [map_zero, sub_zero, map_one]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hsum : (X : K[X]) + X = 0 := by
      calc
        (X : K[X]) + X = 2 * X := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    have hnegX : -(X : K[X]) = X := by
      calc
        -(X : K[X]) = -X + (X + X) := by rw [hsum, add_zero]
        _ = X := by ring
    calc
      (X : K[X]) * (X - 1) = X ^ 2 - X := by ring
      _ = X ^ 2 + X := by simp [sub_eq_add_neg, hnegX]
  have hprod_u :
      (X - C (0 : K)) * (X - C (1 : K)) ∣ D.u :=
    hcop.mul_dvd
      (Polynomial.dvd_iff_isRoot.mpr hu0)
      (Polynomial.dvd_iff_isRoot.mpr hu1)
  have hu :
      (X - C (0 : K)) * (X - C (1 : K)) = D.u := by
    have hpdeg :
        ((X - C (0 : K)) * (X - C (1 : K))).natDegree = 2 := by
      rw [natDegree_mul
        (monic_X_sub_C (0 : K)).ne_zero
        (monic_X_sub_C (1 : K)).ne_zero]
      rw [natDegree_X_sub_C, natDegree_X_sub_C]
    apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hprod_u
    · rw [hdeg, hpdeg]
    · rw [((monic_X_sub_C (0 : K)).mul
          (monic_X_sub_C (1 : K))).leadingCoeff,
        D.u_monic.leadingCoeff]
  have hprod_v :
      (X - C (0 : K)) * (X - C (1 : K)) ∣ D.v :=
    hcop.mul_dvd
      (Polynomial.dvd_iff_isRoot.mpr hv0)
      (Polynomial.dvd_iff_isRoot.mpr hv1)
  constructor
  · rw [← hu]
    exact hfactor
  · rw [← hu]
    exact hprod_v

/-- Literal equality with the selected special graph ideal already recovers
the monic quadratic and the graph value modulo it.  This is the converse
representative statement to `mumfordIdeal_eq_special_of_graphDivisor_eq`. -/
theorem u_eq_base_and_dvd_v_of_mumfordIdeal_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hideal :
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal) :
    D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by
  have hxmem :
      xClass N13SpecialQuotientBasis.specialData.u ∈
        mumfordIdeal D.u D.v := by
    rw [hideal]
    exact
      xClass_mem_mumfordIdeal
        N13SpecialQuotientBasis.specialData.u
        N13SpecialQuotientBasis.specialData.v
  have hxker :
      xClass N13SpecialQuotientBasis.specialData.u ∈
        RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval D]
    exact hxmem
  have hxzero :=
    RingHom.mem_ker.mp hxker
  rw [mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hxzero
  have hueq :
      D.u = (X ^ 2 + X : K[X]) := by
    have hspecial :
        N13SpecialQuotientBasis.specialData.u = D.u :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        D.u_monic
        N13SpecialQuotientBasis.specialData.u_monic
        hxzero
        (by
          rw [hdeg,
            N13SpecialQuotientBasis.specialData_u_natDegree])
    simpa only [N13SpecialQuotientBasis.specialData_u] using hspecial.symm
  have hymem :
      yClass ∈ mumfordIdeal D.u D.v := by
    rw [hideal]
    change
      yClass ∈
        mumfordIdeal
          N13SpecialQuotientBasis.specialData.u
          N13SpecialQuotientBasis.specialData.v
    simpa only [N13SpecialQuotientBasis.specialData_v,
      ySubClass, xClass_zero, sub_zero] using
      ySubClass_mem_mumfordIdeal
        N13SpecialQuotientBasis.specialData.u
        N13SpecialQuotientBasis.specialData.v
  have hyker :
      yClass ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval D]
    exact hymem
  have hyzero :=
    RingHom.mem_ker.mp hyker
  rw [mumfordEval_yClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hyzero
  exact ⟨hueq, hyzero⟩

/-- The literal special graph ideal determines the selected effective
divisor.  The proof recovers the two roots and evaluates the graph there;
it does not enumerate the special curve. -/
theorem graphDivisor_eq_special_of_mumfordIdeal_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hideal :
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor := by
  obtain ⟨hu, hv⟩ :=
    u_eq_base_and_dvd_v_of_mumfordIdeal_eq D hdeg hideal
  have hr0 : D.u.IsRoot 0 := by
    simp [hu]
  have hr1 : D.u.IsRoot 1 := by
    change D.u.eval 1 = 0
    rw [hu]
    norm_num
    exact CharP.cast_eq_zero K 2
  have hmem0 :
      (0 : K) ∈ rootPair D hdeg :=
    (mem_rootPair_iff_isRoot D hdeg 0).2 hr0
  have hmem1 :
      (1 : K) ∈ rootPair D hdeg :=
    (mem_rootPair_iff_isRoot D hdeg 1).2 hr1
  obtain ⟨q, hq⟩ := hv
  have hv0 : D.v.eval 0 = 0 := by
    rw [hq, eval_mul, hr0, zero_mul]
  have hv1 : D.v.eval 1 = 0 := by
    rw [hq, eval_mul, hr1, zero_mul]
  have hp00 :
      N13AbelChartBase.p00 ∈ graphDivisor D hdeg := by
    rw [graphDivisor, Sym2.mem_pmap_iff]
    refine ⟨0, hmem0, ?_⟩
    simp [rootPoint, N13AbelChartBase.p00,
      N13AbelFiberTwoModel.curvePointEquiv, hv0]
  have hp10 :
      N13AbelChartBase.p10 ∈ graphDivisor D hdeg := by
    rw [graphDivisor, Sym2.mem_pmap_iff]
    refine ⟨1, hmem1, ?_⟩
    simp [rootPoint, N13AbelChartBase.p10,
      N13AbelFiberTwoModel.curvePointEquiv, hv1]
  have hpne :
      N13AbelChartBase.p00 ≠ N13AbelChartBase.p10 := by
    intro h
    have h' :=
      congrArg N13AbelFiberTwoModel.curvePointEquiv h
    simp [N13AbelChartBase.p00,
      N13AbelChartBase.p10] at h'
  simpa [N13AbelChartBase.specialBaseDivisor] using
    (Sym2.mem_and_mem_iff hpne).mp ⟨hp00, hp10⟩

theorem mumfordIdeal_eq_zero_of_dvd
    (u v : K[X]) (h : u ∣ v) :
    mumfordIdeal u v = mumfordIdeal u 0 := by
  obtain ⟨q, hq⟩ := h
  have hmultiple :
      xClass v ∈ mumfordIdeal u 0 := by
    rw [hq, xClass_mul, mul_comm]
    exact Ideal.mul_mem_left _ (xClass q)
      (xClass_mem_mumfordIdeal u 0)
  have hmultiple' :
      xClass v ∈ mumfordIdeal u v := by
    have hx : xClass v = xClass u * xClass q := by
      rw [hq, xClass_mul]
    rw [hx]
    simpa only [mul_comm] using
      Ideal.mul_mem_left _ (xClass q)
        (xClass_mem_mumfordIdeal u v)
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal u 0
    · have heq : ySubClass v = ySubClass 0 - xClass v := by
        simp [ySubClass]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal u 0) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal u v
    · have heq : ySubClass 0 = ySubClass v + xClass v := by
        simp [ySubClass]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal u v) hmultiple'

theorem mumfordIdeal_eq_special_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal := by
  obtain ⟨hu, hv⟩ :=
    u_eq_base_and_dvd_v_of_graphDivisor_eq D hdeg hgraph
  calc
    mumfordIdeal D.u D.v = mumfordIdeal D.u 0 :=
      mumfordIdeal_eq_zero_of_dvd D.u D.v hv
    _ = N13SpecialQuotientBasis.specialIdeal := by
      simp [N13SpecialQuotientBasis.specialIdeal,
        N13SpecialQuotientBasis.specialData_u,
        N13SpecialQuotientBasis.specialData_v, hu]

/-- The complete special-fibre bridge: an Abel-compatible quadratic
Mumford graph has the fixed literal graph ideal. -/
theorem mumfordIdeal_eq_special_of_abel_eq
    {J : Type*}
    (G : N13AbelFiberTwoModel.GeometricAbelCriterion J)
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      G.abel (graphDivisor D hdeg) =
        G.abel N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal :=
  mumfordIdeal_eq_special_of_graphDivisor_eq D hdeg
    (graphDivisor_eq_special_of_abel_eq G D hdeg habel)

/-- Set-valued Abel compatibility is already enough to identify the fixed
special graph ideal. -/
theorem mumfordIdeal_eq_special_of_setAbel_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal :=
  mumfordIdeal_eq_special_of_abel_eq
    N13AbelFiberTwoModel.picTwoSetModelCriterion D hdeg habel

/-- For quadratic special graphs, the intrinsic Abel class and the literal
graph ideal carry exactly the same information at the selected regular
class. -/
theorem setAbel_eq_iff_mumfordIdeal_eq_special
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor ↔
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal := by
  constructor
  · exact mumfordIdeal_eq_special_of_setAbel_eq D hdeg
  · intro hideal
    exact congrArg N13AbelFiberTwoModel.abel
      (graphDivisor_eq_special_of_mumfordIdeal_eq
        D hdeg hideal)

end

end MazurProof.N13SpecialGraphDivisor


