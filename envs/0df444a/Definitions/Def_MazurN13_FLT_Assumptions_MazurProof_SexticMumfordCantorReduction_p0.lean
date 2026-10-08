-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordCantorReduction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordCantorReduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:04:31.178974+00:00
-- url     : https://prove2.me/theorems/b7b421e7-56f3-4172-bc35-f2464170ae31
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordCantorReduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordCantorReduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordCantorReduction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordRepresentative_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdealConjugation_p0

set_option autoImplicit false




/-!
# One-step Cantor reduction for a monic sextic

This file isolates the structural algebra used by a well-founded Cantor
reduction.  It contains no enumeration and no Riemann--Roch input.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K)

local instance instDecidableEq_fLT : DecidableEq K := Classical.decEq K

/-! ## Changing the graph polynomial modulo `u` -/

/-- Replacing `v` by a congruent polynomial modulo `u` does not change the
Mumford ideal. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v V : K[X]) (h : u ∣ V - v) :
    mumfordIdeal M u V = mumfordIdeal M u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u v
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u v := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u v)
      have heq :
          ySubClass M V =
            ySubClass M v - xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal M u v) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u V
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u V := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u V)
      have heq :
          ySubClass M v =
            ySubClass M V + xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal M u V) hmultiple

theorem mumfordIdeal_add_mul
    (u v t : K[X]) :
    mumfordIdeal M u (v + u * t) = mumfordIdeal M u v := by
  apply mumfordIdeal_eq_of_dvd_sub
  refine ⟨t, ?_⟩
  ring

/-- Multiplying the first generator by a polynomial unit does not change a
Mumford ideal.  The divisibility formulation avoids choosing that unit. -/
theorem mumfordIdeal_eq_of_dvd_dvd
    (u u' v : K[X]) (huu' : u ∣ u') (hu'u : u' ∣ u) :
    mumfordIdeal M u v = mumfordIdeal M u' v := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := hu'u
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u' v)
    · exact ySubClass_mem_mumfordIdeal M u' v
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := huu'
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u v)
    · exact ySubClass_mem_mumfordIdeal M u v

theorem mumfordIdeal_normalize
    (u v : K[X]) :
    mumfordIdeal M (normalize u) v = mumfordIdeal M u v := by
  exact mumfordIdeal_eq_of_dvd_dvd M (normalize u) u v
    (associated_normalize u).symm.dvd
    (associated_normalize u).dvd

/-! ## The Cantor product identity -/

/-- The ideal product at the heart of one Cantor reduction step.

The Bezout condition is exactly the one supplied by `mumford_bezout` for
the semireduced pair `(u,V)` when `w = (f-V²)/u`. -/
theorem mumfordIdeal_mul_cantor
    (u w V : K[X])
    (hcurve : M.f - V ^ 2 = u * w)
    (hbezout :
      ∃ a b c : K[X],
        a * u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M u V * mumfordIdeal M w V =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M u V
  let J := mumfordIdeal M w V
  let g := ySubClass M V
  apply le_antisymm
  · rw [mumfordIdeal, mumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have hfactor :
          xClass M u * xClass M w =
            ySubClass M V * (yClass M + xClass M V) := by
        symm
        calc
          ySubClass M V * (yClass M + xClass M V) =
              xClass M (M.f - V ^ 2) := by
            simp only [ySubClass]
            calc
              (yClass M - xClass M V) *
                  (yClass M + xClass M V) =
                  yClass M ^ 2 - xClass M V ^ 2 := by ring
              _ = xClass M M.f - xClass M V ^ 2 := by
                rw [yClass_sq]
              _ = xClass M (M.f - V ^ 2) := by
                rw [xClass_sub, xClass_pow]
          _ = xClass M (u * w) := by rw [hcurve]
          _ = xClass M u * xClass M w := by rw [xClass_mul]
      rw [hfactor]
      exact Ideal.mul_mem_right (yClass M + xClass M V) _
        (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (xClass M u) (Ideal.subset_span (Set.mem_singleton _))
    · rw [mul_comm]
      exact Ideal.mul_mem_left _
        (xClass M w) (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (ySubClass M V) (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := hbezout
    have huI : xClass M u ∈ I :=
      xClass_mem_mumfordIdeal M u V
    have hwJ : xClass M w ∈ J :=
      xClass_mem_mumfordIdeal M w V
    have hgI : g ∈ I :=
      ySubClass_mem_mumfordIdeal M u V
    have hgJ : g ∈ J :=
      ySubClass_mem_mumfordIdeal M w V
    have hug : xClass M u * g ∈ I * J :=
      Ideal.mul_mem_mul huI hgJ
    have hgw : g * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul hgI hwJ
    have hgg : g * g ∈ I * J :=
      Ideal.mul_mem_mul hgI hgJ
    have huw : xClass M u * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul huI hwJ
    have htwoVg : xClass M (2 * V) * g ∈ I * J := by
      have hdifference := Ideal.sub_mem (I * J) huw hgg
      convert hdifference using 1
      change
        xClass M (2 * V) * ySubClass M V =
          xClass M u * xClass M w -
            ySubClass M V * ySubClass M V
      have hxTwo :
          xClass M (2 : K[X]) = (2 : CoordinateRing M) := by
        exact map_natCast (xClassHom M) 2
      calc
        xClass M (2 * V) * ySubClass M V =
            xClass M (M.f - V ^ 2) -
              ySubClass M V ^ 2 := by
          simp only [ySubClass]
          rw [show xClass M (M.f - V ^ 2) =
            yClass M ^ 2 - xClass M V ^ 2 by
              rw [yClass_sq, xClass_sub, xClass_pow]]
          simp only [xClass_mul]
          rw [hxTwo]
          ring
        _ = xClass M (u * w) -
              ySubClass M V ^ 2 := by rw [hcurve]
        _ = xClass M u * xClass M w -
              ySubClass M V * ySubClass M V := by
          rw [xClass_mul, pow_two]
    have ha : xClass M a * (xClass M u * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M a) hug
    have hb : xClass M b * (xClass M (2 * V) * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M b) htwoVg
    have hc : xClass M c * (g * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M c) hgw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M u * g) +
            xClass M b * (xClass M (2 * V) * g) +
            xClass M c * (g * xClass M w) = g := by
      calc
        _ = xClass M
              (a * u + b * (2 * V) + c * w) * g := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = g := by rw [hbez, xClass_one, one_mul]
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_cantor_of_semi
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w) :
    mumfordIdeal M D.u D.v * mumfordIdeal M w D.v =
      Ideal.span ({ySubClass M D.v} : Set (CoordinateRing M)) := by
  obtain ⟨w', a, b, c, hw', hbez⟩ := mumford_bezout M D
  have hwEq : w' = w := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    exact hw'.symm.trans hcurve
  subst w'
  exact mumfordIdeal_mul_cantor M D.u w D.v hcurve
    ⟨a, b, c, hbez⟩

/-- Bezout transvection for the graph change `v ↦ v + u t`.  It is the
algebraic reason that the cubic boundary step needs no new coprimality
argument. -/
theorem cantorBezout_add_mul
    (D : SemiMumford M) (t w : K[X])
    (hcurve :
      M.f - (D.v + D.u * t) ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * (D.v + D.u * t)) + c * w = 1 := by
  obtain ⟨w₀, a, b, c, hw₀, hbez⟩ := mumford_bezout M D
  have hwEq :
      w₀ = w + 2 * D.v * t + D.u * t ^ 2 := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    calc
      D.u * w₀ = M.f - D.v ^ 2 := hw₀.symm
      _ = (M.f - (D.v + D.u * t) ^ 2) +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by ring
      _ = D.u * w +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by rw [hcurve]
      _ = D.u * (w + 2 * D.v * t + D.u * t ^ 2) := by ring
  refine ⟨a - 2 * b * t - c * t ^ 2, b + c * t, c, ?_⟩
  rw [hwEq] at hbez
  linear_combination hbez

theorem mumfordIdeal_mul_cantor_add_mul
    (D : SemiMumford M) (t w : K[X])
    (hcurve :
      M.f - (D.v + D.u * t) ^ 2 = D.u * w) :
    mumfordIdeal M D.u D.v *
        mumfordIdeal M w (D.v + D.u * t) =
      Ideal.span
        ({ySubClass M (D.v + D.u * t)} :
          Set (CoordinateRing M)) := by
  rw [← mumfordIdeal_add_mul M D.u D.v t]
  exact mumfordIdeal_mul_cantor M D.u w
    (D.v + D.u * t) hcurve
    (cantorBezout_add_mul M D t w hcurve)

/-! ## Degree descent -/

/-- A factor in `f - V² = u w` cannot vanish. -/
theorem cantorFactor_ne_zero
    (u V w : K[X]) (hcurve : M.f - V ^ 2 = u * w) :
    w ≠ 0 := by
  intro hw
  have hsub : M.f - V ^ 2 = 0 := by
    simpa [hw] using hcurve
  have hsq : V ^ 2 = M.f := (sub_eq_zero.mp hsub).symm
  have hVunit : IsUnit V := by
    apply M.squarefree V
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hVunit.pow 2
  exact M.not_isUnit hfunit

/-- Above genus two, the quotient in a Cantor step has strictly smaller
degree than the old monic denominator. -/
theorem cantorFactor_natDegree_lt
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w)
    (hdeg : 3 < D.u.natDegree) :
    w.natDegree < D.u.natDegree := by
  have hw : w ≠ 0 := cantorFactor_ne_zero M D.u D.v w hcurve
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree : D.v.natDegree < D.u.natDegree := by
    by_cases hv : D.v = 0
    · rw [hv]
      simp
      omega
    · exact natDegree_lt_natDegree hv hvDegree
  have hnum :
      (M.f - D.v ^ 2).natDegree ≤
        max 6 (2 * D.v.natDegree) := by
    calc
      (M.f - D.v ^ 2).natDegree ≤
          max M.f.natDegree (D.v ^ 2).natDegree :=
        natDegree_sub_le _ _
      _ = max 6 (2 * D.v.natDegree) := by
        rw [M.natDegree, natDegree_pow]
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - D.v ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  have hbound :
      max 6 (2 * D.v.natDegree) <
        2 * D.u.natDegree := by
    rw [Nat.max_lt]
    omega
  omega

/-- In the cubic boundary case one replaces `v` by `v + u`.  The leading
terms of `f` and `(v+u)²` then cancel, so the quotient has degree at most
two. -/
theorem cubicCantorFactor
    (D : SemiMumford M) (w : K[X])
    (hdeg : D.u.natDegree = 3)
    (hcurve :
      M.f - (D.v + D.u) ^ 2 = D.u * w) :
    w ≠ 0 ∧ w.natDegree ≤ 2 := by
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hVMonic : (D.v + D.u).Monic :=
    D.u_monic.add_of_right hvDegree
  have hVNatDegree : (D.v + D.u).natDegree = 3 := by
    rw [natDegree_add_eq_right_of_degree_lt hvDegree, hdeg]
  have hf : IsMonicOfDegree M.f 6 :=
    ⟨M.natDegree, M.monic⟩
  have hV : IsMonicOfDegree (D.v + D.u) 3 :=
    ⟨hVNatDegree, hVMonic⟩
  have hV2 : IsMonicOfDegree ((D.v + D.u) ^ 2) 6 := by
    simpa using hV.pow 2
  have hnum :
      (M.f - (D.v + D.u) ^ 2).natDegree < 6 :=
    hf.natDegree_sub_lt (by norm_num) hV2
  have hw : w ≠ 0 :=
    cantorFactor_ne_zero M D.u (D.v + D.u) w hcurve
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - (D.v + D.u) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  constructor
  · exact hw
  · omega

/-! ## The normalized next semirepresentative -/

private theorem normalize_dvd_sub_mod
    (p q : K[X]) :
    normalize q ∣ p - p % normalize q := by
  refine ⟨p / normalize q, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p (normalize q)
  calc
    p - p % normalize q =
        (p % normalize q + normalize q * (p / normalize q)) -
          p % normalize q := by
      rw [hdiv]
    _ = normalize q * (p / normalize q) := by ring

/-- Normalize the quotient and reduce the complementary graph polynomial.
This is the inverse affine class; the actual Cantor successor is its
hyperelliptic conjugate below. -/
def cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w)
    (hw : w ≠ 0) :
    SemiMumford M where
  u := normalize w
  v := V % normalize w
  nInf := n
  u_monic := monic_normalize hw
  v_reduced := by
    apply (mod_eq_self_iff (monic_normalize hw).ne_zero).mpr
    exact degree_mod_lt _ (monic_normalize hw).ne_zero
  curve_dvd := by
    have hnW : normalize w ∣ w :=
      (associated_normalize w).symm.dvd
    have hnBase : normalize w ∣ M.f - V ^ 2 := by
      obtain ⟨c, hc⟩ := hnW
      refine ⟨D.u * c, ?_⟩
      calc
        M.f - V ^ 2 = D.u * w := hcurve
        _ = D.u * (normalize w * c) :=
          congrArg (fun z : K[X] ↦ D.u * z) hc
        _ = normalize w * (D.u * c) := by ring
    have hnGraph :
        normalize w ∣ V - V % normalize w :=
      normalize_dvd_sub_mod V w
    obtain ⟨a, ha⟩ := hnBase
    obtain ⟨b, hb⟩ := hnGraph
    refine ⟨a + b * (V + V % normalize w), ?_⟩
    calc
      M.f - (V % normalize w) ^ 2 =
          (M.f - V ^ 2) +
            (V - V % normalize w) *
              (V + V % normalize w) := by ring
      _ = normalize w * a +
            (normalize w * b) *
              (V + V % normalize w) := by rw [ha, hb]
      _ = normalize w *
            (a + b * (V + V % normalize w)) := by ring

@[simp] theorem cantorComplementSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).u = normalize w := rfl

@[simp] theorem cantorComplementSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).v =
      V % normalize w := rfl

@[simp] theorem cantorComplementSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).nInf = n := rfl

theorem mumfordIdeal_cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdeal M
        (cantorComplementSemi M D V w n hcurve hw).u
        (cantorComplementSemi M D V w n hcurve hw).v =
      mumfordIdeal M w V := by
  change
    mumfordIdeal M (normalize w) (V % normalize w) =
      mumfordIdeal M w V
  calc
    mumfordIdeal M (normalize w) (V % normalize w) =
        mumfordIdeal M (normalize w) V :=
      (mumfordIdeal_eq_of_dvd_sub M (normalize w)
        (V % normalize w) V
        (normalize_dvd_sub_mod V w)).symm
    _ = mumfordIdeal M w V := mumfordIdeal_normalize M w V

theorem mumfordIdeal_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M D.u D.v *
        mumfordIdeal M
          (cantorComplementSemi M D V w n hcurve hw).u
          (cantorComplementSemi M D V w n hcurve hw).v =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  rw [← mumfordIdeal_eq_of_dvd_sub M D.u D.v V hcongr,
    mumfordIdeal_cantorComplementSemi M D V w n hcurve hw]
  exact mumfordIdeal_mul_cantor M D.u w V hcurve hbezout

/-! ## Conjugating the complement -/

/-- The affine Cantor successor is the conjugate of the complement.  Its
graph polynomial is `(-V) mod normalize w`, up to the definitional
linearity of polynomial remainder. -/
def cantorConjugateSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  conjugateSemiMumford M
    (cantorComplementSemi M D V w n hcurve hw)

@[simp] theorem cantorConjugateSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).u =
      normalize w := rfl

@[simp] theorem cantorConjugateSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).v =
      -(V % normalize w) := rfl

theorem cantorConjugateSemi_v_eq_neg_mod
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).v =
      (-V) % normalize w := by
  change -(V % normalize w) = (-V) % normalize w
  rw [← Polynomial.modByMonic_eq_mod V (monic_normalize hw),
    ← Polynomial.modByMonic_eq_mod (-V) (monic_normalize hw),
    Polynomial.neg_modByMonic]

@[simp] theorem cantorConjugateSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).nInf = n := rfl

theorem mumfordIdeal_cantorConjugateSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdeal M
        (cantorConjugateSemi M D V w n hcurve hw).u
        (cantorConjugateSemi M D V w n hcurve hw).v =
      mumfordIdeal M w (-V) := by
  rw [cantorConjugateSemi_v_eq_neg_mod]
  change
    mumfordIdeal M (normalize w) ((-V) % normalize w) =
      mumfordIdeal M w (-V)
  calc
    mumfordIdeal M (normalize w) ((-V) % normalize w) =
        mumfordIdeal M (normalize w) (-V) :=
      (mumfordIdeal_eq_of_dvd_sub M (normalize w)
        ((-V) % normalize w) (-V)
        (normalize_dvd_sub_mod (-V) w)).symm
    _ = mumfordIdeal M w (-V) :=
      mumfordIdeal_normalize M w (-V)

/-! ## Principal functions in one oriented step -/

theorem ySubClass_ne_zero (V : K[X]) :
    ySubClass M V ≠ 0 := by
  intro h
  have hcoeff : (1 : K[X]) = 0 := by
    simpa using congrArg (coeffY M) h
  exact one_ne_zero hcoeff

def ySubFunctionUnit (V : K[X]) : (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (ySubClass M V))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (ySubClass_ne_zero M V))

@[simp] theorem coe_ySubFunctionUnit (V : K[X]) :
    (ySubFunctionUnit M V : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (ySubClass M V) := rfl

def xClassFunctionUnit (p : K[X]) (hp : p ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M p))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hp))

@[simp] theorem coe_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    (xClassFunctionUnit M p hp : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M p) := rfl

/-- The principal correction taking the conjugate complement back to the
original affine ideal class: `(Y-V) / normalize(w)`. -/
def cantorCorrectionUnit
    (V w : K[X]) (hw : w ≠ 0) :
    (FunctionField M)ˣ :=
  ySubFunctionUnit M V *
    (xClassFunctionUnit M (normalize w)
      (monic_normalize hw).ne_zero)⁻¹

theorem mumfordIdealUnit_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M D *
        mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (ySubFunctionUnit M V) := by
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_cantorComplement M D V w n hcurve hw
      hcongr hbezout,
    FractionalIdeal.coeIdeal_span_singleton]

theorem mumfordIdealUnit_complement_mul_conjugate
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) *
        mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (xClassFunctionUnit M (normalize w)
          (monic_normalize hw).ne_zero) := by
  let E := cantorComplementSemi M D V w n hcurve hw
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_xClassFunctionUnit]
  change
    (mumfordIdeal M E.u E.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M E.u (-E.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (algebraMap (CoordinateRing M) (FunctionField M)
          (xClass M E.u))
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_conj_integral M E,
    FractionalIdeal.coeIdeal_span_singleton]

theorem cantorConjugateSemi_principalRelation
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        toPrincipalIdeal (CoordinateRing M) (FunctionField M)
          (cantorCorrectionUnit M V w hw) =
      mumfordIdealUnit M D := by
  have hprod :=
    mumfordIdealUnit_mul_cantorComplement M D V w n
      hcurve hw hcongr hbezout
  have hnorm :=
    mumfordIdealUnit_complement_mul_conjugate M D V w n
      hcurve hw
  rw [cantorCorrectionUnit, map_mul, map_inv]
  calc
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (ySubFunctionUnit M V) *
          (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (xClassFunctionUnit M (normalize w)
              (monic_normalize hw).ne_zero))⁻¹) =
      mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        ((mumfordIdealUnit M D *
            mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw)) *
          (mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw) *
            mumfordIdealUnit M
              (cantorConjugateSemi M D V w n hcurve hw))⁻¹) := by
        rw [hprod, hnorm]
    _ = mumfordIdealUnit M D := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-! ## Exact oriented update -/

/-- The raw oriented class attached to an integral semirepresentative.  The
`-1` agrees exactly with `mumfordRaw` on balanced representatives. -/
def semiMumfordRaw (D : SemiMumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D,
    Multiplicative.ofAdd (D.nInf - 1))

def semiMumfordClass (O : InfinityOrder M) (D : SemiMumford M) :
    OrientedPic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range
      (semiMumfordRaw M D)

theorem semiMumfordClass_eq_iff
    (O : InfinityOrder M) (D₁ D₂ : SemiMumford M) :
    semiMumfordClass M O D₁ = semiMumfordClass M O D₂ ↔
      ∃ alpha : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁ *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M)
                alpha =
            mumfordIdealUnit M D₂ ∧
        Multiplicative.ofAdd (D₁.nInf - 1) *
              O.ordPlus alpha =
            Multiplicative.ofAdd (D₂.nInf - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₁) =
    QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨alpha, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨alpha, congrArg Prod.fst hmul, congrArg Prod.snd hmul⟩
  · rintro ⟨alpha, hIdeal, hInf⟩
    refine ⟨principalOriented M O alpha,
      MonoidHom.mem_range.mpr ⟨alpha, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

@[simp] theorem semiMumfordClass_toSemi
    (O : InfinityOrder M) (D : Mumford M) :
    semiMumfordClass M O D.toSemi = classOf M O D := rfl

/-- The unique integer correction forced by the order of the principal
function `(Y-V)/normalize(w)` at the chosen positive infinity. -/
def cantorNextNInf
    (O : InfinityOrder M) (D : SemiMumford M)
    (V w : K[X]) (hw : w ≠ 0) : ℤ :=
  D.nInf -
    Multiplicative.toAdd
      (O.ordPlus (cantorCorrectionUnit M V w hw))

/-- One structurally complete Cantor step, including the sign of the next
graph polynomial and the exact oriented-infinity correction. -/
def cantorNextSemi
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  cantorConjugateSemi M D V w
    (cantorNextNInf M O D V w hw) hcurve hw

@[simp] theorem cantorNextSemi_u
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u = normalize w := rfl

theorem cantorNextSemi_v
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).v =
      (-V) % normalize w :=
  cantorConjugateSemi_v_eq_neg_mod M D V w
    (cantorNextNInf M O D V w hw) hcurve hw

@[simp] theorem cantorNextSemi_nInf
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).nInf =
      D.nInf -
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) := rfl

theorem cantorNextSemi_class
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    semiMumfordClass M O
        (cantorNextSemi M O D V w hcurve hw) =
      semiMumfordClass M O D := by
  apply (semiMumfordClass_eq_iff M O
    (cantorNextSemi M O D V w hcurve hw) D).2
  refine ⟨cantorCorrectionUnit M V w hw, ?_, ?_⟩
  · exact cantorConjugateSemi_principalRelation M D V w
      (cantorNextNInf M O D V w hw) hcurve hw hcongr hbezout
  · change
      Multiplicative.ofAdd
          (D.nInf -
              Multiplicative.toAdd
                (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1) *
          O.ordPlus (cantorCorrectionUnit M V w hw) =
        Multiplicative.ofAdd (D.nInf - 1)
    change
      D.nInf -
          Multiplicative.toAdd
            (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1 +
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) =
      D.nInf - 1
    omega

theorem natDegree_normalize_eq
    (p : K[X]) :
    (normalize p).natDegree = p.natDegree := by
  exact natDegree_eq_natDegree degree_normalize

@[simp] theorem cantorNextSemi_natDegree
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u.natDegree =
      w.natDegree := by
  rw [cantorNextSemi_u, natDegree_normalize_eq]

theorem cantorBezout_of_semi_factor
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  obtain ⟨w', a, b, c, hw', hbez⟩ := mumford_bezout M D
  have hwEq : w' = w := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    exact hw'.symm.trans hcurve
  subst w'
  exact ⟨a, b, c, hbez⟩

/-- The ordinary branch of the degree step preserves the oriented class
and strictly decreases degree whenever the current degree exceeds three. -/
theorem cantorNextSemi_sameGraph
    (O : InfinityOrder M) (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w)
    (hdeg : 3 < D.u.natDegree) :
    semiMumfordClass M O
          (cantorNextSemi M O D D.v w hcurve
            (cantorFactor_ne_zero M D.u D.v w hcurve)) =
        semiMumfordClass M O D ∧
      (cantorNextSemi M O D D.v w hcurve
          (cantorFactor_ne_zero M D.u D.v w hcurve)).u.natDegree <
        D.u.natDegree := by
  let hw := cantorFactor_ne_zero M D.u D.v w hcurve
  constructor
  · apply cantorNextSemi_class M O D D.v w hcurve hw
    · simp
    · exact cantorBezout_of_semi_factor M D w hcurve
  · rw [cantorNextSemi_natDegree]
    exact cantorFactor_natDegree_lt M D w hcurve hdeg

/-- At degree three, the monic lift `V=v+u` preserves the oriented class
and lands directly in affine degree at most two. -/
theorem cantorNextSemi_cubic
    (O : InfinityOrder M) (D : SemiMumford M) (w : K[X])
    (hdeg : D.u.natDegree = 3)
    (hcurve : M.f - (D.v + D.u) ^ 2 = D.u * w) :
    semiMumfordClass M O
          (cantorNextSemi M O D (D.v + D.u) w hcurve
            (cubicCantorFactor M D w hdeg hcurve).1) =
        semiMumfordClass M O D ∧
      (cantorNextSemi M O D (D.v + D.u) w hcurve
          (cubicCantorFactor M D w hdeg hcurve).1).u.natDegree ≤ 2 := by
  let hw := (cubicCantorFactor M D w hdeg hcurve).1
  constructor
  · apply cantorNextSemi_class M O D (D.v + D.u) w hcurve hw
    · refine ⟨1, ?_⟩
      ring
    · simpa using cantorBezout_add_mul M D 1 w (by simpa using hcurve)
  · rw [cantorNextSemi_natDegree]
    exact (cubicCantorFactor M D w hdeg hcurve).2

end

end MazurProof.SexticMumford


