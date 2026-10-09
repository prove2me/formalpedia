-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityIdealApproximation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityIdealApproximation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:02:20.139854+00:00
-- url     : https://prove2.me/theorems/0134f4d3-50f0-45a8-b656-ca57e3a249c0
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityIdealApproximation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityIdealApproximation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityIdealApproximation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJetLift_p0
import Mathlib.RingTheory.Ideal.Prod

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Actual N13 two-branch ideal equality implies all-order approximation on the
ordinary infinity chart after clearing one nonzero vertical scalar. The
scalar is retained, not cancelled in the integral ring. This is the precise
input that becomes ordinary approximation after generic-fibre localization.
-/

namespace MazurProof.N13InfinityIdealApproximation

noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def jetIdeal (n : ℕ) : Ideal QP := Ideal.span ({PowerSeries.X ^ n} : Set QP)
abbrev Jet (n : ℕ) := QP ⧸ jetIdeal n
abbrev JetPair (n : ℕ) := Jet n × Jet n

def jetQuot (n : ℕ) : QP →+* Jet n := Ideal.Quotient.mk (jetIdeal n)

def toJets (n : ℕ) : B →+* JetPair n :=
  ((jetQuot n).comp N13InfinityChartMarking.positiveExpansion).prod
    ((jetQuot n).comp N13InfinityChartMarking.negativeExpansion)

def scalar (n : ℕ) : R₂ →+* JetPair n := (toJets n).comp (algebraMap R₂ B)

theorem positive_scalar (c : R₂) :
    N13InfinityChartMarking.positiveExpansion (algebraMap R₂ B c) =
      PowerSeries.C (cMap c) := by
  change N13InfinityChartMarking.positiveExpansion (base (Polynomial.C c)) = _
  rw [generic_plus_base]
  simp

theorem negative_scalar (c : R₂) :
    N13InfinityChartMarking.negativeExpansion (algebraMap R₂ B c) =
      PowerSeries.C (cMap c) := by
  change N13InfinityChartMarking.negativeExpansion (base (Polynomial.C c)) = _
  rw [generic_minus_base]
  simp

theorem jet_eq_of_dvd_sub (n : ℕ) (r s : QP)
    (h : (PowerSeries.X : QP) ^ n ∣ r - s) : jetQuot n r = jetQuot n s := by
  have hh : jetQuot n (r - s) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

theorem toJets_eq_zero_iff (n : ℕ) (z : B) :
    toJets n z = 0 ↔ N13IntegralInfinityChart.tClass ^ n ∣ z := by
  rw [generic_branch_dvd_iff]
  constructor
  · intro h
    have hp : jetQuot n (N13InfinityChartMarking.positiveExpansion z) = 0 :=
      congrArg Prod.fst h
    have hm : jetQuot n (N13InfinityChartMarking.negativeExpansion z) = 0 :=
      congrArg Prod.snd h
    exact ⟨Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp),
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hm)⟩
  · rintro ⟨hp, hm⟩
    apply Prod.ext
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hp)
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hm)

/-- Every pair of finite generic jets is the jet of one integral chart
element up to a common nonzero Z2 scalar. -/
theorem exists_scaled_jet_pair (n : ℕ) (w : JetPair n) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ z : B, toJets n z = scalar n c * w := by
  rcases w with ⟨r, s⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨c, hc, z, hp, hm⟩ := exists_scaled_branch_jet_lift n r s
  refine ⟨c, hc, z, ?_⟩
  apply Prod.ext
  · change jetQuot n (N13InfinityChartMarking.positiveExpansion z) =
      jetQuot n (N13InfinityChartMarking.positiveExpansion (algebraMap R₂ B c)) * jetQuot n r
    rw [positive_scalar, ← map_mul]
    exact jet_eq_of_dvd_sub n _ _ hp
  · change jetQuot n (N13InfinityChartMarking.negativeExpansion z) =
      jetQuot n (N13InfinityChartMarking.negativeExpansion (algebraMap R₂ B c)) * jetQuot n s
    rw [negative_scalar, ← map_mul]
    exact jet_eq_of_dvd_sub n _ _ hm

/-- Jets that are represented by an element of J after one nonzero vertical
scalar. Jet lifting supplies closure under arbitrary coefficient pairs. -/
def scaledIdeal (n : ℕ) (J : Ideal B) : Ideal (JetPair n) where
  carrier := {w | ∃ c : R₂, c ≠ 0 ∧ ∃ z : B, z ∈ J ∧ toJets n z = scalar n c * w}
  zero_mem' := by
    refine ⟨1, one_ne_zero, 0, J.zero_mem, ?_⟩
    simp
  add_mem' := by
    intro u v hu hv
    obtain ⟨c, hc, x, hx, hxu⟩ := hu
    obtain ⟨d, hd, y, hy, hyv⟩ := hv
    refine ⟨c * d, mul_ne_zero hc hd,
      algebraMap R₂ B d * x + algebraMap R₂ B c * y,
      J.add_mem (J.mul_mem_left _ hx) (J.mul_mem_left _ hy), ?_⟩
    rw [map_add, map_mul, map_mul]
    change scalar n d * toJets n x + scalar n c * toJets n y = _
    rw [hxu, hyv, map_mul]
    ring
  smul_mem' := by
    intro u v hv
    obtain ⟨c, hc, x, hx, hxv⟩ := hv
    obtain ⟨d, hd, y, hyu⟩ := exists_scaled_jet_pair n u
    refine ⟨c * d, mul_ne_zero hc hd, y * x, J.mul_mem_left _ hx, ?_⟩
    change toJets n (y * x) = scalar n (c * d) * (u * v)
    rw [map_mul, hyu, hxv, map_mul]
    ring

theorem map_toJets_le_scaledIdeal (n : ℕ) (J : Ideal B) :
    Ideal.map (toJets n) J ≤ scaledIdeal n J := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro z hz
  refine ⟨1, one_ne_zero, z, hz, ?_⟩
  simp

private theorem map_prod_eq
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (I : Ideal R) :
    Ideal.map (f.prod g) I = Ideal.prod (Ideal.map f I) (Ideal.map g I) := by
  rw [Ideal.ideal_prod_eq (Ideal.map (f.prod g) I)]
  simp only [Ideal.map_map]
  rfl

theorem map_toJets_eq_of_branch_eq
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (n : ℕ) : Ideal.map (toJets n) I = Ideal.map (toJets n) J := by
  unfold toJets
  rw [map_prod_eq, map_prod_eq]
  simp only [← Ideal.map_map]
  rw [hp, hm]

/-- The actual two generic branch ideal equalities now produce an actual
ordinary-chart approximation to EVERY finite order. The nonzero vertical
scalar is explicit; it becomes invertible only on the generic fibre. -/
theorem scaled_approximations_of_branch_eq
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (x : B) (hx : x ∈ I) (n : ℕ) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ y : B,
      algebraMap R₂ B c * x - N13IntegralInfinityChart.tClass ^ n * y ∈ J := by
  have hj : toJets n x ∈ Ideal.map (toJets n) J := by
    rw [← map_toJets_eq_of_branch_eq I J hp hm n]
    exact Ideal.mem_map_of_mem (toJets n) hx
  obtain ⟨c, hc, z, hz, heq⟩ := map_toJets_le_scaledIdeal n J hj
  have hzero : toJets n (algebraMap R₂ B c * x - z) = 0 := by
    rw [map_sub, map_mul]
    change scalar n c * toJets n x - toJets n z = 0
    rw [heq, sub_self]
  obtain ⟨y, hy⟩ := (toJets_eq_zero_iff n _).mp hzero
  refine ⟨c, hc, y, ?_⟩
  have hsame : algebraMap R₂ B c * x - N13IntegralInfinityChart.tClass ^ n * y = z := by
    linear_combination hy
  rw [hsame]
  exact hz

end
end MazurProof.N13InfinityIdealApproximation


