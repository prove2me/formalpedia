-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:50.905266+00:00
-- url     : https://prove2.me/theorems/9bf3c03f-23f9-4ce0-b822-a1f91509acb0
-- title:
--   PChart Lat Nm Section
-- statement:
--   Definitions and structural lemmas for PChart Lat Nm Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
theorem mConeMap_of_homog (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f d) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
  have hf' := (geoMultiHomog_iff f d).mpr hf
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [Geo.mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring
theorem mem_mCoordIdeal_iff (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f d) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_homog y hf, mul_eq_zero, C_eq_zero]
  have : (∏ k, (X k : MvPolynomial ι Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
  simp [this]
variable (P : ArithVariety n) (y : Coord n → Ω)
theorem mkF_eq_zero_iff' (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
    {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f d) :
    P.mkF f = 0 ↔ aeval y f = 0 := by
  rw [P.mkF_eq_zero_iff, hP, mem_mCoordIdeal_iff y hf]
theorem exists_rep (hb : Geo.Birational (ι := blockIdx n) y) (s : Ω) :
    ∃ (g h : MvPolynomial (Coord n) ℤ) (d : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g d ∧
      IsWeightedHomogeneous (coordDeg n) h d ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h := by
  obtain ⟨d, g, h, hg, hh, h0, he⟩ := hb s
  exact ⟨g, h, d, (geoMultiHomog_iff g d).mp hg, (geoMultiHomog_iff h d).mp hh, h0, he⟩
theorem frac_eq (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) {s : Ω}
    {g q g₀ q₀ : MvPolynomial (Coord n) ℤ} {d d₀ : ι → ℕ}
    (hg : IsWeightedHomogeneous (coordDeg n) g d) (hq : IsWeightedHomogeneous (coordDeg n) q d)
    (h0 : aeval y q ≠ 0) (he : aeval y g = s * aeval y q)
    (hg₀ : IsWeightedHomogeneous (coordDeg n) g₀ d₀) (hq₀ : IsWeightedHomogeneous (coordDeg n) q₀ d₀)
    (hq₀0 : aeval y q₀ ≠ 0) (he₀ : aeval y g₀ = s * aeval y q₀) :
    P.mkF g₀ / P.mkF q₀ = P.mkF g / P.mkF q := by
  rw [div_eq_div_iff (fun h => hq₀0 ((mkF_eq_zero_iff' P y hP hq₀).mp h))
    (fun h => h0 ((mkF_eq_zero_iff' P y hP hq).mp h))]
  rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]
  have h1 := hg₀.mul hq
  have h2 := hg.mul hq₀
  rw [add_comm] at h2
  have hsub : IsWeightedHomogeneous (coordDeg n) (g₀ * q - g * q₀) (d₀ + d) :=
    (weightedHomogeneousSubmodule ℤ (coordDeg n) (d₀ + d)).sub_mem h1 h2
  rw [mkF_eq_zero_iff' P y hP hsub, map_sub, map_mul, map_mul, he₀, he]
  ring
def thetaFun (hb : Geo.Birational (ι := blockIdx n) y) (s : Ω) : P.FunField :=
  P.mkF (exists_rep y hb s).choose / P.mkF (exists_rep y hb s).choose_spec.choose
theorem thetaFun_eq (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
    (hb : Geo.Birational (ι := blockIdx n) y) {s : Ω} {g q : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hg : IsWeightedHomogeneous (coordDeg n) g d) (hq : IsWeightedHomogeneous (coordDeg n) q d)
    (h0 : aeval y q ≠ 0) (he : aeval y g = s * aeval y q) :
    thetaFun P y hb s = P.mkF g / P.mkF q := by
  obtain ⟨d₀, hg₀, hq₀, hq₀0, he₀⟩ := (exists_rep y hb s).choose_spec.choose_spec
  exact frac_eq P y hP hg hq h0 he hg₀ hq₀ hq₀0 he₀
def theta (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
    (hb : Geo.Birational (ι := blockIdx n) y) : Ω →+* P.FunField where
  toFun := thetaFun P y hb
  map_one' := by
    rw [thetaFun_eq P y hP hb (isWeightedHomogeneous_one ℤ (coordDeg n))
      (isWeightedHomogeneous_one ℤ (coordDeg n)) (by simp) (by simp)]
    simp
  map_zero' := by
    rw [thetaFun_eq P y hP hb (isWeightedHomogeneous_zero ℤ (coordDeg n) 0)
      (isWeightedHomogeneous_one ℤ (coordDeg n)) (by simp) (by simp)]
    simp
  map_mul' s s' := by
    obtain ⟨g, q, d, hg, hq, hq0, he⟩ := exists_rep y hb s
    obtain ⟨g', q', d', hg', hq', hq0', he'⟩ := exists_rep y hb s'
    rw [thetaFun_eq P y hP hb hg hq hq0 he, thetaFun_eq P y hP hb hg' hq' hq0' he',
      thetaFun_eq P y hP hb (hg.mul hg') (hq.mul hq') (by rw [map_mul]; exact mul_ne_zero hq0 hq0')
        (by rw [map_mul, map_mul, he, he']; ring), map_mul, map_mul, div_mul_div_comm]
  map_add' s s' := by
    obtain ⟨g, q, d, hg, hq, hq0, he⟩ := exists_rep y hb s
    obtain ⟨g', q', d', hg', hq', hq0', he'⟩ := exists_rep y hb s'
    have h2 := hg'.mul hq
    rw [add_comm] at h2
    have hQ0 : P.mkF q ≠ 0 := fun h => hq0 ((mkF_eq_zero_iff' P y hP hq).mp h)
    have hQ0' : P.mkF q' ≠ 0 := fun h => hq0' ((mkF_eq_zero_iff' P y hP hq').mp h)
    rw [thetaFun_eq P y hP hb hg hq hq0 he, thetaFun_eq P y hP hb hg' hq' hq0' he',
      thetaFun_eq P y hP hb ((hg.mul hq').add h2) (hq.mul hq')
        (by rw [map_mul]; exact mul_ne_zero hq0 hq0')
        (by simp only [map_add, map_mul]; rw [he, he']; ring)]
    rw [div_add_div _ _ hQ0 hQ0']
    simp only [map_add, map_mul]
    ring
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)
theorem theta_eq {s : Ω} {g q : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hg : IsWeightedHomogeneous (coordDeg n) g d) (hq : IsWeightedHomogeneous (coordDeg n) q d)
    (h0 : aeval y q ≠ 0) (he : aeval y g = s * aeval y q) :
    theta P y hP hb s = P.mkF g / P.mkF q :=
  thetaFun_eq P y hP hb hg hq h0 he
theorem theta_chartCoord (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (p : Coord n) :
    theta P y hP hb (y p / y ⟨p.1, c p.1⟩) = P.chartCoord c p := by
  rw [ArithVariety.chartCoord]
  exact theta_eq P y hP hb (isWeightedHomogeneous_X ℤ (coordDeg n) p)
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨p.1, c p.1⟩ : IsWeightedHomogeneous _ _ (coordDeg n p))
    (by rw [aeval_X]; exact hc p.1) (by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (hc p.1)])
theorem theta_mem_chartRing (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) : theta P y hP hb x ∈ P.chartRing c := by
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨p, rfl⟩ := hu
    rw [theta_chartCoord P y hP hb c hc p]
    exact Subring.subset_closure ⟨p, rfl⟩
  | algebraMap r =>
    rw [eq_intCast, map_intCast]
    exact intCast_mem _ r
  | add u v _ _ hu hv =>
    rw [map_add]
    exact add_mem hu hv
  | mul u v _ _ hu hv =>
    rw [map_mul]
    exact mul_mem hu hv
def thetaChart (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Geo.chartRingZ (ι := blockIdx n) y c →+* P.chartRing c :=
  ((theta P y hP hb).comp (Geo.chartRingZ (ι := blockIdx n) y c).val.toRingHom).codRestrict
    (P.chartRing c) fun x => theta_mem_chartRing P y hP hb c hc x.2
def readElt (c₀ : (k : ι) → Fin (n k + 1)) (b : ι → ℤ) (s : Ω) : P.FunField :=
  theta P y hP hb (s * ∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * P.chartPow c₀ b
end ChartLatNm
end
end GroundTheory.Heights₂.Heights


