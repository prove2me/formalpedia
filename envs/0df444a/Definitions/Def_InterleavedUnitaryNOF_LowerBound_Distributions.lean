-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Distributions
-- name    : InterleavedUnitaryNOF_LowerBound_Distributions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:12.014385+00:00
-- url     : https://prove2.me/theorems/ff3cb76b-04fa-4645-bdc6-a72aea781421
-- title:
--   Independent and constrained Haar input laws, rounding and cylinders
-- statement:
--   The independent law samples all ten Haar factors. The constrained law samples $X,Y,E_1$ independently and sets $E_2=(PE_1Q)^{-1}$, with $P=A_1B_1C_1D_1$ and $Q=A_2B_2C_2D_2$. Both are actual probability constructions on continuous special-unitary groups.
--
--   $$R_b(t)=2^{-b}\lceil2^bt-1/2\rceil,\qquad \widetilde\mu_j=R_*\mu_j.$$
--
--   The rounding maps inverse-encode each coordinate and pad the three bit strings separately; measurability is proved. A cylinder stores exactly three measurable Boolean factors. Specified-product averages sample three independent Haar elements and compute the fourth, including the coordinatewise two-group version.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), §4, pp.9–10; §4.2 product-conditioning convention, p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Haar

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

abbrev Quart (m : ℕ) := Fin 4 → SU m
abbrev Duo (m : ℕ) := Fin 2 → SU m
abbrev ContinuousInput (m : ℕ) := Quart m × Quart m × Duo m

noncomputable def haarPower (m q : ℕ) [NeZero m] : Measure (Fin q → SU m) :=
  Measure.pi (fun _ => haar m)
instance haarPowerProbability (m q : ℕ) [NeZero m] :
    IsProbabilityMeasure (haarPower m q) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

noncomputable def mu0 (m : ℕ) [NeZero m] : Measure (ContinuousInput m) :=
  (haarPower m 4).prod ((haarPower m 4).prod (haarPower m 2))

def firstProduct {m : ℕ} (x y : Quart m) : SU m := x 0 * y 0 * x 1 * y 1

def secondProduct {m : ℕ} (x y : Quart m) : SU m := x 2 * y 2 * x 3 * y 3

/-- Independent X,Y,E₁, with only E₂ set to the required inverse. -/
def constrainedSample {m : ℕ} (u : Quart m × Quart m × SU m) : ContinuousInput m :=
  (u.1, u.2.1, ![u.2.2, (firstProduct u.1 u.2.1 * u.2.2 * secondProduct u.1 u.2.1)⁻¹])

theorem constrainedSample_measurable (m : ℕ) :
    Measurable (@constrainedSample m) := by
  unfold constrainedSample firstProduct secondProduct
  refine measurable_fst.prodMk (measurable_snd.fst.prodMk ?_)
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> dsimp
  · exact measurable_snd.snd
  · apply Continuous.measurable
    fun_prop

noncomputable def mu1 (m : ℕ) [NeZero m] : Measure (ContinuousInput m) :=
  Measure.map constrainedSample ((haarPower m 4).prod ((haarPower m 4).prod (haar m)))

instance mu0Probability (m : ℕ) [NeZero m] : IsProbabilityMeasure (mu0 m) :=
  inferInstanceAs (IsProbabilityMeasure ((haarPower m 4).prod ((haarPower m 4).prod (haarPower m 2))))

instance mu1Probability (m : ℕ) [NeZero m] : IsProbabilityMeasure (mu1 m) :=
  Measure.isProbabilityMeasure_map (constrainedSample_measurable m).aemeasurable

def matrices {m : ℕ} (u : ContinuousInput m) : MatrixInput m :=
  (fun a => (u.1 a).val, fun a => (u.2.1 a).val, fun a => (u.2.2 a).val)

noncomputable def bval (b : Bool) : ℝ := if b then 1 else 0

/-- Nearest grid point with exact half-way ties down. -/
noncomputable def roundReal (n : ℕ) (t : ℝ) : ℝ :=
  (Int.ceil ((2 : ℝ)^(precision n) * t - 1/2) : ℝ) / (2 : ℝ)^(precision n)

/-- Inverse two's-complement encoding, then independent zero padding. -/
noncomputable def roundGroup {m q : ℕ} (n : ℕ) (u : Fin q → SU m) : Bits n :=
  fun k =>
    let block := k.val / (precision n + 2)
    let entry := block / 2
    let a := entry / (m*m)
    let i := entry / m % m
    let j := entry % m
    if ha : a < q then if hi : i < m then if hj : j < m then
      let v := (u ⟨a,ha⟩).val ⟨i,hi⟩ ⟨j,hj⟩
      let t := if block % 2 = 0 then v.re else v.im
      let z := Int.ceil ((2 : ℝ)^(precision n) * t - 1/2)
      Nat.testBit (z % (2 : ℤ)^(precision n + 2)).toNat (k.val % (precision n + 2))
      else false else false else false

@[fun_prop] theorem continuous_su_entry (m q : ℕ) (a : Fin q) (i j : Fin m) :
    Continuous (fun u : Fin q → SU m => (u a).val i j) :=
  (continuous_subtype_val.comp (continuous_apply a)).matrix_elem i j

theorem roundGroup_measurable (m q n : ℕ) : Measurable (@roundGroup m q n) := by
  classical
  apply measurable_pi_iff.mpr
  intro k
  dsimp [roundGroup]
  split_ifs
  all_goals first
    | exact measurable_const
    | refine (measurable_of_countable (fun z : ℤ =>
        Nat.testBit (z % (2 : ℤ)^(precision n + 2)).toNat
          (k.val % (precision n + 2)))).comp (Int.measurable_ceil.comp ?_)
      apply Continuous.measurable
      fun_prop

noncomputable def roundInputs {m : ℕ} (n : ℕ) (u : ContinuousInput m) :
    Bits n × Bits n × Bits n :=
  (roundGroup n u.1, roundGroup n u.2.1, roundGroup n u.2.2)

theorem roundInputs_measurable (m n : ℕ) : Measurable (@roundInputs m n) :=
  ((roundGroup_measurable m 4 n).comp measurable_fst).prodMk
    (((roundGroup_measurable m 4 n).comp measurable_snd.fst).prodMk
      ((roundGroup_measurable m 2 n).comp measurable_snd.snd))

noncomputable def roundedMu (j : Bool) (n m : ℕ) [NeZero m] :
    Measure (Bits n × Bits n × Bits n) :=
  Measure.map (roundInputs n) (if j then mu1 m else mu0 m)

/-- All measurable Boolean cylinder factors, with no finite-type restriction. -/
structure Cylinder (m : ℕ) where
  f : Quart m × Duo m → Bool
  g : Quart m × Duo m → Bool
  h : Quart m × Quart m → Bool
  measurable_f : Measurable f
  measurable_g : Measurable g
  measurable_h : Measurable h

def Cylinder.value {m : ℕ} (c : Cylinder m) (u : ContinuousInput m) : Bool :=
  c.f (u.2.1,u.2.2) && c.g (u.1,u.2.2) && c.h (u.1,u.2.1)

noncomputable def mass {m : ℕ} (μ : Measure (ContinuousInput m)) (c : Cylinder m) : ℝ :=
  ∫ u, bval (c.value u) ∂μ

/-- The constraint law ABCD=T is sampling, not conditioning on a null event. -/
noncomputable def productAverage {G : Type*} [Group G] [MeasurableSpace G]
    (ν : Measure G) (T : G) (a b : G × G → ℝ) : ℝ :=
  ∫ A, ∫ B, ∫ C, a (A,C) * b (B,(A*B*C)⁻¹*T) ∂ν ∂ν ∂ν

noncomputable def pairAverage {G : Type*} [MeasurableSpace G]
    (ν : Measure G) (a : G × G → ℝ) : ℝ := ∫ u, a u ∂(ν.prod ν)

end InterleavedUnitaryNOF.LowerBound


