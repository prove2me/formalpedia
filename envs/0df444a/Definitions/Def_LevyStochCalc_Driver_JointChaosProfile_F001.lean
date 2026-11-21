-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosProfile_F001
-- name    : LevyStochCalc_Driver_JointChaosProfile_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:40:34.356742+00:00
-- url     : https://prove2.me/theorems/61fb1216-c913-46ed-9299-94e99b2c51c0
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfile_F000
import Definitions.Def_SourceProof_37a7ff2c7873067deccef303
import Definitions.Def_SourceProof_b5912c738affc5f69d2adbcb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos element of one step of a Lévy driver at a simple mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a finite pairwise disjoint family `A` of
mark sets of finite intensity carrying a profile `c` constant on each of them, the
bidegree-`(n, m)` element of the step is the product `H_n(ΔWʲ; b - a) D_m(c)` of the degree-`n`
Wiener chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` chaos element of the
profile over the strips `(a, b] ×ˢ A k`. Since `σ(W)` and `σ(N)` are independent, the expectation
of a product of a function of the increment and a function of the counts of the strips factors,
so the `L²` pairing of two such elements is the product of the Hermite and the Charlier factor,
`E[J_(n, m)(c) J_(n', m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m` for `τ = b - a` and
the bilinear form `⟨c, c'⟩ = ∑_k c_k c'_k τ ν(A k)`. Distinct bidegrees are therefore orthogonal,
and a fortiori so are distinct total degrees `n + m`. The step tuple is independent of the joint
filtration at `a`, so the conditional pairing at that node is the same constant.

One Brownian coordinate is covered, and the profile is constant on the sets of one given family:
no mode of `L²(ν)` beyond such combinations of indicators enters. On a one-set family the element
is the single-mark-set element of a step scaled by `c 0 ^ m`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile` — the bidegree-`(n, m)` element of a
  step at a mark profile.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.measurable_markedChaosDegree_sigmaPoisson` — a degree element
  of a profile is measurable for the Poisson σ-algebra of the driver.
* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_markedChaosDegree` — a Brownian increment
  of the driver is independent of a degree element of a profile of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfile` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul` —
  `E[J_(n,m)(c) J_(n',m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_sq` — the second moment as the
  product of the Hermite and the Charlier factor.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero_of_add_ne` —
  orthogonality across bidegrees and across total degrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfile_mul` — the conditional pairing
  at the node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Independence of the Brownian and the Poisson data of a step -/

namespace LevyDriver

/-! ### The element of a bidegree at a mark profile -/

/-- Joint chaos elements of a step of the driver at mark profiles with different total degrees
are orthogonal. -/
theorem integral_jointChaosStepProfile_mul_eq_zero_of_add_ne (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) {n m n' m' : ℕ} (hdeg : n + m ≠ n' + m')
    (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
      * D.jointChaosStepProfile j n' m' a b A c' ω ∂P = 0 := by
  classical
  rw [(_root_.Prove2MeSourceProof.h_37a7ff2c7873067deccef303 D) j hab hA hAν hd n m n' m' c c']
  rcases eq_or_ne n n' with rfl | hn
  · have hm : m ≠ m' := fun h => hdeg (by rw [h])
    simp [hm]
  · simp [hn]
/-- Joint chaos elements of a step of the driver at mark profiles of different bidegrees are
orthogonal. -/
theorem integral_jointChaosStepProfile_mul_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) {n m n' m' : ℕ}
    (hne : (n, m) ≠ (n', m')) (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
      * D.jointChaosStepProfile j n' m' a b A c' ω ∂P = 0 := by
  classical
  rw [(_root_.Prove2MeSourceProof.h_37a7ff2c7873067deccef303 D) j hab hA hAν hd n m n' m' c c']
  rcases eq_or_ne n n' with rfl | hn
  · have hm : m ≠ m' := fun h => hne (by rw [h])
    simp [hm]
  · simp [hn]
/-- The second moment of a joint chaos element of a step of the driver at a mark profile is the
product of the Hermite and the Charlier factor,
`E[J_(n,m)(c) ^ 2] = n! τ ^ n m! (∑_k c_k ^ 2 τ ν(A k)) ^ m`. -/
theorem integral_jointChaosStepProfile_sq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m : ℕ)
    (c : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω ^ 2 ∂P
      = ((n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n)
        * ((m.factorial : ℝ)
          * (∑ k, c k ^ 2 * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m) := by
  have h := (_root_.Prove2MeSourceProof.h_37a7ff2c7873067deccef303 D) j hab hA hAν hd n m n m c c
  rw [if_pos rfl, if_pos rfl] at h
  simp only [← pow_two] at h
  exact h
/-- The joint chaos elements of a step of the driver at a mark profile are centred in positive
total degree. -/
theorem integral_jointChaosStepProfile_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) {n m : ℕ}
    (hnm : n + m ≠ 0) (c : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω ∂P = 0 := by
  have h := D.integral_jointChaosStepProfile_mul_eq_zero_of_add_ne j hab hA hAν hd
    (n := n) (m := m) (n' := 0) (m' := 0) (by simpa using hnm) c c
  simpa using h
/-- The conditional pairing of the joint chaos elements of a step of the driver at mark profiles,
taken at the node preceding the step, agrees with the unconditional one. -/
theorem condExp_jointChaosStepProfile_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m n' m' : ℕ)
    (c c' : Fin p → ℝ) :
    P[fun ω => D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω | D.filtration (a : ℝ)]
      =ᵐ[P] fun _ => (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (∑ k, c k * c' k * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m else 0) := by
  classical
  set C : Fin p → Set (ℝ × E) := fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k with hC
  have hCm : ∀ k, MeasurableSet (C k) := fun k => measurableSet_Ioc.prod (hA k)
  have hCs : ∀ k, C k ⊆ Set.Ioi (a : ℝ) ×ˢ Set.univ := fun k x hx => ⟨hx.1.1, trivial⟩
  have hindep : Indep (D.stepSigma C (a : ℝ) (b : ℝ)) (D.filtration (a : ℝ)) P :=
    (_root_.Prove2MeSourceProof.h_b5912c738affc5f69d2adbcb D) C hCm a.coe_nonneg (by exact_mod_cast hab) hCs
  have hincr : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      (le_sup_of_le_left (le_iSup (fun i => D.incrementSigma i (a : ℝ) (b : ℝ)) j))
  have hcount : ∀ k, Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (fun ω => D.N.N ω (C k)) :=
    fun k => Measurable.of_comap_le
      (le_sup_of_le_right (le_iSup (fun k => D.regionSigma (C k)) k))
  have hmc : ∀ (r : ℕ) (e : Fin p → ℝ), Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (Poisson.markedChaosDegree D.N r C e) := fun r e =>
    Finset.measurable_sum _ fun α _ =>
      (Finset.univ.measurable_prod fun k _ =>
          (((Probability.continuous_charlierScaled (α k) _).measurable).comp
              ENNReal.measurable_toReal).comp (hcount k)).const_mul _
  have hstep : ∀ (q r : ℕ) (e : Fin p → ℝ), Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStepProfile j q r a b A e ω) := fun q r e =>
    ((Probability.measurable_wienerChaosStep q _).comp hincr).mul (hmc r e)
  have hmeas : StronglyMeasurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω) :=
    Measurable.stronglyMeasurable ((hstep n m c).mul (hstep n' m' c'))
  have h := condExp_indep_eq (D.stepSigma_le C hCm (a : ℝ) (b : ℝ)) (D.filtration.le (a : ℝ))
    hmeas hindep
  rw [(_root_.Prove2MeSourceProof.h_37a7ff2c7873067deccef303 D) j hab.le hA hAν hd n m n' m' c c'] at h
  exact h
end LevyDriver

end LevyStochCalc.Driver


