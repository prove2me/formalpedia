-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_RateModel
-- name    : BauerleRiederMDP_PDMDP_RateModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:22.234198+00:00
-- url     : https://prove2.me/theorems/6b20e499-7aac-44f5-a7d7-80e3c83eb65c
-- title:
--   Transition rates $q_{xy}(u)$, the uniformized kernel $Q$ and assumptions (i)–(iv)
-- statement:
--   A continuous-time Markov Decision Chain has a countable state space $E$, transition rates $q_{xy}(u)\in\mathbb R$ that are **conservative**, $\sum_{y\in E}q_{xy}(u)=0$, and **bounded**, $\lambda\ge-q_{xx}(u)$, and a reward rate $r$. The **uniformized** transition probabilities are
--   $$
--   Q(\{y\}|x,u):=\begin{cases}\frac1\lambda q_{xy}(u),&y\ne x,\\1+\frac1\lambda q_{xx}(u),&y=x.\end{cases}
--   $$
--   The module proves that $Q$ is a Markov kernel, defines $\sum_yq_{xy}(u)v(y)$ and $r(x,u)+\sum_yq_{xy}(u)v(y)$, and states the assumptions: (i) $U$ compact, (ii) $u\mapsto q_{xy}(u)$ continuous, (iii) $u\mapsto\sum_yb(y)q_{xy}(u)$ continuous, (iv) $u\mapsto r(x,u)$ upper semicontinuous.
--
--   **Formalization Note** $q_{xy}(u)\ge0$ for $y\ne x$ and the measurability of $q_{xy}$ are required: they make $Q$ a stochastic kernel. For $v$ with values in $[-\infty,\infty)$ the sum is the diagonal term plus an integral against the nonnegative rates; it is meaningful when $v(x)>-\infty$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.256–257 and Theorem 8.3.1, p.257

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace BauerleRiederMDP.PDMDP

/-- The rate data of a continuous-time Markov Decision Chain (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §8.3, pp.256–257, PDF 267–268):
the countable state space `E`, the transition rates `q_{xy}(u) ∈ ℝ`, which are conservative,
`∑_y q_{xy}(u) = 0`, and bounded, `λ ≥ -q_{xx}(u)`, and the reward rate `r`.

**Formalization Note** `HasSum` carries the absolute convergence of the conservativity sum.
`q_{xy}(u) ≥ 0` for `y ≠ x` is what makes `q` transition rates, and `Q` below a probability; the
measurability of `u ↦ q_{xy}(u)` makes `Q` a kernel. -/
structure RateModel (E U : Type*) [MeasurableSpace E] [MeasurableSpace U] where
  /-- The rates `q_{xy}(u)`, as `q x y u`. -/
  q : E → E → U → ℝ
  q_measurable : ∀ x y, Measurable (q x y)
  q_nonneg : ∀ x y u, y ≠ x → 0 ≤ q x y u
  q_conservative : ∀ x u, HasSum (fun y => q x y u) 0
  /-- The uniformization rate `λ`, the intensity of the Poisson process. -/
  lam : ℝ
  lam_pos : 0 < lam
  q_bounded : ∀ x u, -q x x u ≤ lam
  /-- The reward rate. -/
  r : E × U → ℝ
  r_measurable : Measurable r

namespace RateModel

variable {E U : Type*} [MeasurableSpace E] [MeasurableSpace U]

/-- The transition probabilities of the uniformized chain (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.257, PDF 268):
`Q({y}|x,u) := q_{xy}(u)/λ` for `y ≠ x` and `1 + q_{xx}(u)/λ` for `y = x`. -/
noncomputable def Qprob (R : RateModel E U) (x : E) (u : U) (y : E) : ℝ :=
  if y = x then 1 + R.q x x u / R.lam else R.q x y u / R.lam

theorem Qprob_nonneg (R : RateModel E U) (x : E) (u : U) (y : E) : 0 ≤ R.Qprob x u y := by
  unfold Qprob
  have hl := R.lam_pos
  split_ifs with h
  · have : -1 ≤ R.q x x u / R.lam := by
      rw [le_div_iff₀ hl]
      linarith [R.q_bounded x u]
    linarith
  · exact div_nonneg (R.q_nonneg x y u h) hl.le

theorem hasSum_Qprob (R : RateModel E U) (x : E) (u : U) : HasSum (R.Qprob x u) 1 := by
  have h1 : HasSum (fun y => R.q x y u / R.lam) 0 := by
    simpa using (R.q_conservative x u).div_const R.lam
  have h2 : HasSum (fun y => if y = x then (1 : ℝ) else 0) 1 := hasSum_ite_eq x 1
  have h3 := h1.add h2
  rw [zero_add] at h3
  convert h3 using 1
  funext y
  unfold Qprob
  by_cases h : y = x
  · subst h; simp [add_comm]
  · simp [h]

variable [Countable E] [MeasurableSingletonClass E]

/-- The uniformized law `Q(·|x,u)` as a measure on `E`. -/
noncomputable def Qmeasure (R : RateModel E U) (p : E × U) : Measure E :=
  Measure.sum fun y => ENNReal.ofReal (R.Qprob p.1 p.2 y) • Measure.dirac y

theorem measurable_Qmeasure (R : RateModel E U) : Measurable R.Qmeasure := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have h : ∀ p, R.Qmeasure p B =
      ∑' y, ENNReal.ofReal (R.Qprob p.1 p.2 y) * Measure.dirac y B := by
    intro p
    simp [Qmeasure, Measure.sum_apply _ hB]
  simp_rw [h]
  refine Measurable.tsum fun y => Measurable.mul_const ?_ _
  refine ENNReal.measurable_ofReal.comp ?_
  refine measurable_from_prod_countable_right fun x => ?_
  by_cases hyx : y = x
  · simpa [Qprob, hyx] using ((R.q_measurable x x).div_const R.lam).const_add 1
  · simpa [Qprob, hyx] using (R.q_measurable x y).div_const R.lam

/-- The kernel `Q` of the uniformized chain (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.257, PDF 268). -/
noncomputable def Q (R : RateModel E U) : Kernel (E × U) E :=
  ⟨R.Qmeasure, R.measurable_Qmeasure⟩

instance (R : RateModel E U) : IsMarkovKernel R.Q := by
  refine ⟨fun p => ⟨?_⟩⟩
  change R.Qmeasure p Set.univ = 1
  have h := ENNReal.ofReal_tsum_of_nonneg (R.Qprob_nonneg p.1 p.2) (R.hasSum_Qprob p.1 p.2).summable
  rw [(R.hasSum_Qprob p.1 p.2).tsum_eq, ENNReal.ofReal_one] at h
  have h2 : R.Qmeasure p Set.univ = ∑' y, ENNReal.ofReal (R.Qprob p.1 p.2 y) := by
    simp [Qmeasure, Measure.sum_apply _ MeasurableSet.univ]
  rw [h2, ← h]

/-- `∑_{y ∈ E} q_{xy}(u) v(y)` for `v` with values in `[-∞, ∞)`, the sum of (8.10) (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.257,
PDF 268).

**Formalization Note** The diagonal term `q_{xx}(u) v(x)` carries a nonpositive coefficient and
the off-diagonal terms are an integral of `v` against the nonnegative rates. The sum is meaningful
when `v(x) > -∞`: with `v(x) = -∞` and `q_{xx}(u) < 0` it is of the form `∞ - ∞` in the book. -/
noncomputable def rateSum (R : RateModel E U) (v : E → EReal) (x : E) (u : U) : EReal :=
  (R.q x x u : EReal) * v x +
    MDPFinance.PDMDP.erealIntegral
      (Measure.sum fun y => if y = x then 0 else ENNReal.ofReal (R.q x y u) • Measure.dirac y) v

/-- The function `u ↦ r(x,u) + ∑_y q_{xy}(u) v(y)` of Theorems 8.3.1 and 8.3.3 and of (8.10)
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.257–261, PDF 268–272). -/
noncomputable def rateObjective (R : RateModel E U) (v : E → EReal) (x : E) (u : U) : EReal :=
  ((R.r (x, u) : ℝ) : EReal) + R.rateSum v x u

/-- The continuity and compactness assumptions of Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.3.1, p.257, PDF 268:
(i) `U` is compact, (ii) `u ↦ q_{xy}(u)` is continuous for all `x, y ∈ E`,
(iii) `u ↦ ∑_{y ∈ E} b(y) q_{xy}(u)` is continuous for all `x ∈ E`,
(iv) `u ↦ r(x,u)` is upper semicontinuous for all `x ∈ E`. -/
structure ContinuityCompactness [TopologicalSpace U] (R : RateModel E U) (b : E → ℝ) : Prop where
  compact : CompactSpace U
  q_continuous : ∀ x y, Continuous (R.q x y)
  bound_continuous : ∀ x, Continuous fun u => ∑' y, b y * R.q x y u
  r_usc : ∀ x, UpperSemicontinuous fun u => R.r (x, u)

end RateModel

end BauerleRiederMDP.PDMDP


