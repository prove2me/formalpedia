-- Prove2me | Definitions.Def_MatroidProphetKW_RankOne_Supplement_ValueDist
-- name    : MatroidProphetKW_RankOne_Supplement_ValueDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:04:34.094009+00:00
-- url     : https://prove2.me/theorems/5375e3a3-ca4f-4be8-bc46-7816e13c33df
-- title:
--   §6, p. 11 — value distributions with a positive density on an interval, virtual valuations φ_x, regularity, φ_x^{-1}
-- statement:
--   These are the single-service primitives of the Bayesian unit-demand mechanism design setting of §6.
--
--   1. **Value distribution.** The value $v_x$ of a service $x$ is supported on an interval $I_x\subseteq\mathbb R$, which may be unbounded and may contain negative numbers. Its distribution function $F_x$ has a density $f_x$ that is measurable and strictly positive on $I_x$; the law of $v_x$ is the measure with density $f_x$ on $I_x$ and no mass outside, and it has total mass $1$. We write $F_x(v)=\Pr[v_x\le v]$.
--   2. **Virtual valuation.** On $I_x$,
--   $$\varphi_x(v)=v-\frac{1-F_x(v)}{f_x(v)}.$$
--   3. **Regularity.** The distribution is *regular* when $\varphi_x$ is monotonically increasing (non-decreasing) on $I_x$.
--   4. **Inverse virtual valuation.** For a real $t$, $\varphi_x^{-1}(t)=\inf\{v\in I_x:\varphi_x(v)\ge t\}$, and $\varphi_x^{-1}(t)=+\infty$ when no value of $I_x$ reaches $t$. This is the price function of the mechanisms.
--   5. **Weight law.** The law of the clipped virtual value $\max(\varphi_x(v_x),0)$. It is the weight distribution handed to the prophet-inequality algorithm that sets the thresholds $T(A,x)$.
--   6. **Prior and type space.** For services $x\in\mathcal U$, the values are independent, $v=(v_x)_x$ having the product law; the type space is $\prod_x I_x$.
--
--   These objects let the mechanisms of §6 translate thresholds on virtual values into posted prices.
--
--   **Formalization Note** `ValueDist` records the interval `I` (order-connected, hence measurable), the density `f` and the normalisation $\int_I f=1$. `phi` is evaluated outside `I` only on a null set. `phiInv` takes values in `WithTop ℝ`; the infimum is real-valued whenever the set is nonempty, because $\varphi_x(v)\le v$ on $I_x$ makes it bounded below by $t$. The paper states virtual values without a sign; the weight law clips them at $0$ because the prophet-inequality algorithms of §§2–4 take non-negative weights.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 11, §6 (density f_x positive on the support interval, φ_x, regularity); pp. 12–14, Algorithms 1–3 (φ_x^{-1}, the weights w(x) = φ_x(v_x))

import Mathlib

namespace MatroidProphetKW.RankOne.Supplement

open MeasureTheory

/-- A value distribution of §6 (Kleinberg–Weinberg, *Matroid Prophet Inequalities*,
arXiv:1201.4764v1, p. 11): the value `v_x` is supported on an interval `I ⊆ ℝ` (possibly
unbounded, possibly containing negative numbers), and its distribution function `F_x` has a
density `f_x` that is well defined (measurable) and positive on `I`. The law of the value is the
measure with density `f` on `I` and no mass outside `I`; `total` says that it is a probability
measure. -/
structure ValueDist where
  /-- the support interval of the value -/
  I : Set ℝ
  I_interval : I.OrdConnected
  /-- the density `f_x` -/
  f : ℝ → ℝ
  f_measurable : Measurable f
  f_pos : ∀ v ∈ I, 0 < f v
  total : ∫⁻ v in I, ENNReal.ofReal (f v) = 1

namespace ValueDist

/-- The law of the value: density `f` on the support interval `I`, no mass outside. -/
noncomputable def law (D : ValueDist) : Measure ℝ :=
  (volume.restrict D.I).withDensity (fun v => ENNReal.ofReal (D.f v))

instance (D : ValueDist) : IsProbabilityMeasure D.law :=
  ⟨by rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact D.total⟩

/-- The distribution function `F_x(v) = Pr[v_x ≤ v]`. -/
noncomputable def cdf (D : ValueDist) (v : ℝ) : ℝ := D.law.real (Set.Iic v)

/-- The virtual valuation `φ_x(v) = v − (1 − F_x(v)) / f_x(v)` (§6, p. 11). It is meaningful on
the support interval `I`, where `f_x > 0`. -/
noncomputable def phi (D : ValueDist) (v : ℝ) : ℝ := v - (1 - D.cdf v) / D.f v

/-- Regularity (§6, p. 11): the virtual valuation function `φ_x` is monotonically increasing
(non-decreasing) on the support interval. -/
def Regular (D : ValueDist) : Prop := MonotoneOn D.phi D.I

/-- The inverse virtual valuation `φ_x^{-1}(t)` used for prices (Algorithms 1–3, pp. 12–14), as a
generalized inverse: the infimum of the values `v ∈ I` with `φ_x(v) ≥ t`, and `+∞` (`⊤`) when there
is no such value. -/
noncomputable def phiInv (D : ValueDist) (t : ℝ) : WithTop ℝ := by
  classical
  exact if {v | v ∈ D.I ∧ t ≤ D.phi v}.Nonempty then
      ((sInf {v | v ∈ D.I ∧ t ≤ D.phi v} : ℝ) : WithTop ℝ)
    else ⊤

lemma measurable_cdf (D : ValueDist) : Measurable D.cdf := by
  refine Monotone.measurable ?_
  intro a b hab
  exact measureReal_mono (Set.Iic_subset_Iic.2 hab)

lemma measurable_phi (D : ValueDist) : Measurable D.phi := by
  unfold phi
  exact measurable_id.sub ((measurable_const.sub D.measurable_cdf).div D.f_measurable)

/-- The law of the weight `w(x) = max(φ_x(v_x), 0)` that the prophet-inequality algorithm embedded
in the mechanisms sees (§6, p. 12): the image of the value law under the clipped virtual
valuation. -/
noncomputable def wLaw (D : ValueDist) : Measure ℝ :=
  D.law.map (fun v => max (D.phi v) 0)

instance (D : ValueDist) : IsProbabilityMeasure D.wLaw :=
  Measure.isProbabilityMeasure_map (D.measurable_phi.max measurable_const).aemeasurable

end ValueDist

/-- The prior of §6 (p. 11): the values `v_x`, `x ∈ 𝒰`, are independent, `v_x ∼ D x`. -/
noncomputable def prior {α : Type*} [Fintype α] (D : α → ValueDist) : Measure (α → ℝ) :=
  Measure.pi (fun x => (D x).law)

/-- The type space: value profiles with every `v_x` in its support interval. -/
def typeSpace {α : Type*} (D : α → ValueDist) : Set (α → ℝ) := {v | ∀ x, v x ∈ (D x).I}

end MatroidProphetKW.RankOne.Supplement


