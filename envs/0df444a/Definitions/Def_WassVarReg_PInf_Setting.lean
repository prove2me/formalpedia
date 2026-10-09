-- Prove2me | Definitions.Def_WassVarReg_PInf_Setting
-- name    : WassVarReg_PInf_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:50.977705+00:00
-- url     : https://prove2.me/theorems/29ad79f7-7d70-4c3b-9216-901be624e435
-- title:
--   §2 and §3.4 — W∞, robust regularizer, local slope, local growth, boundary gap, Assumption 5(I)
-- statement:
--   Let $(Z,d)$ be a metric space. For probability laws $P,Q$, the **infinity-Wasserstein distance** is the infimum, over couplings $\pi$ of $P$ and $Q$, of the essential supremum of $d(\tilde z,z)$ under $\pi$. The **robust value** at radius $\rho\ge0$ is the supremum of $\mathbb E_P[f]$ over $W_\infty(P,Q)\le\rho$; the **regularizer** subtracts $\mathbb E_Q[f]$.
--
--   For a loss $f:Z\to\mathbb R$, the **local slope** and **local growth** are
--   $$
--   |\partial f|(z)=\limsup_{\tilde z\to z,\,\tilde z\ne z}\frac{(f(\tilde z)-f(z))_+}{d(\tilde z,z)},\qquad
--   G_f(\delta,z)=\sup_{d(\tilde z,z)\le\delta}\bigl(f(\tilde z)-f(z)\bigr).
--   $$
--   For a set $D\subseteq Z$, the boundary gap is $(\delta-d(z,D))_+$, with $d(z,\varnothing)=+\infty$. A finitely supported law has nonnegative weights summing to one.
--
--   **Assumption 5(I)** bounds the difference between $G_f(\delta,z)$ and $\delta|\partial f|(z)$ by $H(z)\delta^2+M(\delta-d(z,D_f))_+$ for every $f$ in the loss class, every $z$, and $0\le\delta<\delta_0$.
--
--   These definitions supply the finite-support duality and the local expansion of the robust regularizer.
--
--   **Formalization Note** Values of $W_\infty$ and the local slope lie in $[0,+\infty]$; robust values and local growth lie in the extended reals. Assumption 5(I) requires the values appearing in its real inequality to be finite. The published extended-real expectation is reused, while the finite nominal law ensures that subtracting its expectation is meaningful.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), pp. 3–4: W_p, (D), regularizer; p. 12: Definition 2 and (4); p. 13: Assumption 5(I); pp. 5–6: D_f

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace WassVarReg.PInf

/-- The order-infinity Wasserstein distance: the least essential maximal travel distance
among couplings. The infimum is in `ℝ≥0∞`, so an empty coupling set has value `⊤`. -/
noncomputable def winfDist {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    (P Q : ProbabilityMeasure Z) : ℝ≥0∞ :=
  ⨅ γ ∈ WassersteinLinOpt.Ball.couplings (P : Measure Z) (Q : Measure Z),
    essSup (fun x : Z × Z => ENNReal.ofReal (dist x.1 x.2)) γ

/-- The robust expected loss over the closed order-infinity Wasserstein ball. -/
noncomputable def worstCaseInf {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    (ρ : ℝ) (Q : ProbabilityMeasure Z) (f : Z → ℝ) : EReal :=
  ⨆ (P : ProbabilityMeasure Z) (_ : winfDist P Q ≤ ENNReal.ofReal ρ),
    WassersteinDRO.Duality.nominalRisk (P : Measure Z) f

/-- The order-infinity Wasserstein regularizer. In its uses here the nominal law is
finitely supported, so its expectation is a finite real and the subtraction is defined. -/
noncomputable def regularizerInf {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    (ρ : ℝ) (Q : ProbabilityMeasure Z) (f : Z → ℝ) : EReal :=
  worstCaseInf ρ Q f - WassersteinDRO.Duality.nominalRisk (Q : Measure Z) f

/-- A finitely supported probability law with weights `q` summing to one. -/
noncomputable def discreteLaw {Z : Type*} [MeasurableSpace Z] {m : ℕ}
    (q : Fin m → ℝ≥0) (zs : Fin m → Z) (hq : ∑ j, q j = 1) : ProbabilityMeasure Z := by
  have hsum : HasSum q 1 := by simpa [hq] using (hasSum_fintype q)
  exact ⟨Measure.sum (fun j => (q j : ℝ≥0∞) • Measure.dirac (zs j)),
    hsum.isProbabilityMeasure_sum_dirac_nnreal⟩

/-- The one-sided local slope of Definition 2. Puncturing the neighbourhood removes
the zero denominator; `ofReal` takes the positive part of the quotient. -/
noncomputable def localSlope {Z : Type*} [MetricSpace Z] (f : Z → ℝ) (z : Z) : ℝ≥0∞ :=
  Filter.limsup (fun z' => ENNReal.ofReal ((f z' - f z) / dist z' z))
    (nhdsWithin z {z}ᶜ)

/-- Local growth `G_f(δ,z)` of display (4). The extended-real supremum represents an
unbounded loss on a metric ball as `⊤`; for `δ ≥ 0`, `z` is feasible. -/
noncomputable def Gf {Z : Type*} [MetricSpace Z] (f : Z → ℝ) (δ : ℝ) (z : Z) : EReal :=
  ⨆ (z' : Z) (_ : dist z' z ≤ δ), ((f z' - f z : ℝ) : EReal)

/-- `(ρ - d(z,D))₊`, with `d(z,∅)=∞`. In particular, this is zero for the empty set. -/
noncomputable def boundaryGap {Z : Type*} [MetricSpace Z] (ρ : ℝ) (D : Set Z)
    (z : Z) : ℝ :=
  (ENNReal.ofReal ρ - Metric.infEDist z D).toReal

/-- The order-infinity clause of Assumption 5. The finiteness conditions make its
real-valued inequality meaningful even when a loss is unbounded on a metric ball. -/
def Assumption5I {Z : Type*} [MetricSpace Z] (F : Set (Z → ℝ))
    (D : (Z → ℝ) → Set Z) (H : Z → ℝ) (δ0 M : ℝ) : Prop :=
  ∀ f ∈ F, ∀ z, localSlope f z ≠ ⊤ ∧
    ∀ δ : ℝ, 0 ≤ δ → δ < δ0 → Gf f δ z ≠ ⊤ ∧
      |(Gf f δ z).toReal - (localSlope f z).toReal * δ| ≤
        H z * δ ^ 2 + M * boundaryGap δ (D f) z

end WassVarReg.PInf


