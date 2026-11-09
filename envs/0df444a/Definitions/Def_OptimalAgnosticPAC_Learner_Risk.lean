-- Prove2me | Definitions.Def_OptimalAgnosticPAC_Learner_Risk
-- name    : OptimalAgnosticPAC_Learner_Risk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:28.818044+00:00
-- url     : https://prove2.me/theorems/e11ab9eb-0837-4b81-9e60-1b43efd61a70
-- title:
--   §§1–3 — risks, the empirical optimum, traces and leave-one-out rules
-- statement:
--   Let $P$ be a distribution on $\mathcal X\times\{-1,+1\}$. The risk of a classifier $h$ is $L(h)=\mathbb P(h(X)\ne Y)$. With $\ell(a,y)=|a-y|/2$, the risk of a score $g:\mathcal X\to[-1,1]$ is
--   $$L(g)=\mathbb E\,\ell(g(X),Y)=\tfrac12\mathbb E|g(X)-Y|,$$
--   the risk of the randomized predictor that outputs $+1$ with probability $(1+g(x))/2$. The two risks agree on $\{-1,+1\}$-valued maps.
--
--   For a class $\mathcal H$, $L^*=\min_{h\in\mathcal H}L(h)$, and footnote 1 of the paper assumes this minimum is attained. For a labeled sequence $S=((x_i,y_i))_{i=1}^n$,
--   $$\widehat L^*_S=\frac1n\min_{h\in\mathcal H}\sum_{i=1}^n\mathbf 1\{h(x_i)\ne y_i\},\qquad \widehat L^{\mathrm{LOO}}_S=\frac1n\sum_{i=1}^n\mathbf 1\{\widehat y_i\ne y_i\},$$
--   where a leave-one-out rule observes all inputs and all labels except $y_i$ when predicting $\widehat y_i$. The trace of $\mathcal H$ on $x_1,\dots,x_m$ is $\{(h(x_1),\dots,h(x_m)):h\in\mathcal H\}$.
--
--   The class is called trace measurable when, for every $m$, the map sending $(x_1,\dots,x_m)$ to this trace is measurable. It is this mission's reading of the paper's assumption that all maps depending on the data are measurable.
--
--   **Formalization Note** Samples are functions on `Fin n`, and the i.i.d. law is the product measure. The infimum defining $L^*$ is taken over a set of numbers in $[0,1]$. It has the junk value $0$ on an empty class, which attainment excludes. The score risk is a Bochner integral: every score it is applied to in this mission is measurable with values in $[-1,1]$, so the integrand is integrable.
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §1 and footnote 1, PDF p. 2 (printed p. 1); §2, PDF pp. 6–7 (printed pp. 5–6); §3, PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

variable {X : Type}

/-- The classifier risk `L(h) = P(h(X) ≠ Y)` (PDF p. 2), for a distribution `P` on
`X × {-1,+1}`, with `Bool` labels (`true` is `+1`). All classifiers to which it is applied in this
mission are measurable, so the set is measurable. -/
noncomputable def risk [MeasurableSpace X] (P : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  P.real {z | h z.1 ≠ z.2}

/-- `ℓ(a, y) = |a - y| / 2` (PDF p. 8). -/
noncomputable def loss (a : ℝ) (y : Bool) : ℝ := |a - sgn y| / 2

/-- The risk of a score `g : X → [-1,1]` (PDF p. 8): `L(g) = E ℓ(g(X), Y) = E |g(X) - Y| / 2`.
This is the risk of the randomized predictor with conditional mean `g`, not the 0-1 risk of the
sign of `g`. All scores to which it is applied in this mission are measurable with values in
`[-1,1]`, so the integrand is bounded and measurable, hence integrable. -/
noncomputable def scoreRisk [MeasurableSpace X] (P : Measure (X × Bool)) (g : X → ℝ) : ℝ :=
  ∫ z, loss (g z.1) z.2 ∂P

/-- `L* = min_{h ∈ H} L(h)` (PDF p. 2), written as the infimum of the risks. Risks lie in `[0,1]`,
so the set is bounded below; on an empty `H` the value is the junk `0`, which `AttainsMinRisk`
excludes wherever `L*` is used as a minimum. Lemma 3.3 uses the same object as
`inf_{h ∈ T_p} L(h)` on the nonempty class `T_p`. -/
noncomputable def minRisk [MeasurableSpace X] (P : Measure (X × Bool)) (H : Set (X → Bool)) : ℝ :=
  sInf (risk P '' H)

/-- Footnote 1 of the paper (PDF p. 2): the minimum defining `L*` is attained. -/
def AttainsMinRisk [MeasurableSpace X] (P : Measure (X × Bool)) (H : Set (X → Bool)) : Prop :=
  ∃ h ∈ H, risk P h = minRisk P H

/-- The law of an i.i.d. sample of size `n` from `P`. -/
noncomputable def sampleLaw [MeasurableSpace X] (P : Measure (X × Bool)) [SigmaFinite P] (n : ℕ) :
    Measure (Fin n → X × Bool) :=
  Measure.pi (fun _ => P)

/-- `∑_i 1{h(x_i) ≠ y_i}`, the number of errors of `h` on the labeled sequence `S`. -/
noncomputable def errCount {n : ℕ} (h : X → Bool) (S : Fin n → X × Bool) : ℕ :=
  (Finset.univ.filter (fun i => h (S i).1 ≠ (S i).2)).card

/-- `L̂*_S = (1/n) min_{h ∈ H} ∑_i 1{h(x_i) ≠ y_i}` (PDF p. 6). For nonempty `H` the
natural-number infimum is an attained minimum; every statement using it has `H` nonempty and
`n ≥ 1`. -/
noncomputable def empMinRisk {n : ℕ} (H : Set (X → Bool)) (S : Fin n → X × Bool) : ℝ :=
  (sInf ((fun h => errCount h S) '' H) : ℕ) / n

/-- The trace `{(h(x_1), …, h(x_m)) : h ∈ H}` of `H` on a sequence (PDF p. 7). -/
def trace {m : ℕ} (H : Set (X → Bool)) (x : Fin m → X) : Set (Fin m → Bool) :=
  {f | ∃ h ∈ H, f = fun i => h (x i)}

/-- The measurability reading of footnote 1 of the paper ("all maps depending on the data are
measurable") as a condition on the class: for every `m`, the map sending a sequence of `m` points
to the trace of `H` on it is measurable, the codomain being a finite set of subsets. -/
def TraceMeasurable [MeasurableSpace X] (H : Set (X → Bool)) : Prop :=
  ∀ (m : ℕ) (T : Set (Fin m → Bool)), MeasurableSet {x : Fin m → X | trace H x = T}

/-- A leave-one-out rule on `n` indices (PDF p. 6): `rule i y` is the prediction `ŷ_i`, and it
observes all labels except `y_i`, i.e. it does not depend on the value of `y i`. The dependence on
the inputs is expressed by choosing the rule after the input sequence. -/
def IsLOORule {n : ℕ} (rule : Fin n → (Fin n → Bool) → Bool) : Prop :=
  ∀ (i : Fin n) (y y' : Fin n → Bool), (∀ j, j ≠ i → y j = y' j) → rule i y = rule i y'

/-- `L̂^LOO_S = (1/n) ∑_i 1{ŷ_i ≠ y_i}` (PDF p. 6). -/
noncomputable def looRisk {n : ℕ} (rule : Fin n → (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter (fun i => rule i y ≠ y i)).card : ℝ) / n

end OptimalAgnosticPAC.Learner


