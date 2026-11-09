-- Prove2me | Definitions.Def_PhiSobBayes_IsStronglyLogConcave
-- name    : PhiSobBayes_IsStronglyLogConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:16.21728+00:00
-- url     : https://prove2.me/theorems/6fc96675-0c3f-47f4-831b-eb782af67ecf
-- title:
--   $\rho$-strongly log-concave probability measure
-- statement:
--   For $\rho\in\mathbb R$, a probability measure $\mu$ on $\mathbb R^n$ is **$\rho$-strongly log-concave** if $\mu(dx)=e^{-W(x)}\,dx$ for a twice differentiable $W:\mathbb R^n\to\mathbb R$ with $\nabla^2W\succeq\rho I_n$, that is,
--   $$\rho\,\|v\|^2\le D^2W(x)(v,v)\qquad\text{for all }x,v\in\mathbb R^n.$$
--
--   It is the conclusion of Lemma 6.1 (with $\rho=t$) and the hypothesis of the Bakry–Émery criterion (Fact A.22).
--
--   **Formalization Note** As for log-concavity: twice Fréchet differentiable $W$, density with respect to Lebesgue measure. $\mu$ is a probability measure, as the paper's measures $e^{-W}dx$ are (posteriors in Lemma 6.1; the $\Phi$-entropy is not homogeneous in the total mass).
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma 6.1, p.29 (PDF 29); Fact A.22, p.62 (PDF 62)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `μ` is a **`ρ`-strongly log-concave probability measure** on `ℝⁿ`: `μ(dx) = e^{−W(x)} dx`
with `∇²W ⪰ ρ I_n`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma 6.1, p.29 (PDF 29): "𝜇_{𝑡,𝑦} is 𝑡-strongly log-concave, that is,
𝜇_{𝑡,𝑦}(d𝑥) = 𝑒^{−𝑊(𝑥)}d𝑥 with ∇²𝑊 ⪰ 𝑡𝐼𝑛"; Fact A.22, p.62 (PDF 62).

**Formalization Note** As in `IsLogConcave`: `W` twice differentiable with
`ρ ‖v‖² ≤ D²W(x)(v, v)` for all `x, v`, density with respect to `volume`, and `μ` a probability
measure (the paper's measures `e^{−W}dx` are normalized: posteriors in Lemma 6.1, and the
Φ-entropy is not homogeneous in the total mass). -/
def IsStronglyLogConcave {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (ρ : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ W : EuclideanSpace ℝ (Fin n) → ℝ, Differentiable ℝ W ∧
    Differentiable ℝ (fderiv ℝ W) ∧ (∀ x v, ρ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x v v) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-W x)))

end PhiSobBayes


