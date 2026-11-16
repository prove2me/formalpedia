-- Prove2me | Definitions.Def_UnknownCovDP_General_Supplement_RelPrior
-- name    : UnknownCovDP_General_Supplement_RelPrior
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:46:22.976966+00:00
-- url     : https://prove2.me/theorems/a1a09cb9-238a-41a7-a7f0-2b94c1408c9e
-- title:
--   §4, eq. (17) — the Mahalanobis norm $d_\Sigma$ and the prior $\mathcal P_{\mathrm{rel}}(d)$
-- statement:
--   Fix a dimension $d$. This module sets up the experiment of §4.
--
--   1. **Mahalanobis norm.** For a positive semidefinite $d\times d$ matrix $\Sigma$ with Moore–Penrose pseudo-inverse $\Sigma^\dagger$ and a vector $y\in\mathbb R^d$,
--   $$d_\Sigma(y)=\begin{cases}\sqrt{y^\top\Sigma^\dagger y}, & y\in\mathrm{Span}(\Sigma),\\ \infty,&\text{otherwise,}\end{cases}$$
--   where $\mathrm{Span}(\Sigma)$ is the column space of $\Sigma$.
--   2. **The prior $\mathcal P_{\mathrm{rel}}(d)$** (eq. (17)). The mean and the covariance are independent, with
--   $$\mu\sim N(0,I_d),\qquad \Sigma=I_d-vv^\top,\quad v\ \text{uniform on the unit sphere}\ \{v:\|v\|_2=1\}.$$
--
--   So $\Sigma$ is the orthogonal projector onto the hyperplane $v^\perp$, and $d_\Sigma(y)<\infty$ exactly when $y\perp v$. These objects are used by Theorem 4.1.
--
--   **Formalization Note** $d_\Sigma$ takes values in $[0,\infty]$. The pseudo-inverse is the published `LatentRobust.pinv` (the unique matrix satisfying the four Penrose conditions). The uniform direction is realized as $v=g/\|g\|_2$ with $g\sim N(0,I_d)$, whose law is rotation invariant and carried by the sphere; the null point $g=0$ is sent to $0$. The defining maps are proved measurable, so the laws are probability measures.
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, §4, definition of d_Σ and eq. (17), printed p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_UnknownCovDP_General_Model
import Definitions.Def_LatentRobust_pinv

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General.Supplement

/-!
# The Mahalanobis norm `d_Σ` and the prior `P_rel`

Gaucher, Linder, Smith, Ullman, Zakynthinou, *Dimension-Free Private Mean Estimation is Impossible
Without the Covariance*, STOC 2027 submission #573 (October 2026), §4, the definition of `d_Σ` and
eq. (17) (printed p. 27, PDF p. 28).

**Formalization Note.**
* `d_Σ(y)` takes values in `[0, ∞]`: `√(yᵀ Σ† y)` when `y ∈ Span(Σ)` (the column space of `Σ`) and
  `∞` otherwise. `Σ†` is the published Moore–Penrose inverse `LatentRobust.pinv`.
* The uniform direction `v` on the unit sphere of `ℝ^d` is realized as `g/‖g‖` with `g ∼ N(0, I_d)`,
  whose law is rotation invariant and carried by the sphere (the null event `g = 0` maps to `0`).
  The defining maps are proved measurable.
-/

/-- The Mahalanobis norm of `y` relative to `S` (§4, p. 27): `√(yᵀ S† y)` if `y ∈ Span(S)`, `∞`
otherwise. -/
noncomputable def mahalanobis {d : ℕ} (S : Mat d) (y : Vec d) : ℝ≥0∞ := by
  classical
  exact if (WithLp.ofLp y : Fin d → ℝ) ∈ LinearMap.range (Matrix.toLin' S) then
      ENNReal.ofReal (Real.sqrt ((WithLp.ofLp y : Fin d → ℝ) ⬝ᵥ
        (LatentRobust.pinv S).mulVec (WithLp.ofLp y)))
    else ⊤

/-- `g ↦ g/‖g‖` (and `0 ↦ 0`). -/
noncomputable def normalize {d : ℕ} (g : Vec d) : Vec d := ‖g‖⁻¹ • g

lemma measurable_normalize (d : ℕ) : Measurable (normalize : Vec d → Vec d) :=
  (measurable_norm.inv).smul measurable_id

/-- The uniform law on the unit sphere `{v : ‖v‖₂ = 1}` of `ℝ^d`: the law of `g/‖g‖`,
`g ∼ N(0, I_d)`. -/
noncomputable def sphereLaw (d : ℕ) : Measure (Vec d) :=
  (multivariateGaussian (0 : Vec d) (1 : Mat d)).map normalize

/-- `v ↦ I_d − v vᵀ`. -/
noncomputable def relCov {d : ℕ} (v : Vec d) : Mat d :=
  1 - Matrix.vecMulVec (WithLp.ofLp v) (WithLp.ofLp v)

lemma measurable_relCov (d : ℕ) : Measurable (relCov : Vec d → Mat d) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have h : (fun v : Vec d => relCov v i j) =
      fun v => (1 : Mat d) i j - (WithLp.ofLp v) i * (WithLp.ofLp v) j := by
    funext v; simp [relCov, Matrix.vecMulVec_apply]
  rw [h]
  exact measurable_const.sub
    (((PiLp.continuous_apply 2 _ i).mul (PiLp.continuous_apply 2 _ j)).measurable)

instance sphereLaw_prob (d : ℕ) : IsProbabilityMeasure (sphereLaw d) :=
  Measure.isProbabilityMeasure_map (measurable_normalize d).aemeasurable

/-- The `Σ`-marginal of `P_rel(d)` (eq. (17)): `Σ = I_d − v vᵀ` with `v` uniform on the unit
sphere. -/
noncomputable def relCovPrior (d : ℕ) : Measure (Mat d) :=
  (sphereLaw d).map relCov

instance relCovPrior_prob (d : ℕ) : IsProbabilityMeasure (relCovPrior d) :=
  Measure.isProbabilityMeasure_map (measurable_relCov d).aemeasurable

/-- The prior `P_rel(d)` of eq. (17): `μ ∼ N(0, I_d)` and, independently, `Σ = I_d − v vᵀ` with `v`
uniform on the unit sphere. -/
noncomputable def Prel (d : ℕ) : Measure (Vec d × Mat d) :=
  (multivariateGaussian (0 : Vec d) (1 : Mat d)).prod (relCovPrior d)

end UnknownCovDP.General.Supplement


