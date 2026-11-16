-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Supplement_Priors
-- name    : MatrixSenseRank_Testing_Supplement_Priors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:06:53.789686+00:00
-- url     : https://prove2.me/theorems/9776eae9-50af-4a2b-85df-5ae16d48cc9b
-- title:
--   Definition 6 — target priors and shared-target sample laws
-- statement:
--   In dimension $n\ge2$, normalize a standard Gaussian vector to obtain a uniform unit vector $u$. Applying Gram–Schmidt to two independent standard Gaussian vectors gives a Haar orthonormal pair $(u_1,u_2)$. Define
--
--   $$ A_{\rm yes}=uu^\top,\qquad A_{\rm no}=\frac{u_1u_1^\top+u_2u_2^\top}{\sqrt2}. $$
--
--   Their pushforward laws are $D_{\rm yes}$ and $D_{\rm no}$. To generate $P_{\Pi,T}$, draw one target $A\sim\Pi$ and then $T$ independent full-Gaussian matrices, returning all $(X^{(t)},\langle A,X^{(t)}\rangle)$ with that same target. The null law $Q_T$ draws independent full-Gaussian designs and independent standard normal labels.
--
--   These constructions are the two target mixtures in the linear sample lower bound. Gaussian normalization at zero and Gram–Schmidt at a zero residual return zero only on null sets in the stated dimensions; they do not add zero matrices to the topological support.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Definition 6 and §4.2, printed p. 13–14, PDF p. 14–15 (1-based).

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Supplement_Experiments
import Definitions.Def_MatrixSenseRank_Testing_Supplement_Divergences

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatrixSenseRank.Testing.Supplement

/-- Gaussian normalization constructs normalized surface probability (positive dimension).
Its value at zero is zero, on a Gaussian null set. -/
noncomputable def unitDirection {n : ℕ} (g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => g i / vectorNorm g

/-- Gram--Schmidt on two independent normals constructs the Haar orthonormal pair for n>=2.
The zero residual receives zero on a null set; no conditional density is replaced by a point mass. -/
noncomputable def secondDirection {n : ℕ} (g h : Fin n → ℝ) : Fin n → ℝ :=
  let u := unitDirection g
  unitDirection (fun i => h i - (∑ j, u j * h j) * u i)

def outer {n : ℕ} (u : Fin n → ℝ) : Mat n n := fun i j => u i * u j

noncomputable def noTarget {n : ℕ} (p : (Fin n → ℝ) × (Fin n → ℝ)) : Mat n n :=
  (Real.sqrt 2)⁻¹ • (outer (unitDirection p.1) + outer (secondDirection p.1 p.2))

/-- Definition 6: one sampled target, subsequently shared across observations. -/
noncomputable def yesPrior (n : ℕ) : Measure (Mat n n) :=
  Measure.map (fun g : Fin n → ℝ => outer (unitDirection g))
    (coordinateLaw (gaussianReal 0 1) n)

noncomputable def noPrior (n : ℕ) : Measure (Mat n n) :=
  Measure.map noTarget ((coordinateLaw (gaussianReal 0 1) n).prod
    (coordinateLaw (gaussianReal 0 1) n))

/-- Joint pushforward: sample A ONCE, then independent designs. This is not the product
of the one-observation marginal mixture, which would redraw A each time. -/
noncomputable def priorSamples {n : ℕ} (prior : Measure (Mat n n)) (T : ℕ) :
    Measure (Fin T → Observation n n) :=
  Measure.map (fun p : Mat n n × (Fin T → Mat n n) =>
      fun t => (p.2 t, frobeniusInner p.1 (p.2 t)))
    (prior.prod (Measure.pi (fun _ : Fin T => fullGaussian n n)))

noncomputable def nullSamples (n T : ℕ) : Measure (Fin T → Observation n n) :=
  Measure.pi (fun _ : Fin T => (fullGaussian n n).prod (gaussianReal 0 1))

end MatrixSenseRank.Testing.Supplement


