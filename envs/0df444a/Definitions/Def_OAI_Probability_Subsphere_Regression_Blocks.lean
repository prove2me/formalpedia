-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
-- name    : OAI_Probability_Subsphere_Regression_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:37:34.011036+00:00
-- url     : https://prove2.me/theorems/beaadb42-8bec-4ecb-9d9f-e0d40b61859e
-- title:
--   Polynomial mass bounds, local rescaling of measures, and Gaussian block values of routing maps
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\gamma_E$ be the standard Gaussian measure on $E$, and write $\overline B(z,r)=\{x\in E:\|x-z\|\le r\}$.
--
--   1. **Polynomial mass bound.** For a measure $\nu$ on $E$, an exponent $a\in\mathbb{N}$ and a constant $C\in[0,\infty]$, $\nu$ has *polynomial mass $(a,C)$* if
--   $$\nu\bigl(\overline B(z,r)\bigr)\le C\,r^{a}\qquad\text{for all } z\in E \text{ and all real } r>0 .$$
--   2. **Local normalization.** For $\nu$, $a$, $C$ as above, a centre $z\in E$ and a scale $r\in\mathbb{R}$,
--   $$\nu^{z,r}=\bigl(C\,r^{a}\bigr)^{-1}\,(T_{z,r})_*\bigl(\nu|_{\overline B(z,r)}\bigr),\qquad T_{z,r}(x)=r^{-1}(x-z):$$
--   the restriction of $\nu$ to the ball $\overline B(z,r)$, blown up around $z$ to unit scale and divided by the bound $C r^a$. For $r>0$ it lives on the closed unit ball, and when $\nu$ has polynomial mass $(a,C)$ its total mass is at most $1$.
--   3. **Block value.** For a finite set $J$, a family of functions $h:J\times E\to[0,\infty]$, a map $\varphi:E^m\times\mathbb{R}^m\to J$ (routing a block of $m$ observations to a state) and $s\in E$,
--   $$\mathrm{BV}(h,\varphi)(s)=\int_{E^m}h\Bigl(\varphi\bigl(A,(\langle s,A_j\rangle)_{j<m}\bigr),\ s\Bigr)\,d\gamma_E^{\otimes m}(A).$$
--
--   Polynomial mass bounds quantify how concentrated a measure can be at every scale and every location; the local normalization is the blow-up used to compare a measure at a small scale with a unit-scale one; and the block value is the expected value, over $m$ independent Gaussian rows with noiseless labels $\langle s,A_j\rangle$, of the weight $h$ attached to the state reached after one block, which is how the run of a streaming algorithm is decomposed into blocks.
--
--   **Formalization Note** `PolynomialMass ν a C`, `localNormalize ν a C z r` and `blockValue h φ s`. The inverse in `localNormalize` is taken in `ℝ≥0∞` (so $0^{-1}=\infty$ and $\infty^{-1}=0$), and $r^a$ is a natural power. No measurability of $h$ or $\varphi$ is assumed (the integral is a lower Lebesgue integral). The first two definitions use only the normed, linear and measurable structure of $E$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Blocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Blocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

def localNormalize (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) (r : ℝ) : Measure E :=
  (C * ENNReal.ofReal (r^a))⁻¹ • (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

def blockValue {J : Type*} [Fintype J] {m : ℕ} (h : J → E → ℝ≥0∞)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) : ℝ≥0∞ :=
  ∫⁻ A, h (φ (A, fun j => ⟪s,A j⟫)) s ∂Measure.pi (fun _ : Fin m => stdGaussian E)

end SubsphereRegression

end

end OAI


