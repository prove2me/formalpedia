-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Blocks
-- name    : OAI_Probability_GaussianRegression_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:10:35.6128+00:00
-- url     : https://prove2.me/theorems/5f80d843-a9ef-49af-8316-fa39a89a28d2
-- title:
--   Polynomial ball-mass bounds, localized rescaling of a measure, and block values of finite routing rules
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\gamma_E$ be its standard Gaussian measure (the law of $\sum_i g_ie_i$ for an orthonormal basis $(e_i)$ and independent standard normal $g_i$), and write $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$. The file defines:
--
--   1. **Polynomial mass bound.** A measure $\nu$ on $E$ satisfies the polynomial mass bound with exponent $a\in\mathbb{N}$ and constant $C\in[0,\infty]$ if
--      $$\nu\big(\bar B(z,r)\big)\le C\,r^{a}\qquad\text{for all }z\in E\text{ and all }r>0 .$$
--      All centers are allowed, not only points of the support.
--
--   2. **Localized measure.** For $\nu$, $a$, $C$ as above, a center $z\in E$ and a radius $r\in\mathbb{R}$, the measure $\nu^{(z,r)}$ on $E$ given on measurable sets $B\subseteq E$ by
--      $$\nu^{(z,r)}(B)=\big(C\,r^{a}\big)^{-1}\,\nu\Big(\big\{x\in\bar B(z,r):\ r^{-1}(x-z)\in B\big\}\Big).$$
--      It is the restriction of $\nu$ to $\bar B(z,r)$, transported to the unit ball by the affine map $x\mapsto r^{-1}(x-z)$ and divided by the a-priori bound $C\,r^{a}$ on its mass.
--
--   3. **Block value.** For a finite set $J$, weights $h_j:E\to[0,\infty]$ indexed by $j\in J$, a block length $m\in\mathbb{N}$ and a selection rule $\varphi:E^{m}\times\mathbb{R}^{m}\to J$, the block value at $s\in E$ is
--      $$\beta_{h,\varphi}(s)=\int_{E^{m}}h_{\varphi(A,\,y(A,s))}(s)\,d\gamma_E^{\otimes m}(A),\qquad y(A,s)=\big(\langle s,A_0\rangle,\dots,\langle s,A_{m-1}\rangle\big),$$
--      the expected weight selected by $\varphi$ after reading $m$ independent Gaussian rows with exact labels from $s$.
--
--   When $\nu$ satisfies a polynomial mass bound with $0<C<\infty$ and $r>0$, the localized measure $\nu^{(z,r)}$ has total mass at most $1$, is supported in the closed unit ball and satisfies $\nu^{(z,r)}(\bar B(t,\rho))\le\rho^{a}$ for all $t$ and $\rho>0$, so estimates proved for regular measures on the unit ball apply at every location and scale. Block values model a learner that reads a block of $m$ samples and moves to one of $|J|$ memory states. If each measure with density $h_j$ satisfies a polynomial mass bound, so does the measure with density $\beta_{h,\varphi}$, with the constant enlarged by a factor depending only on $\dim E$, $|J|$ and the block parameters.
--
--   **Formalization Note** The Lean names are `PolynomialMass ν a C`, `localNormalize ν a C z r` and `blockValue h φ s`. In `localNormalize` the prefactor is the inverse in $[0,\infty]$, equal to $\infty$ when $C\,r^{a}=0$, the scaling $r^{-1}$ uses Lean's convention $0^{-1}=0$, and $r^{a}$ is a natural-number power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Blocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Blocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support

namespace OAI

/-!
Localization, finite selection, and block mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

def localNormalize (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) (r : ℝ) : Measure E :=
  (C * ENNReal.ofReal (r^a))⁻¹ • (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

def blockValue {J : Type*} [Fintype J] {m : ℕ} (h : J → E → ℝ≥0∞)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) : ℝ≥0∞ :=
  ∫⁻ A, h (φ (A, fun j => ⟪s,A j⟫)) s ∂Measure.pi (fun _ : Fin m => stdGaussian E)

end Block

end NoiselessRegression

end

end OAI


