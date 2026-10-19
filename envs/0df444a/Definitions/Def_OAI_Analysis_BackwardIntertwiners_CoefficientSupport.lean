-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
-- name    : OAI_Analysis_BackwardIntertwiners_CoefficientSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:51:37.151536+00:00
-- url     : https://prove2.me/theorems/9173c147-78a3-41ed-9381-34e956c44a88
-- title:
--   Convex envelope of a coefficient sequence and logarithmic profiles of a two-sided weight
-- statement:
--   This file attaches a convex envelope to a one-sided complex coefficient sequence and logarithmic profiles to a two-sided weight. A sequence $F:\mathbb{N}\to\mathbb{R}$ is called discretely convex if $n\mapsto F(n+1)-F(n)$ is non-decreasing.
--
--   1. **Coefficient obstacle.** For $d:\mathbb{N}\to\mathbb{C}$, $\mathcal{O}(d)=\{n\in\mathbb{N}\ :\ n>0,\ d(n)\ne0\}$ is the set of positive indices at which $d$ does not vanish.
--   2. **Coefficient envelope.** $G_d:\mathbb{N}\to\mathbb{R}$ is the convex envelope of $n\mapsto-\log|d(n)|$ on $\mathcal{O}(d)$:
--   $$G_d(n)=\sup\bigl\{F(n)\ :\ F(0)=0,\ F\text{ discretely convex},\ F(k)\le-\log|d(k)|\text{ for all }k\in\mathcal{O}(d)\bigr\}.$$
--   3. **Bounded-side tail.** For $B:\mathbb{N}\to\mathbb{R}$, $c:\mathbb{Z}\to\mathbb{C}$, $h\in\mathbb{Z}$ and $p,k\in\mathbb{N}$,
--   $$\theta_{B,c,h}(p,k)=e^{B(p)-B(p+k+1)}\,|c(h+k+1)|.$$
--   4. **Logarithmic profiles and step ratios.** For $w:\mathbb{Z}\to\mathbb{R}$, $n\in\mathbb{N}$ and $j\in\mathbb{Z}$,
--   $$Q_w(n)=-\log w(n),\qquad P_w(n)=\log w(-n),\qquad \rho_w(j)=\frac{w(j+1)}{w(j)}.$$
--
--   If $d$ has nonzero terms at arbitrarily large indices and some discretely convex $G$ with $G(0)=0$ satisfies $|d(n)|\le e^{-G(n)}$ for all $n$, then $G_d(0)=0$, $G_d$ is discretely convex, $G\le G_d$, $|d(n)|\le e^{-G_d(n)}$ for all $n$, and the bound is attained at corners: $G_d(n+2)-2G_d(n+1)+G_d(n)>0$ implies $|d(n+1)|=e^{-G_d(n+1)}$. For a positive weight $w$, the bounds $|b(j)|\le w(j)$ and $|c(j)|\,w(j)\le1$ on two-sided sequences $b,c$ become the exponential envelopes $|b(n)|\le e^{-Q_w(n)}$, $|b(-n)|\le e^{P_w(n)}$, $|c(n)|\le e^{Q_w(n)}$, $|c(-n)|\le e^{-P_w(n)}$, and for positive $w$ with $w(0)=1$ whose profiles $P_w,Q_w$ are discretely convex and eventually at least $\delta n^2$ for some $\delta>0$, the step ratios $\rho_w$ are summable over $\mathbb{Z}$. These objects feed the proof that, for quadratically decaying weights, two sequences whose correlations vanish at all positive lags have separated supports.
--
--   **Formalization Note** The names are `coefficientObstacle`, `coefficientEnvelope`, `boundedSideTail`, `positiveLog` ($Q_w$), `negativeLog` ($P_w$) and `stepRatio` ($\rho_w$). The envelope is defined through `convexEnvelope`, a real `sSup`, which is $0$ for an empty or unbounded-above set. `Real.log` satisfies $\log 0=0$ and $\log x=\log|x|$, and division by $0$ gives $0$; these conventions play no role for the strictly positive weights to which the profiles are applied.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

def coefficientObstacle (d : ℕ → ℂ) : Set ℕ := {n | 0 < n ∧ d n ≠ 0}

def coefficientEnvelope (d : ℕ → ℂ) : ℕ → ℝ :=
  convexEnvelope (coefficientObstacle d) (fun n => -Real.log ‖d n‖)

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

end CoefficientEnvelope

def boundedSideTail (B : ℕ → ℝ) (c : ℤ → ℂ) (h : ℤ) (p k : ℕ) : ℝ :=
  Real.exp (B p - B (p+k+1)) * ‖c (h+(k:ℤ)+1)‖

def positiveLog (w : ℤ → ℝ) (n : ℕ) : ℝ := -Real.log (w n)
def negativeLog (w : ℤ → ℝ) (n : ℕ) : ℝ := Real.log (w (-(n:ℤ)))
def stepRatio (w : ℤ → ℝ) (j : ℤ) : ℝ := w (j+1) / w j

end
end BackwardIntertwiners

end OAI


