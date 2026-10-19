-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
-- name    : OAI_Analysis_BackwardIntertwiners_WeightSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:52:37.047808+00:00
-- url     : https://prove2.me/theorems/dec4dea9-7d18-4935-9915-4cb21099e23a
-- title:
--   Quadratic two-sided weights and the support separation property
-- statement:
--   This file isolates a class of two-sided weights and the property of them that is used to analyse operators commuting with a weighted shift. Let $w:\mathbb{Z}\to\mathbb{R}$. A sequence $F:\mathbb{N}\to\mathbb{R}$ is discretely convex if $n\mapsto F(n+1)-F(n)$ is non-decreasing.
--
--   1. **Quadratic weights.** $w$ is a quadratic weight if all of the following hold:
--      - $w(j)>0$ for every $j\in\mathbb{Z}$, and $w$ is non-increasing on $\mathbb{Z}$;
--      - $n\mapsto\log w(-n)$ and $n\mapsto-\log w(n)$ are discretely convex on $\mathbb{N}$;
--      - the root series converges, $\sum_{j\in\mathbb{Z}\setminus\{0\}}w(j)^{1/j}<\infty$;
--      - there is a constant $a>\log 3$ with
--   $$\lim_{n\to\infty}\frac{\log w(n)}{n^2}=-a,\qquad\lim_{n\to\infty}\frac{\log w(-n)}{n^2}=a.$$
--      Thus $w$ decays like $e^{-an^2}$ to the right and grows like $e^{an^2}$ to the left.
--   2. **Support separation.** $w$ has the support separation property if for all $b,c:\mathbb{Z}\to\mathbb{C}$, neither identically zero, satisfying
--   $$|b(j)|\le w(j),\qquad |c(j)|\,w(j)\le1\qquad(j\in\mathbb{Z}),$$
--   and whose correlations vanish at every positive lag,
--   $$\sum_{j\in\mathbb{Z}}b(j)\,c(j-r)=0\qquad(r=1,2,3,\dots),$$
--   there exist $t,h\in\mathbb{Z}$ with $b(t)\ne0$, $c(h)\ne0$, $b(j)=0$ for all $j>t$, $c(j)=0$ for all $j<h$, and $t\le h$. In words: the support of $b$ has a largest element, the support of $c$ has a smallest element, and the former does not exceed the latter.
--   3. **Reflected weight.** $\tilde w(j)=1/w(-j)$ for $j\in\mathbb{Z}$.
--
--   Every quadratic weight has the support separation property; this is the one-dimensional input for showing that a closed subspace invariant under the model forward weighted shift is ordered along each fiber. Reflection exchanges the two sides of $\mathbb{Z}$: the profiles $-\log\tilde w(n)$ and $\log\tilde w(-n)$ are $\log w(-n)$ and $-\log w(n)$, and if $(b,c)$ satisfies the bounds above for $w$ with vanishing positive-lag correlations, then the reflected pair $(j\mapsto c(-j),\ j\mapsto b(-j))$ satisfies them for $\tilde w$. This lets a one-sided argument be applied to both ends of the supports.
--
--   **Formalization Note** The definitions are the structure `QuadraticWeights w` (fields `positive`, `decreasing`, `convex_negative`, `concave_positive`, `root_sum`, `quadratic`), the predicate `SupportSeparation w` and the function `reflectedWeight w`. The root series is `Summable` of the function equal to $0$ at $j=0$ and to the real power $w(j)^{1/j}$ otherwise. The correlations are unconditional sums `tsum`, and Lean assigns the value $0$ to a non-summable family, so the vanishing hypothesis formally says that each correlation series either sums to $0$ or is not summable. The inverse in `reflectedWeight` satisfies $0^{-1}=0$, which is irrelevant for positive weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

structure QuadraticWeights (w : ℤ → ℝ) : Prop where
  positive : ∀ j, 0 < w j
  decreasing : Antitone w
  convex_negative : DiscreteConvex (fun n => Real.log (w (-(n : ℤ))))
  concave_positive : DiscreteConvex (fun n => -Real.log (w n))
  root_sum : Summable (fun j : ℤ => if j = 0 then 0 else w j ^ (1 / (j : ℝ)))
  quadratic : ∃ a : ℝ, Real.log 3 < a ∧
    Tendsto (fun n : ℕ => Real.log (w n) / (n : ℝ)^2) atTop (𝓝 (-a)) ∧
    Tendsto (fun n : ℕ => Real.log (w (-(n : ℤ))) / (n : ℝ)^2) atTop (𝓝 a)

def SupportSeparation (w : ℤ → ℝ) : Prop :=
  ∀ b c : ℤ → ℂ,
    (∃ j, b j ≠ 0) → (∃ j, c j ≠ 0) →
    (∀ j, ‖b j‖ ≤ w j) → (∀ j, ‖c j‖ * w j ≤ 1) →
    (∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j - r)) = 0) →
    ∃ t h : ℤ, b t ≠ 0 ∧ c h ≠ 0 ∧
      (∀ j, t < j → b j = 0) ∧ (∀ j, j < h → c j = 0) ∧ t ≤ h

def reflectedWeight (w : ℤ → ℝ) (j : ℤ) : ℝ := (w (-j))⁻¹

end
end BackwardIntertwiners

end OAI


