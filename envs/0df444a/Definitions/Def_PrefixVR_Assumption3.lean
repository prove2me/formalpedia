-- Prove2me | Definitions.Def_PrefixVR_Assumption3
-- name    : PrefixVR_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:49.345148+00:00
-- url     : https://prove2.me/theorems/7c0a2578-ec29-4af8-865a-64642b5c5c31
-- title:
--   Assumption 3: $f$ is $L_f$-smooth and (2) holds with $\delta\ge0$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ with gradient maps $g_i$, and $f=\frac1n\sum_{i=1}^n f_i$. **Assumption 3** with constants $L_f$ and $\delta$ holds if
--
--   1. every $f_i$ is differentiable with $\nabla f_i(x)=g_i(x)$ for all $x$;
--   2. $L_f>0$ and the average function $f$ is $L_f$-smooth: it is differentiable with gradient $\nabla f=\frac1n\sum_i g_i$ and $\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|$ for all $x,y$;
--   3. $\delta\ge0$ and condition (2) holds:
--   $$
--   \frac1n\sum_{i=1}^n\|\nabla f_i(x)-\nabla f_i(y)-\nabla f(x)+\nabla f(y)\|^2\le\delta^2\|x-y\|^2\qquad\text{for all }x,y.
--   $$
--
--   It separates the smoothness of the average objective from the error introduced by sampling a gradient difference, and replaces the component smoothness of Assumption 1 in the refined analysis.
--
--   **Formalization Note** $L_f$-smoothness is the published `ConvexOptAlg.SmoothGD.IsBetaSmooth` and $f$ is the published `KatyushaNs.favg`. Clause 1 makes explicit that the gradients $\nabla f_i$ named in (2) exist; it forces the gradient of $f$ to be the average of the $g_i$, so clause 2 adds nothing beyond "$f$ is $L_f$-smooth".
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), Assumption 3, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation

namespace PrefixVR

/-- **Assumption 3.** Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), Assumption 3,
p.4: "The average function f is L_f-smooth, where L_f > 0. For some δ ≥ 0 and all x, y ∈ ℝᵈ,
(2) holds."

`Assumption3 fi g Lf δ` says: each component `fi i` has gradient `g i x` at every `x` (the
gradients `∇fᵢ` named in (2) exist); `Lf > 0`; the average `f = (1/n) ∑ᵢ fᵢ` is `Lf`-smooth with
gradient map `gradAvg g` (differentiable with `Lf`-Lipschitz gradient, the published
`ConvexOptAlg.SmoothGD.IsBetaSmooth`); `δ ≥ 0`; and (2) holds (`Variation g δ`).

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, components are `Fin n`, and
`f = KatyushaNs.favg fi`. Since each `fi i` has gradient `g i x`, the gradient of `f` is
necessarily `gradAvg g x`, so the smoothness clause adds no condition beyond "f is
`Lf`-smooth". -/
def Assumption3 {n d : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf δ : ℝ) : Prop :=
  (∀ i x, HasGradientAt (fi i) (g i x) x) ∧ 0 < Lf ∧
    ConvexOptAlg.SmoothGD.IsBetaSmooth (KatyushaNs.favg fi) (gradAvg g) Lf ∧
    0 ≤ δ ∧ Variation g δ

end PrefixVR


