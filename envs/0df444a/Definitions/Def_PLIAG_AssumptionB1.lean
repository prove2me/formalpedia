-- Prove2me | Definitions.Def_PLIAG_AssumptionB1
-- name    : PLIAG_AssumptionB1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:51.747863+00:00
-- url     : https://prove2.me/theorems/ca495179-7ad1-45ca-99ee-7dd4ff1031d1
-- title:
--   Assumption B1: proper lsc convex components, $L_n$-smooth relative to $w$
-- statement:
--   **Assumption B1.** Each component function $f_n$ is proper, lower semicontinuous and convex with $\operatorname{dom}w\subseteq\operatorname{dom}f_n$, and is differentiable on $\operatorname{int}\operatorname{dom}w$. Moreover, for every $n\in\mathcal N=\{1,\dots,N\}$ the pair $(w,f_n)$ satisfies the Lipschitz-like/convexity condition: there is $L_n>0$ such that
--
--   $$
--   L_nw-f_n\ \text{is convex on }\operatorname{int}\operatorname{dom}w .
--   $$
--
--   This is relative smoothness of $f_n$ with respect to $w$; it is equivalent to $f_n(y)\le f_n(x)+\langle\nabla f_n(x),y-x\rangle+L_nD_w(y,x)$ for $x,y\in\operatorname{int}\operatorname{dom}w$, and it replaces the Lipschitz continuity of $\nabla f_n$.
--
--   **Formalization Note** The constants $L_n$ are the argument `Lc`. "Proper lsc convex" is the published `TensorAHPE.IsProperClosedConvex`. On $\operatorname{int}\operatorname{dom}w\subseteq\operatorname{dom}f_n$ both functions are finite, so differentiability and the convexity of $L_nw-f_n$ are stated for their real values there.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Assumption B1, §2.3, p.7

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_TensorAHPE_IsProperClosedConvex

namespace PLIAG

/-- **Assumption B1** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, §2.3, p.7). Each component `f_n` is
proper lsc convex with `dom w ⊆ dom f_n`, differentiable on `int dom w`, and the pair `(w, f_n)`
satisfies the Lipschitz-like/convexity condition: there is `L_n > 0` such that `L_n w − f_n` is
convex on `int dom w`. The constants `L_n` are the argument `Lc`.

**Formalization Note.** Values are `EReal`; "proper lsc convex" is the published
`TensorAHPE.IsProperClosedConvex`. On `int dom w ⊆ dom f_n` both `w` and `f_n` are finite, so
differentiability and the convexity of `L_n w − f_n` there are stated for the real functions
`(w ·).toReal`, `(f_n ·).toReal`, which agree with `w`, `f_n` on that set. -/
def AssumptionB1 {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (Lc : Fin N → ℝ) : Prop :=
  ∀ n, TensorAHPE.IsProperClosedConvex (f n) ∧ AubinLipschitz.effDom w ⊆ AubinLipschitz.effDom (f n) ∧
    DifferentiableOn ℝ (fun x => (f n x).toReal) (interior (AubinLipschitz.effDom w)) ∧ 0 < Lc n ∧
    ConvexOn ℝ (interior (AubinLipschitz.effDom w)) (fun x => Lc n * (w x).toReal - (f n x).toReal)

end PLIAG


