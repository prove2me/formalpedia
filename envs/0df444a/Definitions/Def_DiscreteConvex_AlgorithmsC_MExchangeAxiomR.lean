-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_MExchangeAxiomR
-- name    : DiscreteConvex_AlgorithmsC_MExchangeAxiomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:52.22789+00:00
-- url     : https://prove2.me/theorems/bf1de323-ac01-42c3-8347-077042f02c0a
-- title:
--   Axiom (M-EXC[R])
-- statement:
--   Axiom (M-EXC[R]): $f:\mathbb{R}^V\to\mathbb{R}\cup\{+\infty\}$ is a real-domain M-convex function — for $x,y\in\operatorname{dom} f$ and $u\in\operatorname{supp}^+(x-y)$ there are $v\in\operatorname{supp}^-(x-y)$ and $\alpha_0>0$ with $f(x)+f(y)\ge f(x-\alpha(\chi_u-\chi_v))+f(y+\alpha(\chi_u-\chi_v))$ for all $0\le\alpha\le\alpha_0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3, Proposition 10.41.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3, Proposition 10.41

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomR
import Definitions.Def_DiscreteConvex_AlgorithmsC_SuppPosR
import Definitions.Def_DiscreteConvex_AlgorithmsC_SuppNegR

namespace DiscreteConvex.AlgorithmsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Axiom (M-EXC[R]): `f` is a real-domain M-convex function. Proposition 10.41 concludes that
the conjugate scaling `f⟨α⟩` is itself a dual-integral polyhedral M-convex function; the
L♮-convexity of `g_α` is Theorem 7.10 (2) and a lemma of its proof, not the proposition. -/
def MExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y, ∃ v ∈ SuppNegR x y, ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥
        g (fun w => x w - alpha * (if w = u then (1:ℝ) else 0) +
          alpha * (if w = v then (1:ℝ) else 0)) +
        g (fun w => y w + alpha * (if w = u then (1:ℝ) else 0) -
          alpha * (if w = v then (1:ℝ) else 0))

end DiscreteConvex.AlgorithmsC


