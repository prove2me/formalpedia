-- Prove2me | Definitions.Def_ActiveSaddleSGD_ActiveManifold
-- name    : ActiveSaddleSGD_ActiveManifold
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:03.746048+00:00
-- url     : https://prove2.me/theorems/94c352c6-1f99-44cb-a0db-548b457cdaf8
-- title:
--   Active manifolds, active strict saddles of order $p$, the Verdier and angle conditions, Assumption 2
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be locally Lipschitz, with Clarke subdifferential $\partial f$, and let $x^*$ be a Clarke critical point, $0\in\partial f(x^*)$.
--
--   1. $M$ is a $C^p$ **active manifold** around $x^*$ if on a neighbourhood $U$ of $x^*$, $M\cap U$ is a $C^p$ submanifold, $f$ is $C^p$ on $M\cap U$, and
--   $$
--   \inf\{\|v\|:v\in\partial f(x),\ x\in U\setminus M\}>0.
--   $$
--   2. $x^*$ is an **active strict saddle** of order $p\ge2$ if moreover there is $w\in T_{x^*}M$ with $\nabla_Mf(x^*)=0$ and $\langle w,\mathcal H_{f,M}(x^*)(w)\rangle<0$.
--   3. The **Verdier condition**: there is $C\ge0$ such that for $y\in M\cap U$, $x\in U$, $v\in\partial f(x)$,
--   $$
--   \|P_{T_yM}(v)-\nabla_Mf(y)\|\le C\|x-y\|.
--   $$
--   4. The **angle condition**: there is $\beta>0$ such that for $x\in U$, $v\in\partial f(x)$,
--   $$
--   \langle v,x-P_M(x)\rangle\ge\beta\|x-P_M(x)\|.
--   $$
--
--   **Assumption 2** says that $x^*$ is an active strict saddle of order 5 satisfying the Verdier and angle conditions. Off $M$ the subgradients are large and point away from $M$, while on $M$ the function is smooth with a direction of negative curvature.
--
--   **Formalization Note** The witnesses $k$ (the dimension), $F$, $G$, $M$, $U$, $w$, $C$, $\beta$ are explicit parameters of `Assumption2`. One open $U$ serves all conditions, and one representative $F$ on $U$ gives "$f$ is $C^p$ on $M\cap U$": each condition passes to smaller neighbourhoods, so this is the same as one neighbourhood per condition. Sharpness is a constant $c>0$ because $U\setminus M$ may be empty, the smooth case. The angle condition is required of every nearest point of $x$ in $M$. $x^*\in M$ follows from sharpness.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Definitions 3–6, pp.9–10, and Assumption 2, p.12

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ActiveSaddleSGD_ManifoldCalculus

open PathoSubgrad.Circle ProjLikeRetr.Retractor RandomGradFree.Nonsmooth
open scoped InnerProductSpace

namespace ActiveSaddleSGD

variable {d : ℕ}

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Definition 3, p.9: `M` is a `C^p` active
manifold of dimension `k` around the Clarke critical point `x*`, on the open neighbourhood `U`,
with smooth representative `F` of `f`.

**Formalization Note** "`f` is `C^p` on `M ∩ U`" is given by one representative `F`, `C^p` on `U`;
this loses nothing because `U` can be shrunk. The sharpness condition
`inf{‖v‖ : v ∈ ∂f(x), x ∈ U∖M} > 0` is stated with a constant `c > 0`, since `U∖M` may be empty
(the smooth case, `M = ℝᵈ`, p.9), where a real `sInf` would be `0`. `x* ∈ M` follows from
sharpness and `0 ∈ ∂f(x*)`. -/
structure IsActiveManifold (p k : ℕ) (f F : EuclideanSpace ℝ (Fin d) → ℝ)
    (M U : Set (EuclideanSpace ℝ (Fin d))) (xs : EuclideanSpace ℝ (Fin d)) : Prop where
  isOpen : IsOpen U
  mem : xs ∈ U
  crit : xs ∈ critSet f
  submanifold : ∀ y ∈ M ∩ U, IsSubmanifoldAt p k M y
  contDiffOn : ContDiffOn ℝ (p : WithTop ℕ∞) F U
  eqOn : Set.EqOn F f (M ∩ U)
  sharp : ∃ c > 0, ∀ x ∈ U \ M, ∀ v ∈ clarkeSubdiff f x, c ≤ ‖v‖

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Definition 4, p.9: `x*` is an active strict
saddle of order `p ≥ 2`, witnessed by the active manifold `M`, the representative `F`, an extension
`G` of `∇_M f` and the direction `w ∈ T_{x*}M`: `∇_M f(x*) = 0` and `⟨w, H_{f,M}(x*)(w)⟩ < 0`.

**Formalization Note** `G` is `C^{p-1}` on `U` and agrees with `∇_M f` on `M ∩ U`, as on p.5. -/
structure IsActiveStrictSaddle (p k : ℕ) (f F : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (M U : Set (EuclideanSpace ℝ (Fin d))) (xs w : EuclideanSpace ℝ (Fin d)) : Prop where
  two_le : 2 ≤ p
  active : IsActiveManifold p k f F M U xs
  contDiffOn_G : ContDiffOn ℝ ((p - 1 : ℕ) : WithTop ℕ∞) G U
  eqOn_G : Set.EqOn G (riemGrad M F) (M ∩ U)
  tangent : w ∈ tangentSpace M xs
  gradient_eq_zero : riemGrad M F xs = 0
  curvature_neg : ⟪w, curvOp M G xs w⟫_ℝ < 0

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Definition 5 iii), p.10: the Verdier condition
on `U`, with constant `C ≥ 0`: `‖P_{T_yM}(v) − ∇_M f(y)‖ ≤ C ‖x − y‖` for `y ∈ M ∩ U`, `x ∈ U`,
`v ∈ ∂f(x)`. -/
def VerdierCondition (f F : EuclideanSpace ℝ (Fin d) → ℝ) (M U : Set (EuclideanSpace ℝ (Fin d)))
    (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ y ∈ M ∩ U, ∀ x ∈ U, ∀ v ∈ clarkeSubdiff f x,
    ‖(tangentSpace M y).starProjection v - riemGrad M F y‖ ≤ C * ‖x - y‖

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Definition 5 iv), p.10: the angle condition
on `U`, with constant `β > 0`: `⟨v, x − P_M(x)⟩ ≥ β ‖x − P_M(x)‖` for `x ∈ U`, `v ∈ ∂f(x)`.

**Formalization Note** `P_M(x)` is the set of nearest points (p.5), and the inequality is required
of each of them. It is a singleton near `x*` by Lemma 1, and `U` can be shrunk. -/
def AngleCondition (f : EuclideanSpace ℝ (Fin d) → ℝ) (M U : Set (EuclideanSpace ℝ (Fin d)))
    (β : ℝ) : Prop :=
  0 < β ∧ ∀ x ∈ U, ∀ z, IsMetricProjection M x z → ∀ v ∈ clarkeSubdiff f x,
    β * ‖x - z‖ ≤ ⟪v, x - z⟫_ℝ

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Assumption 2, p.12, with Definitions 3–6: `x*`
is an active strict saddle of order 5 satisfying the Verdier and angle conditions.

**Formalization Note** All witnesses (`k`, `F`, `G`, `M`, `U`, `w`, `C`, `β`) are explicit, because
Assumption 3 and Lemma 4 speak of the same `M` and `β`. One neighbourhood `U` serves Definitions 3
and 5: each condition is inherited by smaller neighbourhoods, so this is the same as asking for
one `U` per condition. -/
structure Assumption2 (k : ℕ) (f F : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (M U : Set (EuclideanSpace ℝ (Fin d))) (xs w : EuclideanSpace ℝ (Fin d)) (C β : ℝ) : Prop where
  saddle : IsActiveStrictSaddle 5 k f F G M U xs w
  verdier : VerdierCondition f F M U C
  angle : AngleCondition f M U β

end ActiveSaddleSGD


