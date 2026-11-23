-- Prove2me | Definitions.Def_StochConvexProg_FirstStage_Supplement_EpsSolutions
-- name    : StochConvexProg_FirstStage_Supplement_EpsSolutions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:56:42.656043+00:00
-- url     : https://prove2.me/theorems/3a2845fd-ca45-4130-808b-9f36e458361d
-- title:
--   ε-solutions M(ε) of the dual D and the ε-subgradient set ∂_εφ(0) (pp. 192–193)
-- statement:
--   This file adds the two sets that appear in Theorem 4 of Rockafellar and Wets on top of the published duality layer of the two-stage stochastic convex program. There $U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$ is paired with $Y=\mathbb R^{m_1}\times\mathcal L^1_{m_2}$ by
--   $$\langle u,y\rangle=u_1\cdot y_1+\int_S u_2(s)\cdot y_2(s)\,\sigma(ds),$$
--   $g(y)=\inf_{x\in X}L(x,y)$ is the dual objective, $\sup\mathbf D=\sup_{y\in Y}g(y)$, and $\varphi(u)=\inf_{x\in X}F(x,u)$ is the perturbation function, all with values in $[-\infty,+\infty]$.
--
--   1. For $\varepsilon>0$, an element $y\in Y$ is an **$\varepsilon$-solution** to the dual $\mathbf D$ if it yields the maximum in $\mathbf D$ to within $\varepsilon$. The set of $\varepsilon$-solutions is
--   $$M(\varepsilon)=\{\,y\in Y \mid g(y)\ge \sup\mathbf D-\varepsilon\,\}.$$
--   2. For a function $\varphi:U\to[-\infty,+\infty]$ and $\varepsilon>0$, the **$\varepsilon$-subgradient set** of $\varphi$ at $0$ is
--   $$\partial_\varepsilon\varphi(0)=\{\,y\in Y \mid \varphi(u)\ge[\varphi(0)-\varepsilon]+\langle u,y\rangle\ \text{ for all } u\in U\,\}.$$
--
--   These are the objects through which Theorem 4 expresses the directional derivatives of $\varphi$ at $0$ without assuming that the dual problem has a solution.
--
--   **Formalization Note** Both sets are defined for every real $\varepsilon$; only $\varepsilon>0$ is used. Values are in `EReal`, and $\sup\mathbf D-\varepsilon$ and $\varphi(0)-\varepsilon$ are `EReal` subtraction of a real number. Under the hypotheses of Theorem 4, $\sup\mathbf D$ and $\varphi(0)$ are finite, so no infinite-arithmetic convention is involved. The pairing is the published `pairUY`.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 192 (Corollary 2: ε-solution 'yields the maximum in D(u) to within ε'; Theorem 4: M(ε)) and p. 193 (proof of Theorem 4: ∂_εφ(0))

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory StochConvexProg.Duality

namespace StochConvexProg.FirstStage.Supplement

/-- Rockafellar–Wets (1976), p. 192 (Corollary 2 and Theorem 4): `M(ε)`, the set of `ε`-solutions
to the dual `D`, i.e. the `y ∈ Y` that yield the maximum in `D` to within `ε`:
`M(ε) = {y ∈ Y | g(y) ≥ sup D − ε}`. -/
noncomputable def epsSolutions {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (ε : ℝ) : Set (YSpace σ m₁ m₂) :=
  {y | pr.supD - (ε : EReal) ≤ pr.dualObj y}

/-- Rockafellar–Wets (1976), p. 193 (proof of Theorem 4): the `ε`-subgradient set `∂_εφ(0)` of a
function `φ : U → R ∪ {±∞}` at `0`, with respect to the pairing (1.6): the `y ∈ Y` such that
`φ(u) ≥ [φ(0) − ε] + ⟨u, y⟩` for all `u ∈ U`. -/
noncomputable def epsSubdiffZero {S : Type*} [MeasurableSpace S] {σ : Measure S} {m₁ m₂ : ℕ}
    (φ : USpace σ m₁ m₂ → EReal) (ε : ℝ) : Set (YSpace σ m₁ m₂) :=
  {y | ∀ u : USpace σ m₁ m₂, (φ 0 - (ε : EReal)) + ((pairUY u y : ℝ) : EReal) ≤ φ u}

end StochConvexProg.FirstStage.Supplement


