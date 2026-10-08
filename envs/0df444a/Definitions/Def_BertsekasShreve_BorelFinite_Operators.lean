-- Prove2me | Definitions.Def_BertsekasShreve_BorelFinite_Operators
-- name    : BertsekasShreve_BorelFinite_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:08.922285+00:00
-- url     : https://prove2.me/theorems/e6f5d378-c189-4153-a81e-a33936f19fbe
-- title:
--   The dynamic programming operators T_μ and T of Definitions 8.4 and 8.5
-- statement:
--   Fix a model $(S,C,U,W,p,f,\alpha,g,N)$ as in Definition 8.1, and let $J:S\to R^*$ be universally measurable. For $\mu\in U(C\mid S)$,
--   $$T_\mu(J)(x)=\int_C\Big[g(x,u)+\alpha\int_S J(x')\,t(dx'\mid x,u)\Big]\mu(du\mid x),$$
--   and
--   $$T(J)(x)=\inf_{u\in U(x)}\Big\{g(x,u)+\alpha\int_S J(x')\,t(dx'\mid x,u)\Big\},\qquad x\in S.$$
--   $J_0$ denotes the identically zero function on $S$, $T^K$ the $K$-fold composition of $T$, and $T_{\mu_0}\cdots T_{\mu_{K-1}}$ the composition in which $T_{\mu_{K-1}}$ is applied first.
--
--   These are the operators of the finite-horizon dynamic programming algorithm: the algorithm starts from $J_0$ and applies $T$ repeatedly.
--
--   **Formalization Note** Integrals are the extended integrals $\int f^+-\int f^-$ with $\infty-\infty=\infty$, and the sum inside the bracket uses the book's convention $-\infty+\infty=\infty$. The operators are defined for every $J$; the book defines them for universally measurable $J$, and theorems that need this carry it as a hypothesis.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 194–195, Definitions 8.4 and 8.5; p. 196 (definition of T^k)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy

namespace BertsekasShreve.BorelFinite

open MeasureTheory

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- The mapping `H(x, u, J) = g(x,u) + α ∫_S J(x′) t(dx′|x,u)` (p. 195), with the integral in the
extended sense (43) of Chapter 7 and the sum taken with the convention (42). -/
noncomputable def H (M : Model S C W) (J : S → EReal) (z : S × C) : EReal :=
  BertsekasShreve.FiniteHorizon.badd (M.g z) ((M.α : EReal) * extInt (fun h => ∫⁻ y, h y ∂(M.t z)) J)

/-- **Definition 8.4** (p. 194). For `μ ∈ U(C|S)` and universally measurable `J : S → R*`,
`T_μ(J)(x) = ∫_C [g(x,u) + α ∫_S J(x′) t(dx′|x,u)] μ(du|x)`. -/
noncomputable def Tmu (M : Model S C W) (μ : UCS M) (J : S → EReal) (x : S) : EReal :=
  extInt (fun h => ∫⁻ u, h u ∂(μ.1.toFun x)) (fun u => H M J (x, u))

/-- **Definition 8.5** (p. 195). For universally measurable `J : S → R*`,
`T(J)(x) = inf_{u ∈ U(x)} {g(x,u) + α ∫_S J(x′) t(dx′|x,u)}`. -/
noncomputable def T (M : Model S C W) (J : S → EReal) (x : S) : EReal :=
  ⨅ u ∈ M.U x, H M J (x, u)

/-- The identically zero function `J₀ : S → R*`. -/
noncomputable def J0 (S : Type*) : S → EReal := fun _ => 0

/-- The composition `T_{μ₀} T_{μ₁} ⋯ T_{μ_{K-1}}` (applied to `J`, the innermost operator being
`T_{μ_{K-1}}`) for a Markov policy `(μ₀, …, μ_{N-1})` and `K ≤ N`. -/
noncomputable def TmuComp (M : Model S C W) (ν : Fin M.N → UCS M) (K : ℕ) (J : S → EReal) :
    S → EReal :=
  ((List.finRange M.N).filter fun k : Fin M.N => (k : ℕ) < K).foldr (fun k J' => Tmu M (ν k) J') J

end BertsekasShreve.BorelFinite


