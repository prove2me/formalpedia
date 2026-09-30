-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_Cooperative
-- name    : StochFictPlay_Supermodular_Cooperative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:16:58.383856+00:00
-- url     : https://prove2.me/theorems/2918a59b-fe72-42f2-a501-bb8f2e2ca28e
-- title:
--   Cooperative and irreducible differential equations
-- statement:
--   Let $v \mapsto g(v)$ be a vector field on $\prod_\alpha \mathbb R^{n^\alpha - 1}$, whose components are indexed by pairs $(\alpha, i)$, and let $X$ be a set of states.
--
--   1. **Cooperative.** $\dot v = g(v)$ is cooperative on $X$ if
--   $$\frac{\partial g^\alpha_i}{\partial v^\beta_j}(v) \ge 0 \quad \text{for all } v \in X \text{ and all distinct pairs } (\alpha,i) \ne (\beta,j).$$
--   2. **Irreducible.** $\dot v = g(v)$ is irreducible on $X$ if for every nonempty proper subset $I$ of the components there are $(\alpha,i) \in I$ and $(\beta,j) \notin I$ such that $\partial g^\alpha_i/\partial v^\beta_j(v) \ne 0$ for all $v \in X$.
--
--   Cooperative irreducible systems are strongly monotone (Hirsch, Smith), which drives the convergence results for supermodular games.
--
--   **Formalization Note** The partial derivative is the $(\alpha,i)$ entry of the Fréchet derivative of $g$ applied to the $(\beta,j)$ basis vector. The paper's irreducibility sentence quantifies $v$ twice ("for each $v$ … for all $v$"); the uniform version stated here is the one its proof of Theorem 5.4 (p. 31) establishes, and it implies the pointwise reading.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 20 (definitions of cooperative and irreducible), p. 31 (proof of Theorem 5.4)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_StochOrder

namespace StochFictPlay.Supermodular

/-- The components `(α, i)` of a state `v ∈ ∏_α ℝ^{n^α − 1}`. -/
abbrev Comp {p : ℕ} (n : Fin p → ℕ) := Σ α : Fin p, Fin (n α - 1)

/-- The partial derivative `∂g^α_i / ∂v^β_j (v)` of a field `g` on `∏_α ℝ^{n^α − 1}`, at `v`,
for `a = (α, i)` and `b = (β, j)`: the `a`-coordinate of the Fréchet derivative of `g` at `v`
applied to the basis vector of coordinate `b`. -/
noncomputable def partialDeriv {p : ℕ} {n : Fin p → ℕ} (g : Coord n → Coord n) (v : Coord n)
    (a b : Comp n) : ℝ :=
  fderiv ℝ g v (Pi.single b.1 (Pi.single b.2 (1 : ℝ))) a.1 a.2

/-- Cooperative differential equation `v̇ = g(v)` on `X` (manuscript p. 20):
`∂g^α_i/∂v^β_j (v) ≥ 0` for all `v ∈ X` and all distinct pairs `(α, i)` and `(β, j)`. -/
def IsCooperative {p : ℕ} {n : Fin p → ℕ} (g : Coord n → Coord n) (X : Set (Coord n)) : Prop :=
  ∀ v ∈ X, ∀ a b : Comp n, a ≠ b → 0 ≤ partialDeriv g v a b

/-- Irreducible differential equation `v̇ = g(v)` on `X` (manuscript p. 20), in the uniform form
proved on p. 31: for each nonempty proper subset `I` of the components there are `(α, i) ∈ I`
and `(β, j) ∉ I` such that `∂g^α_i/∂v^β_j (v) ≠ 0` for all `v ∈ X`. -/
def IsIrreducible {p : ℕ} {n : Fin p → ℕ} (g : Coord n → Coord n) (X : Set (Coord n)) : Prop :=
  ∀ I : Set (Comp n), I.Nonempty → Iᶜ.Nonempty →
    ∃ a ∈ I, ∃ b ∉ I, ∀ v ∈ X, partialDeriv g v a b ≠ 0

end StochFictPlay.Supermodular


