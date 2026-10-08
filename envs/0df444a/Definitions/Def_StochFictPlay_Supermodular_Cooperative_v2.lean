-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_Cooperative_v2
-- name    : StochFictPlay_Supermodular_Cooperative_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T06:02:43.034383+00:00
-- url     : https://prove2.me/theorems/8b3556bb-e712-478f-b84e-87e44fac9512
-- title:
--   Cooperative and irreducible differential equations (re-issued over the corrected choice model)
-- statement:
--   For a vector field $g$ on $\prod_\alpha \mathbb R^{n^\alpha-1}$ with components indexed by pairs $(\alpha,i)$ and a set $X$ of states (p. 20): the partial derivative $\partial g^\alpha_i/\partial v^\beta_j(v)$ (the $(\alpha,i)$ entry of the Fréchet derivative of $g$ at $v$ applied to the $(\beta,j)$ basis vector); $\dot v = g(v)$ is *cooperative* on $X$ if $\partial g^\alpha_i/\partial v^\beta_j(v) \ge 0$ for all $v \in X$ and all distinct pairs; it is *irreducible* on $X$ if for every nonempty proper subset $I$ of the components there are $(\alpha,i) \in I$ and $(\beta,j) \notin I$ with $\partial g^\alpha_i/\partial v^\beta_j(v) \ne 0$ for all $v \in X$ (the uniform form the proof of Theorem 5.4, p. 31, establishes).
--
--   **Formalization Note.** Verbatim re-issue of `StochFictPlay_Supermodular_Cooperative` whose only change is that it is built on `StochFictPlay_Supermodular_StochOrder_v2`, so that the whole definition chain uses the corrected `IsRegularDensity` (continuous strictly positive shock densities). No declaration changed.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 20 (cooperative and irreducible dynamics), p. 31 (uniform form in the proof of Theorem 5.4)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_StochOrder_v2

/-! Re-issue of `Def_StochFictPlay_Supermodular_Cooperative` on top of the corrected
`Def_StochFictPlay_Supermodular_ChoiceModel_v2` (continuous strictly positive shock densities).
The declarations below are unchanged. -/

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


