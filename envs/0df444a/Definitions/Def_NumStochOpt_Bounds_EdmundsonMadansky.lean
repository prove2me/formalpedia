-- Prove2me | Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky
-- name    : NumStochOpt_Bounds_EdmundsonMadansky
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:53:34.854752+00:00
-- url     : https://prove2.me/theorems/4df60e34-7c3f-4f6d-90a5-1c4c6efc0c50
-- title:
--   The Edmundson–Madansky two-point law (2.32) and its product over the vertices of a box
-- statement:
--   Let $[a,b]$ be an interval with $a<b$ and let $\xi^0\in[a,b]$. The **Edmundson–Madansky two-point law** (2.32) puts
--   $$
--   p_1=\frac{b-\xi^0}{b-a}\ \text{ at } a,\qquad p_2=\frac{\xi^0-a}{b-a}\ \text{ at } b .
--   $$
--   It is the unique law on $\{a,b\}$ with mean $\xi^0$.
--
--   For a box $\Xi=\times_{j}[a_j,b_j]$ and means $\xi^0_j$, a vertex of $\Xi$ is selected by a choice $v_j\in\{a_j,b_j\}$ of an endpoint in each coordinate. The vector $\hat\xi$ of p. 46 has independent components $\hat\xi_j$ with the two-point law (2.32) on $\{a_j,b_j\}$, so it sits at the vertex $v$ with probability
--   $$
--   w(v)=\prod_j p_j(v_j),\qquad p_j(a_j)=\frac{b_j-\xi^0_j}{b_j-a_j},\quad p_j(b_j)=\frac{\xi^0_j-a_j}{b_j-a_j}.
--   $$
--   For a function $\varphi$ on $\Xi$, the **Edmundson–Madansky upper bound** is
--   $$
--   E\varphi(\hat\xi)=\sum_{v}w(v)\,\varphi(v),
--   $$
--   the sum over the $2^m$ vertices of $\Xi$.
--
--   These are the explicit weights of the upper bound (2.33) and of its product form on p. 46.
--
--   **Formalization Note** A vertex is encoded by a Boolean vector: `true` selects $b_j$, `false` selects $a_j$. The weights divide by $b_j-a_j$; the theorems that use them assume $a_j<b_j$.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 45, Eq. (2.32); p. 46, construction of the variable with independent components on the vertices of the rectangle

import Mathlib

namespace NumStochOpt.Bounds

/-- The two-point Edmundson–Madansky law (2.32), p. 45, of an interval `[a, b]` with mean `ξ⁰`:
the endpoint selected by `s` (`false ↦ a`, `true ↦ b`) receives probability
`p₁ = (b − ξ⁰)/(b − a)` at `a` and `p₂ = (ξ⁰ − a)/(b − a)` at `b`. -/
noncomputable def emProb (a b ξ0 : ℝ) (s : Bool) : ℝ :=
  if s then (ξ0 - a) / (b - a) else (b - ξ0) / (b - a)

/-- The vertex of the box `Ξ = ×_j [a_j, b_j]` selected by `v`: coordinate `j` is `b_j` if
`v j = true` and `a_j` otherwise (p. 46). -/
def boxVertex {ι : Type*} (a b : ι → ℝ) (v : ι → Bool) : ι → ℝ :=
  fun j => if v j then b j else a j

/-- The probability that the discrete vector `ξ̂` of p. 46 — independent components `ξ̂_j`
distributed on `{a_j, b_j}` according to (2.32) with means `ξ⁰_j` — sits at the vertex
selected by `v`: the product `∏_j` of the two-point probabilities. -/
noncomputable def emVertexWeight {ι : Type*} [Fintype ι] (a b ξ0 : ι → ℝ) (v : ι → Bool) : ℝ :=
  ∏ j, emProb (a j) (b j) (ξ0 j) (v j)

/-- The Edmundson–Madansky upper bound `E φ(ξ̂) = Σ_v (∏_j p_j(v_j)) φ(vertex v)`, the sum over
the `2^m` vertices of the box `×_j [a_j, b_j]` (p. 46, with (2.32)–(2.33)). -/
noncomputable def emUpperBound {ι : Type*} [Fintype ι] [DecidableEq ι] (a b ξ0 : ι → ℝ) (φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ v : ι → Bool, emVertexWeight a b ξ0 v * φ (boxVertex a b v)

end NumStochOpt.Bounds


