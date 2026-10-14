-- Prove2me | Definitions.Def_DirectedOpinion_Typical_Marks
-- name    : DirectedOpinion_Typical_Marks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:07.327193+00:00
-- url     : https://prove2.me/theorems/8e279004-8527-4b88-9a57-2b3ef062fa6c
-- title:
--   pp. 3, 6, 8 — full vertex marks, the mark space 𝒮 and the mark metric ρ
-- statement:
--   Let $\mathcal S'$ be a metric space with metric $\rho'$ (in the paper, a Polish space of generic attributes). A **full mark** is a tuple
--   $$\mathbf x=(\mathbf a,q,s,d^-,c_1\mathbb 1(d^-\ge1),c_2\mathbb 1(d^-\ge2),\dots)$$
--   of a generic attribute $\mathbf a\in\mathcal S'$, an internal opinion $q$, a stubbornness label $s$, an in-degree $d^-\in\mathbb N$ and a sequence of weights. The paper's **mark space** is
--   $$\mathcal S=\mathcal S'\times[-1,1]\times\{0,1\}\times\mathbb N\times[0,1]^\infty .$$
--   The **mark metric** is
--   $$\rho(\mathbf x,\tilde{\mathbf x})=\rho'(\mathbf a,\tilde{\mathbf a})+|q-\tilde q|+|s-\tilde s|+|d^--\tilde d^-|+\sum_{j=1}^\infty\bigl|c_j\mathbb 1(d^-\ge j)-\tilde c_j\mathbb 1(\tilde d^-\ge j)\bigr| .$$
--
--   The metric $\rho$ measures how close the marks of a finite graph are to those of its local limit in the strong coupling (Definition 4), and it is the metric in which the signal kernel of Theorem 2 is Lipschitz.
--
--   **Formalization Note** Marks are elements of the product type `A × ℝ × ℝ × ℕ × (ℕ → ℝ)`, with `dist` on `A` as $\rho'$; the label $s$ is a real number, and $\mathcal S$ is the subset `markSpace A` where $q\in[-1,1]$, $s\in\{0,1\}$ and every weight lies in $[0,1]$. Weight coordinates are 0-based. The indicator $\mathbb 1(d^-\ge j)$ is applied inside $\rho$, so only finitely many terms of the series are nonzero and the `tsum` is a finite sum.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 3 (x_i and 𝒮), p. 6 (X_i), p. 8 (ρ)

import Mathlib

namespace DirectedOpinion.Typical

/-- A full vertex mark `x = (a, q, s, d⁻, (c_j 1(d⁻ ≥ j))_{j ≥ 1})` (pp. 3, 6): a generic attribute
`a` in a Polish space `A` (the paper's `S′`), the internal opinion `q`, the stubbornness label `s`,
the in-degree `d⁻`, and the weight sequence (0-based: coordinate `j` is the paper's `c_{j+1}`).
The paper's mark space `𝒮` is the subset `markSpace A`. -/
abbrev Mark (A : Type*) := A × ℝ × ℝ × ℕ × (ℕ → ℝ)

/-- Generic attribute `a` of a mark. -/
def Mark.attr {A : Type*} (x : Mark A) : A := x.1
/-- Internal opinion `q` of a mark. -/
def Mark.q {A : Type*} (x : Mark A) : ℝ := x.2.1
/-- Stubbornness label `s` of a mark. -/
def Mark.s {A : Type*} (x : Mark A) : ℝ := x.2.2.1
/-- In-degree `d⁻` of a mark. -/
def Mark.deg {A : Type*} (x : Mark A) : ℕ := x.2.2.2.1
/-- Weight sequence of a mark; coordinate `j` (0-based) is the paper's `c_{j+1} 1(d⁻ ≥ j+1)`. -/
def Mark.wt {A : Type*} (x : Mark A) : ℕ → ℝ := x.2.2.2.2

/-- The paper's mark space `𝒮 = S′ × [−1, 1] × {0, 1} × ℕ × [0, 1]^∞` (p. 3), as a subset of
`Mark A`. -/
def markSpace (A : Type*) : Set (Mark A) :=
  {x | x.q ∈ Set.Icc (-1 : ℝ) 1 ∧ (x.s = 0 ∨ x.s = 1) ∧ ∀ j, x.wt j ∈ Set.Icc (0 : ℝ) 1}

/-- The mark metric of p. 8:
`ρ(x, x̃) = ρ′(a, ã) + |q − q̃| + |s − s̃| + |d⁻ − d̃⁻| + Σ_{j ≥ 1} |c_j 1(d⁻ ≥ j) − c̃_j 1(d̃⁻ ≥ j)|`,
with `ρ′ = dist` on `A`. The indicator `1(d⁻ ≥ j)` is applied here, so only the first
`max(d⁻, d̃⁻)` terms of the sum can be nonzero and the `tsum` is a finite sum. -/
noncomputable def ρ {A : Type*} [PseudoMetricSpace A] (x y : Mark A) : ℝ :=
  dist x.attr y.attr + |x.q - y.q| + |x.s - y.s| + |(x.deg : ℝ) - (y.deg : ℝ)| +
    ∑' j : ℕ, |(if j < x.deg then x.wt j else 0) - (if j < y.deg then y.wt j else 0)|

end DirectedOpinion.Typical


