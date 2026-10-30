-- Prove2me | Definitions.Def_NAPPAL_VPEB_Problem
-- name    : NAPPAL_VPEB_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:59.208908+00:00
-- url     : https://prove2.me/theorems/6bd0b68e-0cb5-4a30-b721-1f98594c4796
-- title:
--   The data of problem (P) and the constants of Assumption 1
-- statement:
--   An instance of problem
--   $$\text{(P)}\quad \min\ G(u,v) + J(u) + H(v) \quad \text{s.t.}\quad \Omega(u) + \Phi(u) + Bv = 0,\ u \in U,\ v \in \mathbb{R}^d$$
--   consists of
--
--   1. a function $G : \mathbb{R}^n \times \mathbb{R}^d \to \mathbb{R}$ and a function $H : \mathbb{R}^d \to \mathbb{R}$;
--   2. a function $J : \mathbb{R}^n \to (-\infty, +\infty]$;
--   3. a set $U \subseteq \mathbb{R}^n$;
--   4. maps $\Omega, \Phi : \mathbb{R}^n \to \mathbb{R}^m$ and an $m \times d$ matrix $B$;
--   5. the constants $L_G$, $L_H$, $L^0_\Theta$ and $L_{\Omega_j}$ ($j = 1, \dots, m$) of Assumption 1.
--
--   The hypotheses on these data (Assumption 1) are a separate definition.
--
--   **Formalization Note** $J$ takes values in the extended reals (Assumption 1 excludes $-\infty$). $G$ and $H$ are real-valued as declared on p. 2. The constants are given numbers satisfying the Lipschitz hypotheses, not optimal constants.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §1.1, p. 2 (problem (P)) and Assumption 1, p. 7 (constants)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_UV

namespace NAPPAL.VPEB

/-- **The data of problem (P) and the constants of Assumption 1.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §1.1, p. 2:
"(P) min G(u, v) + J(u) + H(v) s.t Ω(u) + Φ(u) + Bv = 0, u ∈ U, v ∈ Rd
where G : Rn × Rd → R is a differentiable function, possibly nonconvex; J : Rn → R is lower
semi-continuous (l.s.c.), possibly nonsmooth and nonconvex; H : Rd → R is a differentiable
function, possibly nonconvex; U is closed convex subset of Rn. … Θ(u) := Ω(u) + Φ(u), with
Θ : Rn → Rm being a differentiable mapping, possibly nonlinear; B is an m × d tall matrix."
The constants `L_G, L_H, L⁰_Θ, L_{Ω_j}` are those of Assumption 1 (p. 7).

A `Problem n d m` records `G : ℝⁿ × ℝᵈ → ℝ`, `H : ℝᵈ → ℝ`, `J : ℝⁿ → (−∞, +∞]`, `U ⊆ ℝⁿ`,
`Ω, Φ : ℝⁿ → ℝᵐ`, the linear map `B : ℝᵈ → ℝᵐ` (the `m × d` matrix), and the constants
`L_G`, `L_H`, `L⁰_Θ` and `L_{Ω_j}` (`j = 1, …, m`). The hypotheses on them are
`Assumption1`.

**Formalization Note.** `J` takes values in `EReal` because (H3) (p. 7) gives it the codomain
`(−∞, ∞]`; `Assumption1` excludes the value `⊥`. `G` and `H` are real-valued, as declared on
p. 2 (paper.md Reading 2; (H1)/(H2) on p. 7 write `(−∞, +∞]`, under which step (6) would be
undefined). The constants are given numbers satisfying the Lipschitz hypotheses, not the
optimal Lipschitz constants; they enter (8) and the constants of the analysis as such. -/
structure Problem (n d m : ℕ) where
  /-- the smooth coupling term `G(u, v)` -/
  G : UV n d → ℝ
  /-- the smooth term `H(v)` -/
  H : EuclideanSpace ℝ (Fin d) → ℝ
  /-- the nonsmooth term `J(u) ∈ (−∞, +∞]` -/
  J : EuclideanSpace ℝ (Fin n) → EReal
  /-- the closed convex set `U` -/
  U : Set (EuclideanSpace ℝ (Fin n))
  /-- the smooth part `Ω` of the constraint map -/
  Ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  /-- the remaining part `Φ` of the constraint map -/
  Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  /-- the matrix `B ∈ ℝ^{m×d}` -/
  B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)
  /-- `L_G`, the Lipschitz constant of `∇G` in (H1) -/
  LG : ℝ
  /-- `L_H`, the Lipschitz constant of `∇H` in (H2) -/
  LH : ℝ
  /-- `L⁰_Θ`, the Lipschitz constant of `Θ` in (H4) -/
  L0Θ : ℝ
  /-- `L_{Ω_j}`, the Lipschitz constant of `∇Ω_j` in (H5) -/
  LΩj : Fin m → ℝ

end NAPPAL.VPEB


