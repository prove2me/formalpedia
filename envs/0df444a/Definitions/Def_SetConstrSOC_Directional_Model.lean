-- Prove2me | Definitions.Def_SetConstrSOC_Directional_Model
-- name    : SetConstrSOC_Directional_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:57.890897+00:00
-- url     : https://prove2.me/theorems/282e0512-776e-4419-a634-2f6b6128be4b
-- title:
--   Problem (P), critical cone, Lagrangian, directional multipliers, lower generalized support
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $g:\mathbb R^n\to\mathbb R^m$ be twice continuously differentiable, let $\Lambda\subseteq\mathbb R^m$ be closed, and let $F=\{x:g(x)\in\Lambda\}$ be the feasible region. The critical cone at $\bar x$ is $C(\bar x)=\{d:\nabla g(\bar x)d\in T_\Lambda(g(\bar x)),\;\nabla f(\bar x)d\le0\}$. The directional M-multiplier set contains the $\lambda$ satisfying Lagrangian stationarity and $\lambda\in N_\Lambda(g(\bar x);\nabla g(\bar x)d)$.
--
--   For a set $S$ and a subset $A$, the lower generalized support function is
--
--   $$
--   \widehat\sigma_{S,A}(\lambda)=\liminf_{\widetilde\lambda\to\lambda}\inf\{\widetilde\lambda^\top u:u\in A,\;\widetilde\lambda\in N_S(u)\}.
--   $$
--
--   These definitions link the variational-analysis layer to the paper's second-order conditions.
--
--   **Formalization Note** The support function is valued in extended reals. The infimum of an empty qualifying set is $+\infty$; the unrestricted function uses $A=\mathbb R^m$.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, pp. 2, 9, 13–15, (1), critical cone, Definition 7, Lagrangian and directional M-multipliers

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_VarAnalysis

open Filter
open scoped Topology
noncomputable section

namespace SetConstrSOC.Directional

/-- Problem (P), p. 2. -/
structure Problem (n m : ℕ) where
  f : E n → ℝ
  g : E n → E m
  Λ : Set (E m)

namespace Problem

variable {n m : ℕ} (P : Problem n m)

/-- The standing assumptions on problem (P), p. 2. -/
def Standing : Prop := ContDiff ℝ 2 P.f ∧ ContDiff ℝ 2 P.g ∧ IsClosed P.Λ

/-- The feasible region F, p. 9. -/
def feasible : Set (E n) := {x | P.g x ∈ P.Λ}

/-- The critical cone C(x̄), p. 13. -/
def criticalCone (x : E n) : Set (E n) :=
  {d | fderiv ℝ P.g x d ∈ tangentCone P.Λ (P.g x) ∧ fderiv ℝ P.f x d ≤ 0}

/-- The second derivative of L(x,λ) = f(x) + ⟪g(x),λ⟫ along d, p. 15. -/
def hessLag (x : E n) (lam : E m) (d : E n) : ℝ :=
  ((fderiv ℝ (fderiv ℝ P.f) x) d) d +
    inner ℝ lam (((fderiv ℝ (fderiv ℝ P.g) x) d) d)

/-- Stationarity of the Lagrangian in x, p. 15. -/
def IsStationary (x : E n) (lam : E m) : Prop :=
  ∀ w : E n, (fderiv ℝ P.f x) w + inner ℝ lam ((fderiv ℝ P.g x) w) = 0

/-- The directional Mordukhovich multiplier set Λ(x̄;d), p. 15. -/
def dirMMultipliers (x d : E n) : Set (E m) :=
  {lam | P.IsStationary x lam ∧
    lam ∈ dirLimNormal P.Λ (P.g x) (fderiv ℝ P.g x d)}

end Problem

/-- Definition 7, p. 14: the lower generalized support function relative to A. -/
def lowerGenSupport {n : ℕ} (S A : Set (E n)) (lam : E n) : EReal :=
  Filter.liminf (fun lam' : E n =>
    ⨅ u ∈ {u | u ∈ A ∧ lam' ∈ limNormal S u}, ((inner ℝ lam' u : ℝ) : EReal)) (𝓝 lam)

/-- Definition 7, p. 14: unrestricted lower generalized support. -/
def lowerGenSupport₀ {n : ℕ} (S : Set (E n)) (lam : E n) : EReal :=
  lowerGenSupport S Set.univ lam

end SetConstrSOC.Directional


