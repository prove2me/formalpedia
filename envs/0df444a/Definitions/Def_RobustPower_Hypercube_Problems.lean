-- Prove2me | Definitions.Def_RobustPower_Hypercube_Problems
-- name    : RobustPower_Hypercube_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:49:03.142305+00:00
-- url     : https://prove2.me/theorems/3d677ad1-dd58-4139-85fa-99276cd77d20
-- title:
--   $\Pi_{\mathrm{Adapt}}(A,B,b,d)$ (5.6) and $\Pi_{\mathrm{Rob}}(A,B,b,d)$ (5.7)
-- statement:
--   Let $\Omega$ be a set of scenarios. In scenario $\omega$ the data are $A(\omega)\in\mathbb R^{m\times n_1}$, $B(\omega)\in\mathbb R^{m\times n_2}$, $b(\omega)\in\mathbb R^m$ and $d(\omega)\in\mathbb R^{n_2}$; the first-stage cost $c\in\mathbb R^{n_1}$ is fixed, and $I_1,I_2$ are the integer coordinates of the two stages.
--
--   1. **Adaptive problem** $\Pi_{\mathrm{Adapt}}(A,B,b,d)$ (5.6): choose $x\in D_{I_1}$ and a second-stage decision $y(\omega)\in D_{I_2}$ for every scenario with $A(\omega)x+B(\omega)y(\omega)\ge b(\omega)$ for all $\omega\in\Omega$. Its value is
--   $$z_{\mathrm{Adapt}}(A,B,b,d)=\inf\Big\{c^Tx+\sup_{\omega\in\Omega}d(\omega)^Ty(\omega)\Big\}.$$
--   2. **Robust problem** $\Pi_{\mathrm{Rob}}(A,B,b,d)$ (5.7): choose $x\in D_{I_1}$ and one $y\in D_{I_2}$ with $A(\omega)x+B(\omega)y\ge b(\omega)$ for all $\omega\in\Omega$. Its value is
--   $$z_{\mathrm{Rob}}(A,B,b,d)=\inf\Big\{c^Tx+\sup_{\omega\in\Omega}d(\omega)^Ty\Big\}.$$
--
--   The robust problem is the adaptive problem restricted to policies that do not depend on the scenario.
--
--   **Formalization Note** Costs and values are extended reals: the inner supremum may be $+\infty$, and an infeasible problem has value $+\infty$. The paper's "min" and "max" are read as infimum and supremum, so no optimal solution is assumed. The page prints $\mathbb Z^{n_2}_+$ for the second-stage integer block in (5.6)–(5.7); it is read as $\mathbb Z^{p_2}_+$, as in (1.1)–(1.3).
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 31, (5.6)–(5.7)

import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.Hypercube

/-- (5.6): feasible adaptive decisions for uncertain `A`, `B`, and `b`. -/
def adaptFeasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧
    ∀ ω, y ω ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ b ω ≤ A ω *ᵥ x + B ω *ᵥ y ω

/-- (5.7): one second-stage decision must satisfy every scenario. -/
def robFeasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ y ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧
    ∀ ω, b ω ≤ A ω *ᵥ x + B ω *ᵥ y

/-- The value `z_Adapt(A,B,b,d)` in (5.6), with `⊤` for infeasibility. -/
noncomputable def zAdapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ)
    (_ : adaptFeasible A B b I₁ I₂ x y), RobustPower.AdaptGap.adaptCost c d x y

/-- The value `z_Rob(A,B,b,d)` in (5.7), with `⊤` for infeasibility. -/
noncomputable def zRob {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ)
    (_ : robFeasible A B b I₁ I₂ x y), RobustPower.AdaptGap.robCost c d x y

end RobustPower.Hypercube


