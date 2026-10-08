-- Prove2me | Definitions.Def_RobustPower_SimplexGap_Problems
-- name    : RobustPower_SimplexGap_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:13:02.59198+00:00
-- url     : https://prove2.me/theorems/069c16ce-ca00-4261-bd89-41700d5c73aa
-- title:
--   (1.1)–(1.2), pp. 3–4 — the two-stage stochastic and robust problems Π_Stoch(b), Π_Rob(b) and their optimal values
-- statement:
--   This file sets up the two-stage problems with uncertain right-hand side of Bertsimas and Goyal, §1.1.
--
--   **Data.** Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$. Let $\Omega$ be a set of scenarios and $b:\Omega\to\mathbb R^m$, where $b(\omega)$ is the right-hand side realized in scenario $\omega$; the uncertainty set is $I_b(\Omega)=\{b(\omega)\mid\omega\in\Omega\}$. For a set $I$ of coordinates, the **mixed-integer domain** is
--   $$\mathcal D(I)=\{x\ge 0 \;:\; x_i\in\mathbb Z \text{ for all } i\in I\},$$
--   which is $\mathbb R^{n-p}_+\times\mathbb Z^{p}_+$ up to relabelling coordinates ($p=|I|$). The first- and second-stage integer coordinates are $I_1$ and $I_2$.
--
--   **The robust problem $\Pi_{\mathrm{Rob}}(b)$ (1.2).** A pair $(x,y)$ is feasible if $x\in\mathcal D(I_1)$, $y\in\mathcal D(I_2)$ and $Ax+By\ge b(\omega)$ for every $\omega\in\Omega$. Its optimal value is
--   $$z_{\mathrm{Rob}}(b)=\inf\{\,c^Tx+d^Ty \;:\; (x,y)\text{ feasible}\,\}.$$
--
--   **The stochastic problem $\Pi_{\mathrm{Stoch}}(b)$ (1.1).** Let $\mu$ be a measure on $\Omega$. A pair $(x,y(\cdot))$ of a first-stage vector and a second-stage policy $y:\Omega\to\mathbb R^{n_2}$ is feasible if $x\in\mathcal D(I_1)$, $y$ is $\mu$-integrable, and for every $\omega\in\Omega$, $y(\omega)\in\mathcal D(I_2)$ and $Ax+By(\omega)\ge b(\omega)$. Its optimal value is
--   $$z_{\mathrm{Stoch}}(b)=\inf\{\,c^Tx+\mathbb E_\mu[d^Ty(\omega)] \;:\; (x,y)\text{ feasible}\,\}.$$
--
--   Both optimal values are taken in the extended reals, so an infeasible problem has value $+\infty$. These are the objects compared in every stochasticity-gap result of the paper.
--
--   **Formalization Note** The infima are `EReal` infima, not real `sInf`, so infeasibility gives $\top$ rather than a junk $0$; no optimal solution is assumed to exist. The constraints of $\Pi_{\mathrm{Stoch}}(b)$ hold for every scenario, as printed ("$\forall\omega\in\Omega$"), not almost surely. Integrability of the policy is the paper's implicit assumption (it takes $\mathbb E_\mu[y(\omega)]$). In $\Pi_{\mathrm{Rob}}(b)$ the printed cost $\max_{\omega} d^Ty$ does not depend on $\omega$ and is written $d^Ty$. Nonnegativity of $c$, $d$, $b$ is not built in; theorems state it where needed.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 3–4, (1.1)–(1.2)

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems

namespace RobustPower.SimplexGap

open MeasureTheory Matrix

/-- Feasibility in the two-stage robust problem `Π_Rob(b)` (1.2): one pair `(x, y)`, with
`x ∈ dom₁`, `y ∈ dom₂` and `A x + B y ≥ b(ω)` for every scenario `ω`. -/
def RobFeasible {Ω : Type*} {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ y ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z_Rob(b)` of `Π_Rob(b)` (1.2), an infimum in `EReal`
(`⊤` when the problem is infeasible). The cost `max_ω dᵀy` does not depend on `ω`. -/
noncomputable def zRob {Ω : Type*} {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : RobFeasible A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal)

/-- Feasibility in the two-stage stochastic problem `Π_Stoch(b)` (1.1): a first-stage `x ∈ dom₁`
and a `μ`-integrable second-stage policy `y : Ω → ℝ^{n₂}` with `y(ω) ∈ dom₂` and
`A x + B y(ω) ≥ b(ω)` for every scenario `ω`. -/
def StochFeasible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n₁ n₂ : ℕ}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ Integrable y μ ∧
    ∀ ω, y ω ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ b ω ≤ A *ᵥ x + B *ᵥ y ω

/-- The optimal value `z_Stoch(b)` of `Π_Stoch(b)` (1.1): the `EReal` infimum of
`cᵀx + E_μ[dᵀy(ω)]` over feasible `(x, y)` (`⊤` when the problem is infeasible). -/
noncomputable def zStoch {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n₁ n₂ : ℕ}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ)
    (d : Fin n₂ → ℝ) (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (_ : StochFeasible μ A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + ∫ ω, d ⬝ᵥ y ω ∂μ : ℝ) : EReal)

end RobustPower.SimplexGap


