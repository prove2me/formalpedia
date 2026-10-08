-- Prove2me | Definitions.Def_RobustPower_CostGap_Problems
-- name    : RobustPower_CostGap_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:59.542988+00:00
-- url     : https://prove2.me/theorems/0554eb11-7e80-4b1f-b089-ad3d40b22290
-- title:
--   (1.4)–(1.5), pp. 4–5 — the two-stage stochastic and robust problems Π_Stoch(b, d), Π_Rob(b, d) and their optimal values
-- statement:
--   Fix data $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$ and $c\in\mathbb R^{n_1}$, a set $\Omega$ of scenarios, and for each scenario $\omega$ a right-hand side $b(\omega)\in\mathbb R^m$ and a second-stage cost vector $d(\omega)\in\mathbb R^{n_2}$. For a set $I$ of coordinates, the **mixed-integer domain** is the set of nonnegative vectors whose coordinates in $I$ are integers; with $|I|=p$ it is $\mathbb R^{n-p}_+\times\mathbb Z^p_+$ up to the order of coordinates. Let $I_1$ and $I_2$ be the integer coordinates of the first and the second stage.
--
--   1. **The stochastic problem** $\Pi_{\mathrm{Stoch}}(b,d)$, (1.4). Let $\mu$ be a probability measure on $\Omega$. A first-stage decision $x$ in the mixed-integer domain of $I_1$ and a policy $\omega\mapsto y(\omega)$ are feasible if $y$ and $\omega\mapsto d(\omega)^{\mathsf T}y(\omega)$ are $\mu$-integrable and, for **every** scenario $\omega$, $y(\omega)$ lies in the mixed-integer domain of $I_2$ and $Ax+By(\omega)\ge b(\omega)$. The optimal value is
--   $$
--   z_{\mathrm{Stoch}}(b,d)=\inf\Bigl\{\,c^{\mathsf T}x+\mathbb E_\mu\bigl[d(\omega)^{\mathsf T}y(\omega)\bigr] : (x,y)\ \text{feasible}\Bigr\}.
--   $$
--   2. **The robust problem** $\Pi_{\mathrm{Rob}}(b,d)$, (1.5). A single pair $(x,y)$ in the mixed-integer domains is feasible if $Ax+By\ge b(\omega)$ for every $\omega\in\Omega$. The optimal value is
--   $$
--   z_{\mathrm{Rob}}(b,d)=\inf\Bigl\{\,c^{\mathsf T}x+\sup_{\omega\in\Omega} d(\omega)^{\mathsf T}y : (x,y)\ \text{feasible}\Bigr\}.
--   $$
--
--   The robust problem commits to one second-stage decision for all scenarios and pays its worst-case cost; the stochastic problem adapts the second-stage decision to the scenario and pays the expected cost. The ratio $z_{\mathrm{Rob}}/z_{\mathrm{Stoch}}$ is the stochasticity gap studied in Section 3.
--
--   **Formalization Note** Both optimal values are infima in the extended reals $[-\infty,+\infty]$: an infeasible problem has value $+\infty$, and the worst-case cost $\sup_\omega d(\omega)^{\mathsf T}y$ may be $+\infty$. No optimal solution is assumed to exist. Integrability of the policy is the paper's implicit assumption (its proofs take $\mathbb E_\mu[y(\omega)]$). The paper prints $\mathbb Z^{n_2}_+$ for the second-stage integer block in (1.4)–(1.5); $\mathbb Z^{p_2}_+$ is meant. The paper's standing sign assumptions ($c\ge0$, $b(\omega)\ge0$, $d(\omega)\ge0$) are not built into the definitions; they hold in the instance of Theorem 3.1.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 4–5, (1.4) and (1.5)

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Feasibility in the two-stage stochastic problem `Π_Stoch(b, d)`, (1.4) (p. 4): a first-stage
`x ∈ RobustPower.StochGap.mixedIntDomain I₁` and an integrable second-stage policy `y : Ω → ℝ^{n₂}` whose cost
`ω ↦ d(ω)ᵀy(ω)` is integrable, with `y ω ∈ RobustPower.StochGap.mixedIntDomain I₂` and `A x + B y(ω) ≥ b(ω)` for
every scenario `ω`. -/
def StochFeasibleBD {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (d : Ω → Fin n₂ → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ)
    (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ Integrable y μ ∧ Integrable (fun ω => d ω ⬝ᵥ y ω) μ ∧
    ∀ ω, y ω ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ b ω ≤ A *ᵥ x + B *ᵥ y ω

/-- The optimal value `z_Stoch(b, d)` of (1.4): the infimum, in `EReal`, of
`cᵀx + E_μ[d(ω)ᵀy(ω)]` over feasible `(x, y)`; it is `⊤` when `Π_Stoch(b, d)` is infeasible. -/
noncomputable def zStochBD {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (_ : StochFeasibleBD μ A B b d I₁ I₂ x y),
    ((c ⬝ᵥ x + ∫ ω, d ω ⬝ᵥ y ω ∂μ : ℝ) : EReal)

/-- Feasibility in the two-stage robust problem `Π_Rob(b, d)`, (1.5) (p. 5): one pair `(x, y)`,
`x ∈ RobustPower.StochGap.mixedIntDomain I₁`, `y ∈ RobustPower.StochGap.mixedIntDomain I₂`, with `A x + B y ≥ b(ω)` for every `ω`. -/
def RobFeasibleBD {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ y ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z_Rob(b, d)` of (1.5): the infimum, in `EReal`, of
`cᵀx + sup_ω d(ω)ᵀy` over robust-feasible `(x, y)`. The worst-case second-stage cost is an
`EReal` supremum, so it may be `+∞`; the value is `⊤` when `Π_Rob(b, d)` is infeasible. -/
noncomputable def zRobBD {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : RobFeasibleBD A B b I₁ I₂ x y),
    ((c ⬝ᵥ x : ℝ) : EReal) + ⨆ ω, ((d ω ⬝ᵥ y : ℝ) : EReal)

end RobustPower.CostGap


