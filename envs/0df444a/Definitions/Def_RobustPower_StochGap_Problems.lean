-- Prove2me | Definitions.Def_RobustPower_StochGap_Problems
-- name    : RobustPower_StochGap_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:53:24.11691+00:00
-- url     : https://prove2.me/theorems/7cfeffd0-8b36-4d34-b008-ccd8a9b10f9e
-- title:
--   (1.1)–(1.2), pp. 3–4 — the two-stage stochastic and robust problems Π_Stoch(b), Π_Rob(b) and their optimal values
-- statement:
--   Fix matrices $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, cost vectors $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$, a set $\Omega$ of scenarios with a probability measure $\mu$, and right-hand sides $b(\omega)\in\mathbb R^m$, $\omega\in\Omega$. For index sets $I_1\subseteq\{1,\dots,n_1\}$, $I_2\subseteq\{1,\dots,n_2\}$ let the mixed-integer domains be the nonnegative vectors whose coordinates in $I_k$ are integers (the paper's $\mathbb R^{n_k-p_k}_+\times\mathbb Z^{p_k}_+$ with $p_k=|I_k|$).
--
--   The **two-stage stochastic problem** $\Pi_{\mathrm{Stoch}}(b)$, (1.1), chooses a first-stage $x$ and a second-stage policy $y:\Omega\to\mathbb R^{n_2}$:
--   $$z_{\mathrm{Stoch}}(b)=\inf\Big\{c^Tx+\mathbb E_\mu[d^Ty(\omega)] : Ax+By(\omega)\ge b(\omega)\ \ \forall\omega\in\Omega\Big\},$$
--   with $x$ and every $y(\omega)$ in their mixed-integer domains.
--
--   The **two-stage robust problem** $\Pi_{\mathrm{Rob}}(b)$, (1.2), uses one second-stage decision for all scenarios:
--   $$z_{\mathrm{Rob}}(b)=\inf\Big\{c^Tx+d^Ty : Ax+By\ge b(\omega)\ \ \forall\omega\in\Omega\Big\}.$$
--
--   These are the two problems compared by the stochasticity gap $z_{\mathrm{Rob}}(b)/z_{\mathrm{Stoch}}(b)$.
--
--   **Formalization Note** Optimal values are infima in the extended reals $\overline{\mathbb R}$, equal to $+\infty$ when the problem is infeasible; no optimal solution is assumed to exist. Policies $y$ are required to be $\mu$-integrable, so that $\mathbb E_\mu[d^Ty(\omega)]$ is the genuine expectation (the paper's proofs take $\mathbb E_\mu[y(\omega)]$). Constraints hold for every scenario, as on the page, not $\mu$-almost surely. The robust objective $\max_{\omega}d^Ty$ of (1.2) is written $d^Ty$, since $d$ does not depend on $\omega$. Integer coordinates form an arbitrary index set, which is the paper's domain up to relabelling coordinates. The sign conditions $c,d\ge0$, $b(\omega)\ge0$ of §1.1 are hypotheses of the theorems, not part of the definition.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 3–4, (1.1)–(1.2)

import Mathlib

open MeasureTheory Matrix

namespace RobustPower.StochGap

/-- The mixed-integer domain `ℝ^{n-p}₊ × ℤ^p₊`, up to relabelling coordinates: nonnegative
vectors whose coordinates in `I` are integers (`p = |I|`). -/
def mixedIntDomain {n : ℕ} (I : Set (Fin n)) : Set (Fin n → ℝ) :=
  {x | 0 ≤ x ∧ ∀ i ∈ I, ∃ z : ℤ, x i = z}

/-- Feasibility in the two-stage stochastic problem `Π_Stoch(b)`, (1.1) (p. 3): a first-stage
`x ∈ mixedIntDomain I₁` and an integrable second-stage policy `y : Ω → ℝ^{n₂}` with
`y ω ∈ mixedIntDomain I₂` and `A x + B y(ω) ≥ b(ω)` for every scenario `ω`. -/
def StochFeasible {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ mixedIntDomain I₁ ∧ Integrable y μ ∧
    ∀ ω, y ω ∈ mixedIntDomain I₂ ∧ b ω ≤ A *ᵥ x + B *ᵥ y ω

/-- The optimal value `z_Stoch(b)` of (1.1): the infimum, in `EReal`, of
`cᵀx + E_μ[dᵀy(ω)]` over feasible `(x, y)`; it is `⊤` when `Π_Stoch(b)` is infeasible. -/
noncomputable def zStoch {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (_ : StochFeasible μ A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + ∫ ω, d ⬝ᵥ y ω ∂μ : ℝ) : EReal)

/-- Feasibility in the two-stage robust problem `Π_Rob(b)`, (1.2) (p. 4): one pair `(x, y)`,
`x ∈ mixedIntDomain I₁`, `y ∈ mixedIntDomain I₂`, with `A x + B y ≥ b(ω)` for every `ω`. -/
def RobFeasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ mixedIntDomain I₁ ∧ y ∈ mixedIntDomain I₂ ∧ ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z_Rob(b)` of (1.2): the infimum, in `EReal`, of `cᵀx + dᵀy` over
robust-feasible `(x, y)` (the inner `max_ω dᵀy` equals `dᵀy`, since `d` does not depend on
`ω`); it is `⊤` when `Π_Rob(b)` is infeasible. -/
noncomputable def zRob {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : RobFeasible A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal)

end RobustPower.StochGap


