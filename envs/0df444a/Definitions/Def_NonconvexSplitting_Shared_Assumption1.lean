-- Prove2me | Definitions.Def_NonconvexSplitting_Shared_Assumption1
-- name    : NonconvexSplitting_Shared_Assumption1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T13:05:43.473865+00:00
-- url     : https://prove2.me/theorems/12b11545-df4a-442f-9816-675c76c58521
-- title:
--   Assumption 1 (parameters of the proximal ADMM)
-- statement:
--   For a linear self-map $\mathcal T$ of $\mathbb{R}^n$ write $\|x\|_{\mathcal T}^2 := \langle x, \mathcal T x\rangle$ (possibly negative when $\mathcal T$ is indefinite). For symmetric self-maps, $\mathcal T_1 \succeq \mathcal T_2$ means $\mathcal T_1 - \mathcal T_2$ is positive semidefinite and $\mathcal T_1 \succ \mathcal T_2$ means it is positive definite.
--
--   Let $h, \phi : \mathbb{R}^n \to \mathbb{R}$ be twice differentiable, $\mathcal M : \mathbb{R}^n \to \mathbb{R}^m$ linear and $\beta \in \mathbb{R}$. **Assumption 1** with witnesses $\sigma, \delta, \gamma \in \mathbb{R}$ and self-maps $\mathcal Q_1, \mathcal Q_2, \mathcal T_1, \mathcal T_2, \mathcal Q_3$ of $\mathbb{R}^n$ holds if
--
--   1. (i) $\sigma > 0$ and $\mathcal M\mathcal M^* \succeq \sigma\mathcal I$; and $\mathcal Q_1 \succeq \nabla^2 h(x) \succeq \mathcal Q_2$ for all $x$;
--   2. (ii) $\beta > 0$, and
--      - $\mathcal T_1 \succeq \mathcal T_2 \succeq 0$ and $\mathcal T_1^2 \succeq [\nabla^2\phi(x)]^2 \succeq \mathcal T_2^2$ for all $x$;
--      - $\delta > 0$ and $\mathcal Q_2 + \beta\mathcal M^*\mathcal M + \mathcal T_2 \succeq \delta\mathcal I$;
--      - $\mathcal Q_3 \succeq [\nabla^2 h(x) + \nabla^2\phi(x)]^2$ for all $x$, and $\gamma \in (0, 1)$ with
--   $$
--   \delta\mathcal I + \mathcal T_2 \succ \frac{2}{\sigma\beta}\mathcal H_\gamma, \qquad \mathcal H_\gamma := \frac{1}{\gamma}\mathcal Q_3 + \frac{1}{1-\gamma}\mathcal T_1^2 .
--   $$
--
--   The paper states the witnesses existentially ("for some $\sigma > 0$", "there exist $\mathcal Q_1, \mathcal Q_2$", …); here they are parameters, and every theorem quantifies over them universally, which is the same hypothesis.
--
--   **Formalization Note** $\succeq$ is Mathlib's Loewner order on continuous linear self-maps ($A \le B$ iff $B - A$ is symmetric and positive semidefinite), so each relation also asserts the symmetry of the difference. The strict order is encoded as $A \le B$ together with $\langle (B - A)x, x\rangle > 0$ for $x \ne 0$. Squares $\mathcal T^2$ are compositions $\mathcal T \circ \mathcal T$, and $\sigma\mathcal I$ is $\sigma$ times the identity.
--
--   **Shared definition.** Serves chunks `01-admm-stationary` (p. 6, Assumption 1; p. 3, the weighted norm and the order ⪰, ≻; previously `NonconvexSplitting.ProxADMM.Assumption1`), `02-admm-bounded` (p. 6, Assumption 1; p. 3, the weighted norm and the order ⪰, ≻; previously `NonconvexSplitting.ADMMBounded.Assumption1`) and `03-admm-kl-convergence` (p. 6, Assumption 1; p. 3 (the orders ⪰, ≻ and ‖·‖²_T); previously `NonconvexSplitting.ADMMKL.Assumption1`). Every copy had the same Lean body, identical up to the namespace, and the same conventions; it is reviewed once here for all of them.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 6, Assumption 1; p. 3, the weighted norm and the order ⪰, ≻; shared by chunks 01-admm-stationary, 02-admm-bounded, 03-admm-kl-convergence

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions

open scoped InnerProductSpace

namespace NonconvexSplitting.Shared

/-- The quadratic form `‖x‖²_T = ⟪x, T x⟫` of a linear self-map `T` (Li–Pong, p. 3).
It is defined for every `T`; for an indefinite `T` it can be negative. -/
noncomputable def wnormSq {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪x, T x⟫_ℝ

/-- Strict Loewner order `A ≺ B` (Li–Pong, p. 3): `B - A` is symmetric and positive definite,
i.e. `A ≤ B` in the Loewner order and `⟪(B - A) x, x⟫ > 0` for every `x ≠ 0`. -/
def StrictLoewner {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  A ≤ B ∧ ∀ x, x ≠ 0 → 0 < ⟪(B - A) x, x⟫_ℝ

/-- Assumption 1 of Li–Pong (p. 6), with its witnesses as explicit parameters.
Here `≤` on linear self-maps is the Loewner order (`A ≤ B` iff `B - A` is symmetric positive
semidefinite), `σ • 1` is `σ I` and `T * T` is `T²`.
(i) `M M* ⪰ σ I` with `σ > 0`, and `Q₁ ⪰ ∇²h(x) ⪰ Q₂` for all `x`.
(ii) `β > 0`; `T₁ ⪰ T₂ ⪰ 0` with `T₁² ⪰ [∇²φ(x)]² ⪰ T₂²` for all `x`;
`Q₂ + β M* M + T₂ ⪰ δ I` with `δ > 0`; `Q₃ ⪰ [∇²h(x) + ∇²φ(x)]²` for all `x`; and
`γ ∈ (0, 1)` with `δ I + T₂ ≻ (2/(σβ)) H_γ`, `H_γ = (1/γ) Q₃ + (1/(1-γ)) T₁²`. -/
def Assumption1 {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β σ : ℝ)
    (Q1 Q2 T1 T2 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (γ : ℝ) : Prop :=
  -- (i)
  (0 < σ ∧ σ • (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) ≤
      M ∘L ContinuousLinearMap.adjoint M) ∧
  (∀ x, Q2 ≤ hess h x ∧ hess h x ≤ Q1) ∧
  -- (ii)
  0 < β ∧
  (0 ≤ T2 ∧ T2 ≤ T1 ∧
    ∀ x, T2 * T2 ≤ hess phi x * hess phi x ∧ hess phi x * hess phi x ≤ T1 * T1) ∧
  (0 < δ ∧ δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
      Q2 + β • (ContinuousLinearMap.adjoint M ∘L M) + T2) ∧
  (∀ x, (hess h x + hess phi x) * (hess h x + hess phi x) ≤ Q3) ∧
  (0 < γ ∧ γ < 1 ∧
    StrictLoewner ((2 / (σ * β)) • ((1 / γ) • Q3 + (1 / (1 - γ)) • (T1 * T1)))
      (δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + T2))

end NonconvexSplitting.Shared


