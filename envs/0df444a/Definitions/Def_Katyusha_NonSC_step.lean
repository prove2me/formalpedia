-- Prove2me | Definitions.Def_Katyusha_NonSC_step
-- name    : Katyusha_NonSC_step
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:24.031064+00:00
-- url     : https://prove2.me/theorems/555c72ef-4df1-48a7-bc6f-6f192c610a46
-- title:
--   The composite objective, the parameters $\tau_{1,s},\tau_2,\alpha_s$ and one inner iteration of Katyusha$^{\mathrm{ns}}$
-- statement:
--   Let $E=\mathbb R^d$ with the Euclidean norm, let $f_1,\dots,f_n:E\to\mathbb R$ be the components of a finite sum with given gradient fields $\nabla f_1,\dots,\nabla f_n:E\to E$, write $f=\frac1n\sum_{i=1}^n f_i$ and $\nabla f=\frac1n\sum_{i=1}^n\nabla f_i$, and let $\psi:E\to\mathbb R$. This file defines the following objects of Allen-Zhu's Algorithm 2 ($\mathtt{Katyusha}^{\mathrm{ns}}$).
--
--   1. **Composite objective** (Problem (1.1)): $F(x)=f(x)+\psi(x)$.
--   2. **Parameters** (Algorithm 2, lines 2 and 5): for an epoch index $s\in\{0,1,2,\dots\}$ and a smoothness constant $L$,
--   $$\tau_{1,s}=\frac{2}{s+4},\qquad \tau_2=\frac12,\qquad \alpha_s=\frac{1}{3\tau_{1,s}L}.$$
--   3. **Linear coupling** (line 9): for weights $\tau_1$ and points $\widetilde x,y,z$, $\;x=\tau_1 z+\tau_2\widetilde x+(1-\tau_1-\tau_2)\,y$.
--   4. **SVRG gradient estimator** (lines 6 and 10): for a snapshot $\widetilde x$, a point $x$ and an index $i$, $\;\widetilde\nabla=\nabla f(\widetilde x)+\nabla f_i(x)-\nabla f_i(\widetilde x)$.
--   5. **One inner iteration** (lines 9–12, Option I): given a weight $\tau_1$, a step $\alpha$, a snapshot $\widetilde x$, the current pair $(y_k,z_k)$ and an index $i$, set $x_{k+1}$ by the coupling, $\widetilde\nabla_{k+1}$ by the estimator at $x_{k+1}$, and
--   $$z_{k+1}=\arg\min_z\Big\{\tfrac{1}{2\alpha}\|z-z_k\|^2+\langle\widetilde\nabla_{k+1},z\rangle+\psi(z)\Big\},\qquad y_{k+1}=\arg\min_y\Big\{\tfrac{3L}{2}\|y-x_{k+1}\|^2+\langle\widetilde\nabla_{k+1},y\rangle+\psi(y)\Big\}.$$
--   The step returns $(y_{k+1},z_{k+1})$.
--
--   These are the building blocks of the run of Algorithm 2 and of the one-iteration inequality (Lemma 2.7).
--
--   **Formalization Note** The two arg-min steps are evaluated through a function $P:\mathbb R\times E\to E$ standing for the proximal map: $z_{k+1}=P(\alpha,\,z_k-\alpha\widetilde\nabla_{k+1})$ and $y_{k+1}=P\big(\tfrac1{3L},\,x_{k+1}-\tfrac1{3L}\widetilde\nabla_{k+1}\big)$, which is exact after completing the square. Theorems using these objects assume that $P(\gamma,v)$ is a minimizer of $\psi(u)+\frac1{2\gamma}\|u-v\|^2$ for every $\gamma>0$ (the published predicate `SAGA.Convex.IsProxPoint`). $f$ and $\nabla f$ are the published `SAGA.Convex.fAvg` and `SAGA.Convex.gradAvg`.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 1, Problem (1.1); p. 15, Algorithm 2, lines 2, 5, 6, 9–12 (Option I)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

namespace Katyusha.NonSC

/-- The composite objective `F(x) = f(x) + ψ(x) = (1/n) ∑ᵢ fᵢ(x) + ψ(x)` of Problem (1.1)
(Allen-Zhu, arXiv:1603.05953v6, p. 1). -/
noncomputable def obj {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  SAGA.Convex.fAvg f x + ψ x

/-- The epoch-dependent momentum weight `τ_{1,s} = 2/(s+4)` of Algorithm 2, line 5 (p. 15). -/
noncomputable def tau1 (s : ℕ) : ℝ := 2 / ((s : ℝ) + 4)

/-- The Katyusha-momentum weight `τ₂ = 1/2` of Algorithm 2, line 2 (p. 15). -/
noncomputable def tau2 : ℝ := 1 / 2

/-- The epoch-dependent step size `α_s = 1/(3 τ_{1,s} L)` of Algorithm 2, line 5 (p. 15). -/
noncomputable def alpha (L : ℝ) (s : ℕ) : ℝ := 1 / (3 * tau1 s * L)

/-- The linear coupling `x_{k+1} = τ₁ z_k + τ₂ x̃ + (1 - τ₁ - τ₂) y_k` (Algorithm 2, line 9;
Lemma 2.6, p. 10), with `τ₂ = 1/2`. -/
noncomputable def coupling {d : ℕ} (τ1 : ℝ) (xt y z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  τ1 • z + tau2 • xt + (1 - τ1 - tau2) • y

/-- The SVRG gradient estimator `∇̃_{k+1} = ∇f(x̃) + ∇fᵢ(x_{k+1}) - ∇fᵢ(x̃)` for the index `i`
(Algorithm 2, lines 6 and 10, p. 15), with `∇f = (1/n) ∑ᵢ ∇fᵢ`. -/
noncomputable def gradEst {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xt x : EuclideanSpace ℝ (Fin d)) (i : Fin n) : EuclideanSpace ℝ (Fin d) :=
  SAGA.Convex.gradAvg f' xt + f' i x - f' i xt

/-- One inner iteration of Algorithm 2 (lines 9–12, Option I, p. 15) with weight `τ₁`, step `α`
and snapshot `x̃`, from `(y_k, z_k)` with the random index `i`; it returns `(y_{k+1}, z_{k+1})`.
`P γ v` plays the role of the proximal point `argmin_u {ψ(u) + 1/(2γ) ‖u - v‖²}`:
* `z_{k+1} = argmin_z {1/(2α) ‖z - z_k‖² + ⟨∇̃, z⟩ + ψ(z)} = P α (z_k - α ∇̃)`,
* `y_{k+1} = argmin_y {3L/2 ‖y - x_{k+1}‖² + ⟨∇̃, y⟩ + ψ(y)} = P (1/(3L)) (x_{k+1} - ∇̃/(3L))`. -/
noncomputable def innerStep {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L τ1 α : ℝ)
    (xt : EuclideanSpace ℝ (Fin d))
    (yz : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  let x := coupling τ1 xt yz.1 yz.2
  let g := gradEst f' xt x i
  (P (1 / (3 * L)) (x - (1 / (3 * L)) • g), P α (yz.2 - α • g))

end Katyusha.NonSC


