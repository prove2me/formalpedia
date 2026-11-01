-- Prove2me | Definitions.Def_ExploreLQMFG_Master
-- name    : ExploreLQMFG_Master
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:46.337982+00:00
-- url     : https://prove2.me/theorems/bb499499-b8fd-4629-a7ee-82f22e1b8ee9
-- title:
--   Classical solutions with bounded derivatives of the master equation (1.8)
-- statement:
--   Fix $T>0$, $\varepsilon>0$, the Riccati solution $\eta$ and maps $Q^\dagger f$, $R^\dagger g$. A function $\theta:[0,T]\times\mathbb R^d\to\mathbb R^d$ is a classical solution of the master equation (1.8)
--   $$\partial_t\theta(t,x)+\frac{\varepsilon^2}2\Delta_x\theta(t,x)-\big(\eta_tx+\theta(t,x)\big)\cdot\nabla_x\theta(t,x)+Q^\dagger f(x)-\eta_t\theta(t,x)=0,\qquad \theta(T,\cdot)=R^\dagger g,$$
--   when
--
--   1. $\theta$ is continuous on $[0,T]\times\mathbb R^d$;
--   2. $\theta$ is $C^{1,2}$ on $[0,T)\times\mathbb R^d$: the time derivative and the first and second spatial derivatives exist and are jointly continuous there;
--   3. the equation holds on $[0,T)\times\mathbb R^d$, with $\Delta_x$ the componentwise Laplacian and $(v\cdot\nabla_x)\theta=\sum_jv_j\partial_j\theta$;
--   4. $\theta(T,x)=R^\dagger g(x)$ for every $x$;
--   5. $\theta$ and $\nabla_x\theta$ are bounded on $[0,T)\times\mathbb R^d$.
--
--   The Jacobian $\nabla_x\theta$ is the matrix with entries $(\nabla_x\theta)_{ij}=\partial_j\theta^i$, the orientation for which $k_t=\nabla_x\theta(t,m_t)$ in (2.18).
--
--   **Formalization Note** "Classical solution (with bounded derivatives)" (p.4) is read as items 1–5. Second derivatives cannot be bounded up to $T$ because $g$ is only Lipschitz, and Lemma 2.8 bounds $\nabla_x\theta$ on $[0,T)$.
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), (1.8) p.4, (2.18) p.22, Lemma 2.8 p.23

import Mathlib
import Definitions.Def_ExploreLQMFG_Model

open MeasureTheory Filter Topology
open scoped NNReal Matrix

namespace ExploreLQMFG

/-- The Jacobian matrix `∇ₓθ(t, x)` of `θ(t, ·) : ℝᵈ → ℝᵈ`, with entries
`(∇ₓθ)ᵢⱼ = ∂ⱼθⁱ(t, x)`, so that `(∇ₓθ) v = Σⱼ vⱼ ∂ⱼθ` (the orientation for which
`k_t = ∇ₓθ(t, m_t)` in (2.18) of arXiv:2107.00839v2, p.22). Computed from Mathlib's `fderiv`. -/
noncomputable def gradMat {d : ℕ} (θ : ℝ → (Fin d → ℝ) → (Fin d → ℝ)) (t : ℝ)
    (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => fderiv ℝ (θ t) x (Pi.single j 1) i

/-- `θ : [0, T] × ℝᵈ → ℝᵈ` is a classical solution, with bounded derivatives, of the master
equation (1.8) of arXiv:2107.00839v2 (p.4):

`∂ₜθ(t, x) + (ε²/2) Δₓθ(t, x) − (η_t x + θ(t, x)) · ∇ₓθ(t, x) + Q†f(x) − η_t θ(t, x) = 0`,
`θ(T, ·) = R†g(·)`,

with `Qf = Q†f`, `Rg = R†g`. Precisely:
1. `θ` is continuous on `[0, T] × ℝᵈ`;
2. on `[0, T) × ℝᵈ`, `θ` is `C^{1,2}`: there are a time derivative `θₜ`, a spatial derivative
   `Dθ` and a second spatial derivative `D²θ`, all jointly continuous on `[0, T) × ℝᵈ`
   (`θₜ` one-sided at `t = 0`);
3. the equation holds on `[0, T) × ℝᵈ`, with `Δₓθ = Σₗ D²θ(eₗ, eₗ)` (the componentwise
   Laplacian) and the transport term `(η_t x + θ) · ∇ₓθ = Dθ(η_t x + θ) = Σⱼ (η_t x + θ)ⱼ ∂ⱼθ`;
4. `θ(T, x) = R†g(x)` for every `x`;
5. `θ` and `∇ₓθ` are bounded on `[0, T) × ℝᵈ`.

**Formalization Note.** p.4 says "a unique classical solution (with bounded derivatives)". The
mission reads this as items 1–5: `g` is only Lipschitz, so second derivatives cannot be bounded
up to `t = T`, and Lemma 2.8 bounds `∇ₓθ` on `[0, T)`. The page writes `Δ²ₓₓ` for the
Laplacian. -/
def IsClassicalSol {d : ℕ} (T : ℝ≥0) (ε : ℝ) (η : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Qf Rg : (Fin d → ℝ) → (Fin d → ℝ)) (θ : ℝ → (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  ContinuousOn (fun p : ℝ × (Fin d → ℝ) => θ p.1 p.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
    (∃ (θt : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
        (Dθ : ℝ → (Fin d → ℝ) → ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)))
        (D2θ : ℝ → (Fin d → ℝ) → ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))),
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
        HasDerivWithinAt (fun s => θ s x) (θt t x) (Set.Ico (0 : ℝ) T) t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, HasFDerivAt (θ t) (Dθ t x) x) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, HasFDerivAt (Dθ t) (D2θ t x) x) ∧
      ContinuousOn (fun p : ℝ × (Fin d → ℝ) => θt p.1 p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℝ × (Fin d → ℝ) => Dθ p.1 p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℝ × (Fin d → ℝ) => D2θ p.1 p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
        θt t x + (ε ^ 2 / 2) • (∑ l, D2θ t x (Pi.single l 1) (Pi.single l 1))
          - Dθ t x (η t *ᵥ x + θ t x) + Qf x - η t *ᵥ θ t x = 0) ∧
    (∀ x, θ T x = Rg x) ∧
    (∃ M : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, eNorm (θ t x) ≤ M) ∧
    (∃ M : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, frob (gradMat θ t x) ≤ M)

end ExploreLQMFG


