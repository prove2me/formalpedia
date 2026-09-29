-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_dualFunction
-- name    : PhiDivRobust_Counterpart_dualFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:48:46.032989+00:00
-- url     : https://prove2.me/theorems/7027a642-c507-4029-a08b-c189b19fbcdb
-- title:
--   Lagrange function L(p, λ, η) of the worst-case problem (14) and dual objective g(λ, η) = sup_{p ≥ 0} L
-- statement:
--   Fix $a\in\mathbb R^n$, $B\in\mathbb R^{n\times m}$, $C\in\mathbb R^{k\times m}$, $d\in\mathbb R^k$, $q\in\mathbb R^m$, $\rho\in\mathbb R$, a φ-divergence function $\phi$ and a decision $x\in\mathbb R^n$. The **Lagrange function** of the worst-case problem $\max\{(a+Bp)^\top x \mid p\ge0,\ Cp\le d,\ I_\phi(p,q)\le\rho\}$ is
--
--   $$L(p,\lambda,\eta) = (a+Bp)^\top x + \rho\lambda - \lambda\sum_{i=1}^m q_i\phi(p_i/q_i) + \eta^\top(d - Cp)$$
--
--   for $p\in\mathbb R^m$, $\lambda\in\mathbb R$, $\eta\in\mathbb R^k$, and the **dual objective function** is
--
--   $$g(\lambda,\eta) = \sup_{p\ge0} L(p,\lambda,\eta)\in\mathbb R\cup\{\pm\infty\}.$$
--
--   Duality between the worst-case problem and $\min_{\lambda,\eta\ge0} g(\lambda,\eta)$ is the core of the proof of Theorem 1.
--
--   **Formalization Note** $L$ is the real part minus $\lambda I_\phi(p,q)$ computed in `EReal` (so $L=-\infty$ where $\lambda>0$ and $I_\phi(p,q)=+\infty$, and $0\cdot(+\infty)=0$ at $\lambda=0$). The paper writes $\max_{p\ge0}$; it is formalized as a supremum, since it need not be attained and may be $+\infty$.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, proof of Theorem 1, the Lagrange function and the dual objective function after (14)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_phiDiv
open Matrix

namespace PhiDivRobust.Counterpart

/-- The Lagrange function of the worst-case problem (14) (Ben-Tal et al. 2013, p. 347, proof of
Theorem 1): `L(p, λ, η) = (a + Bp)ᵀx + ρλ − λ ∑ᵢ qᵢ φ(pᵢ/qᵢ) + ηᵀ(d − Cp)`, valued in `EReal`. -/
noncomputable def lagrangian {n m k : ℕ} (φ : ℝ → EReal) (a : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ)
    (q : Fin m → ℝ) (ρ : ℝ) (x : Fin n → ℝ) (p : Fin m → ℝ) (lam : ℝ) (η : Fin k → ℝ) : EReal :=
  (((a + B *ᵥ p) ⬝ᵥ x + ρ * lam + η ⬝ᵥ (d - C *ᵥ p) : ℝ) : EReal) - (lam : EReal) * phiDiv φ p q

/-- The dual objective function `g(λ, η) = max_{p ≥ 0} L(p, λ, η)` (Ben-Tal et al. 2013, p. 347,
proof of Theorem 1). The paper's `max` is read as a supremum in `EReal` (it need not be attained and
may be `+∞`). -/
noncomputable def dualFunction {n m k : ℕ} (φ : ℝ → EReal) (a : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ)
    (q : Fin m → ℝ) (ρ : ℝ) (x : Fin n → ℝ) (lam : ℝ) (η : Fin k → ℝ) : EReal :=
  ⨆ p ∈ {p : Fin m → ℝ | 0 ≤ p}, lagrangian φ a B C d q ρ x p lam η

end PhiDivRobust.Counterpart


