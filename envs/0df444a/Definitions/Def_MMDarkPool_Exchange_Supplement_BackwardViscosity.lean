-- Prove2me | Definitions.Def_MMDarkPool_Exchange_Supplement_BackwardViscosity
-- name    : MMDarkPool_Exchange_Supplement_BackwardViscosity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:21:36.553535+00:00
-- url     : https://prove2.me/theorems/94420e96-e61b-4344-a701-d04c07973c71
-- title:
--   (3.2), p. 8 — per-component viscosity solutions of backward time-only systems
-- statement:
--   For any component type $I$, terminal time $T\in\mathbb R$, terminal data $g:I\to\mathbb R$, and Hamiltonian $F:I\times\mathbb R^I\to\overline{\mathbb R}$, this defines the per-component backward viscosity notion for
--   $$
--   \partial_t v(t,q)+F(q,v(t,\cdot))=0,\qquad v(T,q)=g(q).
--   $$
--   For every $q\in I$, the function $t\mapsto v(t,q)$ must be continuous on $[0,T]$ and have terminal value $g(q)$. For every $C^1$ test function $\varphi:\mathbb R\to\mathbb R$ and every $t_0\in(0,T)$, a local maximum of $v(\cdot,q)-\varphi$ requires $\varphi'(t_0)+F(q,v(t_0,\cdot))\ge0$; a local minimum requires the reverse inequality. Coupling uses the entire solution row, not the test function.
--
--   This separates the general time-only solution notion from the market model. Theorem 1 applies it with $I=\mathbb Z$, $g=-1$, and the Hamiltonian of (3.2).
--
--   **Formalization Note.** The paper does not define viscosity solution. This is the same interior-time, componentwise convention as in the published base model, with arbitrary component type and terminal data and no imposed grid. No claim of well-posedness for an arbitrary Hamiltonian is made by this definition.
--
--   Differences from the source:
--   - generalization: Equation (3.2) has integer inventory components and terminal value −1. → The solution interface permits any component type, Hamiltonian, horizon and terminal data.; reason: Specializing to ℤ, F P, P.T and constant −1 recovers exactly the model interface; this definition asserts no existence or uniqueness result.
--   - reading: The paper does not define viscosity solution. → Continuous component rows, terminal data, and C¹ tests at interior times with backward signs and own-row coupling.; reason: This makes the implicit time-only solution convention explicit without adding a theorem premise.
--   - encoding: The Hamiltonian is expressed as a real supremum. → The Hamiltonian argument has type EReal; a real derivative is added to it.; reason: This preserves suprema without a real totality default; specialization to the model has finite values under Standing.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, p. 8, HJB (3.2) and terminal condition; viscosity notion made explicit (paper silent).

import Mathlib

namespace MMDarkPool.Exchange.Supplement

/-!
Per-component viscosity solutions of backward, time-only systems.

Theorem 1 and (3.2), arXiv:1912.01129v1, p. 8, do not specify the viscosity
notion. This makes explicit the same convention as the published exchange
model, independently of its finite grid and market-specific parameters.
At interior times, test one component in time and evaluate all coupling
terms on the solution's own row. Continuity and terminal data are required.
-/

/-- Viscosity solution of `∂ₜv(t,q) + F(q,v(t,·)) = 0`, `v(T,q) = g(q)`.
Subsolutions have the backward sign `≥ 0` at local maxima; supersolutions
have `≤ 0` at local minima. No topology on the component type is needed. -/
def IsBackwardViscositySolution {ι : Type*} (T : ℝ)
    (F : ι → (ι → ℝ) → EReal) (g : ι → ℝ) (v : ℝ → ι → ℝ) : Prop :=
  ∀ q : ι,
    ContinuousOn (fun t => v t q) (Set.Icc 0 T) ∧ v T q = g q ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∀ t₀ ∈ Set.Ioo 0 T,
      IsLocalMax (fun t => v t q - φ t) t₀ →
        0 ≤ ((deriv φ t₀ : ℝ) : EReal) + F q (v t₀)) ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∀ t₀ ∈ Set.Ioo 0 T,
      IsLocalMin (fun t => v t q - φ t) t₀ →
        ((deriv φ t₀ : ℝ) : EReal) + F q (v t₀) ≤ 0)

end MMDarkPool.Exchange.Supplement


