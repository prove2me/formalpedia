-- Prove2me | Definitions.Def_KMSHolder_expCut
-- name    : KMSHolder_expCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:07.239068+00:00
-- url     : https://prove2.me/theorems/da9aa68e-f406-46e7-b65d-5cdad4e2d8e4
-- title:
--   Cut-off $u \mapsto e^{z\,\mathrm{clamp}(u,-N,N)}$
-- statement:
--   For $N \in \mathbb N$ and $z \in \mathbb C$ let
--
--   $$
--   e_{N,z}(u) = \exp\big(z \cdot \max(-N, \min(N, u))\big), \qquad u \in \mathbb R ,
--   $$
--
--   a bounded continuous function on $\mathbb R$. As $N \to \infty$, $e_{N,z}(u) \to e^{zu}$ pointwise, and for $\Re z \ge 0$ the family is dominated by $\max(1, |e^{zu}|)$. Applied through the functional calculus of $\log \Delta$, these cut-offs approximate the complex power $\Delta^z = e^{z \log\Delta}$ of the modular operator.
--
--   **Formalization Note** It is the complex-exponent analogue of the published `OAI.BoundedRecovery.halfExponentialCutoff`, $u \mapsto e^{\min(N,u)/2}$. The lower clamp at $-N$ keeps it bounded for every $z$ and does not change the limit for $\Re z \ge 0$.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §2–§4, pp.2–9 (powers Δ^z = e^{−zβL})

import Mathlib

namespace KMSHolder

/-- The cut-off `u ↦ exp(z · clamp(u, −N, N))` with `N = n`, a bounded continuous function on `ℝ`
for every `z ∈ ℂ`. As `N → ∞` it converges pointwise to `u ↦ e^{zu}`, and for `ℜz ≥ 0` it is
dominated by `max(1, |e^{zu}|)`; applied through the spectral calculus of `D = log Δ` it
approximates `Δ^z = e^{zD}` (Jäkel–Robl, arXiv:1103.3608v2, §2–§4, pp.2–9, where `Δ^z` is written
`e^{−zβL}`). It is the complex-exponent analogue of
`OAI.BoundedRecovery.halfExponentialCutoff n = exp(min(n, u)/2)`; the lower clamp at `−N` keeps it
bounded for every `z` and does not change the limit for `ℜz ≥ 0`. -/
noncomputable def expCut (n : ℕ) (z : ℂ) : BoundedContinuousFunction ℝ ℂ :=
  (BoundedContinuousFunction.mkOfCompact
      (⟨fun x : Set.Icc (-(n : ℝ)) n => Complex.exp (z * ((x : ℝ) : ℂ)), by fun_prop⟩ :
        C(Set.Icc (-(n : ℝ)) n, ℂ))).compContinuous
    ⟨Set.projIcc (-(n : ℝ)) n (by have := Nat.cast_nonneg (α := ℝ) n; linarith),
      continuous_projIcc⟩

end KMSHolder


