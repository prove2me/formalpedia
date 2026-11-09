-- Prove2me | Definitions.Def_AgnosticTNS_opNorm
-- name    : AgnosticTNS_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:12.509605+00:00
-- url     : https://prove2.me/theorems/610b43cb-586c-4b63-83e0-5d38a22a0ebe
-- title:
--   Operator norm $\|\cdot\|_\infty$
-- statement:
--   The operator norm of a matrix $M$ is
--   $$
--   \|M\|_\infty=\sup_{\|x\|\le 1}\|Mx\|,
--   $$
--   with Euclidean norms $\|x\|=(\sum_j|x_j|^2)^{1/2}$.
--
--   **Formalization Note** Written with explicit Euclidean norms, not the sup norm Lean puts on function types.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 2.1, p.11

import Mathlib
open Matrix

namespace AgnosticTNS

/-- **The operator norm `‖·‖_∞`**, p.11 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `‖M‖_∞ = sup_{‖x‖ ≤ 1} ‖Mx‖` with Euclidean norms
`‖x‖ = (Σ_j |x_j|²)^{1/2}`.

**Formalization Note** Written as `sSup` over the closed unit ball of `ℂ^k` with explicit Euclidean
norms (not the sup norm Lean puts on function types); the set is nonempty and bounded. -/
noncomputable def opNorm {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℂ) : ℝ :=
  sSup ((fun x : k → ℂ => Real.sqrt (∑ i, ‖(M *ᵥ x) i‖ ^ 2)) '' {x | ∑ j, ‖x j‖ ^ 2 ≤ 1})

end AgnosticTNS


