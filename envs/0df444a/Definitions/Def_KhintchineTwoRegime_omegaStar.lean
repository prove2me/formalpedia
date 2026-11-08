-- Prove2me | Definitions.Def_KhintchineTwoRegime_omegaStar
-- name    : KhintchineTwoRegime_omegaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:33.938465+00:00
-- url     : https://prove2.me/theorems/08902fe5-af7a-4066-83c3-a4e936dae553
-- title:
--   Classical minimizer $\omega^*=(1/\sqrt2,1/\sqrt2,0,\dots,0)$
-- statement:
--   Within the chamber $\mathfrak C$ the unique minimizer of the classical Khintchine inequality is
--   $$
--   \omega^*=\Bigl(\tfrac1{\sqrt2},\tfrac1{\sqrt2},0,\dots,0\Bigr)\in\mathbb R^n,\qquad n\ge2.
--   $$
--   The distance $\tau(\omega)=\|\omega-\omega^*\|_2$ of a proper vector to $\omega^*$ is the parameter of both main theorems.
--
--   **Formalization Note** The first two coordinates (indices 0 and 1) are $1/\sqrt2$ and the rest are $0$. For $n<2$ the vector is truncated; every statement that uses it assumes $n\ge2$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, p.4

import Mathlib

namespace KhintchineTwoRegime

/-- The classical minimizer `ω* = (1/√2, 1/√2, 0, …, 0)` in the proper chamber
(Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, p.4).

**Formalization Note** Coordinates 0 and 1 (the paper's `ω₁, ω₂`) equal `1/√2`, the others
`0`. The paper uses `ω*` for `n ≥ 2`; every statement of the mission that uses it assumes
`n ≥ 2`. -/
noncomputable def omegaStar (n : ℕ) : Fin n → ℝ :=
  fun i => if i.val < 2 then 1 / Real.sqrt 2 else 0

end KhintchineTwoRegime


