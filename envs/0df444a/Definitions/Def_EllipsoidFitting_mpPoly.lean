-- Prove2me | Definitions.Def_EllipsoidFitting_mpPoly
-- name    : EllipsoidFitting_mpPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:34.439347+00:00
-- url     : https://prove2.me/theorems/3bd1ddf7-0b41-4824-ad9d-c6e676c37b59
-- title:
--   The Marchenko–Pastur polynomial basis $q_t^{(\gamma)}$
-- statement:
--   For a real $\gamma$, the polynomials $q_t=q_t^{(\gamma)}$ are defined by
--   $$
--   q_0(x)=1,\qquad q_1(x)=x-1,\qquad q_{t+1}(x)=\bigl(x-(1+\gamma)\bigr)q_t(x)-\gamma\,q_{t-1}(x)\quad(t\ge1).
--   $$
--   For $0<\gamma<1$ they are orthogonal for the Marchenko–Pastur law with ratio $\gamma$; the paper uses them to invert $A$.
--
--   **Formalization Note** Defined for every real $\gamma$; each statement carries the paper's range of $\gamma$.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Definition 2.14, p.18 (PDF p.20)

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

open Polynomial

/-- **The Marchenko–Pastur polynomial basis.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Definition 2.14,
p.18: "q(γ)_0(x) = 1, q(γ)_1(x) = x − 1, and, for t ≥ 1, q(γ)_{t+1}(x) = (x − (1 + γ)) q(γ)_t(x)
− γ · q(γ)_{t−1}(x)."

`mpPoly γ t` is the polynomial `q_t^{(γ)}`.

**Formalization Note** The recurrence is defined for every real `γ`; Definition 2.14 fixes
`0 < γ < 1`, and every statement about `q_t` carries its own range of `γ`. -/
noncomputable def mpPoly (γ : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - 1
  | t + 2 => (X - C (1 + γ)) * mpPoly γ (t + 1) - C γ * mpPoly γ t

end EllipsoidFitting


