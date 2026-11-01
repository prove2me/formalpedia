-- Prove2me | Definitions.Def_TSDRiem_eta
-- name    : TSDRiem_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:28.059747+00:00
-- url     : https://prove2.me/theorems/925843ed-abea-43bd-b4b1-a9c79f521465
-- title:
--   Decrease constant $\eta$ of Lemma 4.4 and Theorem 4.5
-- statement:
--   The sufficient decrease constant of Lemma 4.4 and Theorem 4.5 is
--
--   $$
--   \eta:=\frac{L_{\min}^2\,(1-\sqrt m\,\gamma)^2}{4L_{\max}\big(L_{\min}^2+L_f^2(m-1)m\big)} ,
--   $$
--
--   where $L_k$ are the block smoothness constants, $L_f$ is the smoothness constant of $f$, $m$ is the number of inner steps and $\gamma$ the gap parameter. An outer iteration whose inner loop stays within distance $r$ decreases $f$ by at least $\eta\|\nabla f(x^{t-1})\|^2$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.4, p.13; Theorem 4.5, p.14

import Mathlib
import Definitions.Def_TSDRiem_Lmax
import Definitions.Def_TSDRiem_Lmin

namespace TSDRiem

/-- The sufficient decrease constant of Lemma 4.4 and Theorem 4.5,
`η := L²_min (1 − √m γ)² / (4 L_max (L²_min + L²_f (m − 1) m))`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.4, p.13,
and Theorem 4.5, p.14.

Formalization Note: `m − 1` is real subtraction. -/
noncomputable def eta (m : ℕ) (L : Fin m → ℝ) (Lf γ : ℝ) : ℝ :=
  Lmin L ^ 2 * (1 - Real.sqrt m * γ) ^ 2 /
    (4 * Lmax L * (Lmin L ^ 2 + Lf ^ 2 * ((m : ℝ) - 1) * m))

end TSDRiem


