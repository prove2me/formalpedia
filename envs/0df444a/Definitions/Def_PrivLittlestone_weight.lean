-- Prove2me | Definitions.Def_PrivLittlestone_weight
-- name    : PrivLittlestone_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:28.966677+00:00
-- url     : https://prove2.me/theorems/b3545053-2da1-403f-b82a-44bed69a42a2
-- title:
--   Structural weight $w_S(h) = e^{-\eta\ell_S(h) + a\rho(h)}$
-- statement:
--   For scales $\eta, a > 0$, the **structural weight** of a candidate $h$ after the record sequence $S$ is
--   $$
--   w_S(h) = e^{-\eta \ell_S(h) + a \rho(h)}.
--   $$
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (2), p.5

import Mathlib
import Definitions.Def_PrivLittlestone_cumLoss

namespace PrivLittlestone

/-- The **structural weight** `w_S(h) = e^{−η ℓ_S(h) + a ρ(h)}` (He–He, *Private Online Learning
of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), (2), p.5). -/
noncomputable def weight {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (S : List Z) (h : U) : ℝ :=
  Real.exp (-η * (cumLoss sys S h : ℝ) + a * (sys.ρ h : ℝ))

end PrivLittlestone


