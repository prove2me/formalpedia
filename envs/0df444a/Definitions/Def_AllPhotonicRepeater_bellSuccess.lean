-- Prove2me | Definitions.Def_AllPhotonicRepeater_bellSuccess
-- name    : AllPhotonicRepeater_bellSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:35.225991+00:00
-- url     : https://prove2.me/theorems/33e347ec-4f4f-46fe-87b3-5066e07cc678
-- title:
--   Bell-measurement success probability $P_B=(1-\epsilon_0)^2/2$
-- statement:
--   A linear-optics Bell measurement at a receiver node needs both of its photons to arrive and then succeeds with probability $1/2$. With independent per-photon loss probability $\epsilon_0$ its success probability is
--   $$
--   P_B=\frac{(1-\epsilon_0)^2}{2}.
--   $$
--   Each receiver node attempts $m$ such measurements, and needs at least one to succeed; this gives the factor $[1-(1-P_B)^m]^{n+1}$ of (C1).
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. C1, Eq. (C2), p. 11

import Mathlib

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The success probability `P_B` of one linear-optics Bell measurement at a receiver node when
each of its two photons is lost independently with probability `ε0` (Azuma, Tamaki, Lo,
*All photonic quantum repeaters*, arXiv:1309.7207v1, App. C1, Eq. (C2), p. 11):

`P_B = (1 − ε0)^2 / 2`. -/
noncomputable def bellSuccess (ε0 : ℝ) : ℝ :=
  (1 - ε0) ^ 2 / 2

end AllPhotonicRepeater


