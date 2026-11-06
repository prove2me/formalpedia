-- Prove2me | Definitions.Def_LawLocalComp_upperMoment
-- name    : LawLocalComp_upperMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:11.623821+00:00
-- url     : https://prove2.me/theorems/a4216fb6-95eb-4491-b93d-786facd75216
-- title:
--   Upper moment $\mathbb E[Y\mathbf 1\{Y>t\}]$
-- statement:
--   For a law $Y$ and $t\in\mathbb R$,
--   $$\mathbb E[Y\mathbf 1\{Y>t\}]=\sum_{y>t} y\,\mathbb P(Y=y).$$
--   It is the moment term of the call certificates (6) and of Lemmas 4.1–4.3.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), (6), p.4

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The upper moment `E[Y 1{Y > t}]`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), (6), p.4, and Lemmas 4.1–4.3, pp.6–7.

`upperMoment Y t = ∑_{y > t} y · P(Y = y)`. -/
noncomputable def upperMoment (Y : Law) (t : ℝ) : ℝ := ∑ y ∈ Y.w.support with t < y, Y.w y * y

end LawLocalComp


