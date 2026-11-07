-- Prove2me | Definitions.Def_HZTractability_Lp
-- name    : HZTractability_Lp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:51.098193+00:00
-- url     : https://prove2.me/theorems/6a61a7d2-657a-460f-a0c7-0ccea3daceca
-- title:
--   The endpoints $L$, $U$, the width $w$ and $\eta=\tau w$ (displays (8), (9))
-- statement:
--   With $\gamma=a^2/(1-a^2)$, the price endpoints and width are
--   $$
--   w=U-L=\frac{2}{\gamma K},\qquad L=\frac1{a^2}-\frac{3}{\gamma K},\qquad U=\frac1{a^2}-\frac{1}{\gamma K},
--   $$
--   and, for the parameter $\tau$, $\eta=\tau w$.
--
--   The high price $p_v$ of a vertex is decoded relative to $[L,U]$, and the reference groups pin it inside $[L,U+\eta]$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), displays (8), (9), p.13 (PDF p.15); γ, p.13

import Mathlib

namespace HZTractability

/-- `γ = a²/(1 − a²)` (§4.2, p.13 (PDF 15)). -/
def gam (a : ℚ) : ℚ := a ^ 2 / (1 - a ^ 2)

/-- **The endpoints** `L`, `U` and the width `w` (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, display (8), p.13 (PDF 15)):
"w = U − L = 2/(γK), L = 1/a² − 3/(γK), U = 1/a² − 1/(γK)". This is `L`. -/
def Lp (a : ℚ) (K : ℕ) : ℚ := 1 / a ^ 2 - 3 / (gam a * K)

/-- The upper endpoint `U = 1/a² − 1/(γK)` of display (8), p.13. -/
def Up (a : ℚ) (K : ℕ) : ℚ := 1 / a ^ 2 - 1 / (gam a * K)

/-- The width `w = 2/(γK)` of display (8), p.13. -/
def wp (a : ℚ) (K : ℕ) : ℚ := 2 / (gam a * K)

/-- `η = τ w` (display (9), p.13 (PDF 15): "η = τw, 0 < τ ≤ κ/100"). -/
def eta (a τ : ℚ) (K : ℕ) : ℚ := τ * wp a K

end HZTractability


