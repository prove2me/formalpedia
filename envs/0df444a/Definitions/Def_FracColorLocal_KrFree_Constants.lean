-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Constants
-- name    : FracColorLocal_KrFree_Constants
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:32.282201+00:00
-- url     : https://prove2.me/theorems/0de50fc9-a438-4e98-8365-92d0437acced
-- title:
--   The explicit constants C_ent, C_loss, t∗, C△, c_r, R_t and δ(t)
-- statement:
--   The absolute constants of §8 and (6.1):
--
--   $$C_{\mathrm{ent}}=20+12\cdot 24^2,\qquad C_{\mathrm{loss}}=24(C_{\mathrm{ent}}+1),\qquad t_*=(100\,C_{\mathrm{loss}})^4,\qquad C_\triangle=2^{t_*},$$
--
--   and, for an integer $r\ge 4$ and an integer $t\ge 32$,
--
--   $$c_r=\frac{1}{1+96\,C_\triangle\,r},\qquad R_t=2^t,\qquad \delta(t)=\frac{2C_{\mathrm{loss}}\lceil\log_2 t\rceil}{\lfloor\sqrt t\rfloor}.$$
--
--   $C_\triangle$ is the constant of the structural dichotomy (Lemma 5.1), $c_r$ the constant chosen in (6.1) for Theorem 1.7, $R_t$ the neighbourhood-ratio bound and $\delta(t)$ the loss allowance of a reduction step (8.1).
--
--   **Formalization Note** `Cent`, `Closs`, `tStar`, `Ctri`, `Rt t` are natural numbers, `cr r : ℚ`, and `deltaT t : ℝ` uses `Nat.clog 2 t` $=\lceil\log_2 t\rceil$ and `Nat.sqrt t` $=\lfloor\sqrt t\rfloor$ (both exact for $t\ge 1$).
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 33 (PDF 34), §8 and (8.1); p. 24 (PDF 25), (6.1)

import Mathlib

namespace FracColorLocal.KrFree

/-- `C_ent := 20 + 12 · 24²` (§8). -/
def Cent : ℕ := 20 + 12 * 24 ^ 2

/-- `C_loss := 24 (C_ent + 1)` (§8). -/
def Closs : ℕ := 24 * (Cent + 1)

/-- `t∗ := (100 C_loss)⁴` (§8). -/
def tStar : ℕ := (100 * Closs) ^ 4

/-- `C△ := 2^{t∗}` (§8), the constant of Lemma 5.1. -/
def Ctri : ℕ := 2 ^ tStar

/-- `c_r := 1 / (1 + 96 C△ r)` (6.1). -/
noncomputable def cr (r : ℕ) : ℚ := 1 / (1 + 96 * (Ctri : ℚ) * r)

/-- `R_t := 2^t` (8.1). -/
def Rt (t : ℕ) : ℕ := 2 ^ t

/-- `δ(t) := 2 C_loss ⌈log₂ t⌉ / ⌊√t⌋` (8.1); `Nat.clog 2 t = ⌈log₂ t⌉` and
`Nat.sqrt t = ⌊√t⌋` for `t ≥ 1`. -/
noncomputable def deltaT (t : ℕ) : ℝ := (2 * (Closs : ℝ) * (Nat.clog 2 t : ℝ)) / (Nat.sqrt t : ℝ)

end FracColorLocal.KrFree


