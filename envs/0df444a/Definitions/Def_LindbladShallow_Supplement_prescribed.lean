-- Prove2me | Definitions.Def_LindbladShallow_Supplement_prescribed
-- name    : LindbladShallow_Supplement_prescribed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:18:45.159402+00:00
-- url     : https://prove2.me/theorems/d82b1d4e-b43a-4169-84d3-432bd8ac9af1
-- title:
--   The prescribed execution of §3.3 — windows $r$, periods $M$ and step $h=\tau/M$ (Eq. (15))
-- statement:
--   The prescribed execution of Section 3.3 fixes, for a valid input, how each segment of duration $\tau=T/N_0$ is cut into collision periods and windows. With the coarse-graining length $R$ of Eq. (11), the support-box volume $v_*=(9R)^D$, the threshold $s_0=(256\cdot 7)^{-2}$, the collision constant $C_{\mathrm{col}}=8(\kappa+1)$ and $a=\lambda T$,
--   $$
--   r=2^{\lceil \log_2\max\{1,\lambda\tau v_*/s_0\}\rceil},\qquad
--   M=\min\Bigl\{2^k:\ 2^k\ge \max\Bigl\{r,\ \tfrac{16C_{\mathrm{col}}na^2}{N_0\epsilon}\Bigr\}\Bigr\},\qquad h=\frac{\tau}{M}.
--   $$
--   So $r$ windows of $M/r$ consecutive periods each make up a segment, and every forward window has action at most $s_0$.
--
--   These are the classical data of the local factors $W_C$ to which Theorem 5.1 applies.
--
--   **Formalization Note** The least power of two at least a real $y$ is written $2^{\lceil\log_2\lceil y\rceil\rceil}$ with natural-number logarithms (`Nat.clog 2`); for $y\ge 1$ this is $2^{\lceil\log_2 y\rceil}$.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §3.3, Eq. (15), p.20; v∗ p.19; C_col p.13 and p.60

import Mathlib
import Definitions.Def_LindbladShallow_localDecomp

open scoped Matrix ComplexOrder

namespace LindbladShallow

namespace Supplement

/-- The window-action threshold `s₀ = (256·7)^{−2}` (arXiv:2610.05362, held version sha256
8f4637ef…, §3.3, p.20). -/
noncomputable def s0 : ℝ := 1 / (256 * 7 : ℝ) ^ 2

/-- The support-box volume `v∗ = (9R)^D`, `R = 2r∗m∗` of Eq. (11) (§3.3, p.19). -/
noncomputable def vstar {P : Params} (I : Instance P) : ℝ := (9 * (Rlen I : ℝ)) ^ P.D

/-- The collision constant `C_col := 8(κ + 1)` (§2.3, p.13; repeated after Eq. (63), p.60; used in
Eq. (15)). -/
def Ccol (P : Params) : ℕ := 8 * (P.κ + 1)

/-- The prescribed number of windows `r = 2^{⌈log₂ max{1, λτv∗/s₀}⌉}` (§3.3, p.20).

**Formalization Note** For a real `y ≥ 1`, `2^{⌈log₂ y⌉}` is the least power of two `≥ y`, which is
the least power of two `≥ ⌈y⌉`, i.e. `2^{Nat.clog 2 ⌈y⌉}`. -/
noncomputable def rPres {P : Params} (I : Instance P) : ℕ :=
  2 ^ Nat.clog 2 ⌈max 1 (lam I * tau I * vstar I / s0)⌉₊

/-- The prescribed number of collision periods `M`: the least power of two at least
`max{r, 16 C_col n a² / (N₀ ϵ)}`, `a = λT` (Eq. (15), p.20). -/
noncomputable def Mpres {P : Params} (I : Instance P) : ℕ :=
  2 ^ Nat.clog 2 (max (rPres I)
    ⌈16 * (Ccol P : ℝ) * (I.n : ℝ) * (lam I * (I.T : ℝ)) ^ 2 / ((N0 I : ℝ) * (I.ε : ℝ))⌉₊)

/-- The prescribed collision step `h = τ/M` (Eq. (15), p.20). -/
noncomputable def hPres {P : Params} (I : Instance P) : ℝ := tau I / (Mpres I : ℝ)

end Supplement

end LindbladShallow


