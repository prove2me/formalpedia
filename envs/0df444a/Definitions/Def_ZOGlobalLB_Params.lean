-- Prove2me | Definitions.Def_ZOGlobalLB_Params
-- name    : ZOGlobalLB_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:48:20.485295+00:00
-- url     : https://prove2.me/theorems/85647ed3-0fcd-47c0-9d47-830398c31f7e
-- title:
--   Explicit constants, scales and the parameter choice
-- statement:
--   The explicit constants of the construction: $c_*=37$, $C_*=9147$, $C_N=2^{128}$, $B=\min\{\Delta H,L_0^2\}$, $a_T=e_*^2/(12H_*)$, $a_\sigma=9e_*^2/(64C_N)$, $c_0=\min\{a_T/8,\ e_*^2/(81C_*^2),\ a_\sigma\}$, $a_N=2^{-19}$, the prefactor $c=2^{-19}a_Ta_\sigma/12$; the parameter choice $T=\lfloor a_TB/\epsilon^2\rfloor$, $\sigma^2=a_\sigma L_0^2/\epsilon^2$, $s=m-T+1$, $\ell_0=\lfloor s^2\sigma^2/(2048m)\rfloor$, $N_0=\lfloor a_NdT\sigma^2\rfloor$; the scales $b=\epsilon H_*/(e_*H)$ and $\lambda=\epsilon^2H_*/(e_*^2H)$; and the future-projection error $p_{\mathrm{bad}}=2(N+1)Te^{-(r-T)/(32R^2)}$.
--
--   **Formalization Note.** Floors are `Nat.floor` of nonnegative reals; $r=\lfloor d/2\rfloor$ and $m=d-r$ are natural numbers.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma E.1, p.66; (126); (138), p.70; Lemma F.1, (150)–(151), (157), pp.74–77

import Mathlib
import Definitions.Def_ZOGlobalLB_Fnew

namespace ZOGlobalLB

/-! # Explicit constants and the parameter choice

Xia, Yuan, arXiv:2610.19652, Lemma E.1, p.66 (`c* = 37`, `C* = 9147`), (138), p.70,
Theorem D.1 (`C_N = 2¹²⁸`), and Lemma F.1, pp.74–77, (150), (151), (157).

**Formalization Note.** `B = min{ΔH, L₀²}` (3). Integer parts are `Nat.floor` (`⌊·⌋₊`), applied
to nonnegative arguments. `r = ⌊d/2⌋` is `d / 2` in `ℕ`, `m = d - r`, `s = m - T + 1`
(natural subtraction; the theorems state `T ≤ m`). -/

/-- `c* = 37` (p.66). -/
noncomputable def cStar : ℝ := 37

/-- `C* = 9147` (p.66). -/
noncomputable def CStar : ℝ := 9147

/-- The global noise-moment constant `C_N = 2¹²⁸` (Theorem D.1, p.56). -/
noncomputable def CN : ℝ := 2 ^ 128

/-- `B = min{ΔH, L₀²}` (3), p.4. -/
noncomputable def Bmin (Δ H L₀ : ℝ) : ℝ := min (Δ * H) (L₀ ^ 2)

/-- `a_T = e*²/(12H*)` (150), p.75. -/
noncomputable def aT : ℝ := eStar ^ 2 / (12 * Hstar)

/-- `a_σ = 9e*²/(64C_N)` (150), p.75. -/
noncomputable def aSigma : ℝ := 9 * eStar ^ 2 / (64 * CN)

/-- `c₀ = min{a_T/8, e*²/(81C*²), a_σ}` (150), p.75. -/
noncomputable def c0 : ℝ := min (min (aT / 8) (eStar ^ 2 / (81 * CStar ^ 2))) aSigma

/-- `a_N = 2⁻¹⁹` (p.75). -/
noncomputable def aN : ℝ := 1 / 2 ^ 19

/-- The prefactor `c = 2⁻¹⁹ a_T a_σ / 12` (157), p.77. -/
noncomputable def cPref : ℝ := aN * aT * aSigma / 12

/-- The number of stages `T = ⌊a_T B/ϵ²⌋` (151), p.75. -/
noncomputable def Tpar (Δ H L₀ ε : ℝ) : ℕ := ⌊aT * Bmin Δ H L₀ / ε ^ 2⌋₊

/-- The noise scale `σ = √(a_σ L₀²/ϵ²)` (151), p.75. -/
noncomputable def sigmaPar (L₀ ε : ℝ) : ℝ := Real.sqrt (aSigma * L₀ ^ 2 / ε ^ 2)

/-- The residual stage dimension `s = m - T + 1` (138), p.70. -/
def sPar (m T : ℕ) : ℕ := m - T + 1

/-- The per-stage budget `ℓ₀ = ⌊s²σ²/(2048m)⌋` (138), p.70. -/
noncomputable def ell0 (m T : ℕ) (σ : ℝ) : ℕ := ⌊(sPar m T : ℝ) ^ 2 * σ ^ 2 / (2048 * m)⌋₊

/-- The query budget `N₀ = ⌊a_N d T σ²⌋` (p.75). -/
noncomputable def N0par (d T : ℕ) (σ : ℝ) : ℕ := ⌊aN * d * T * σ ^ 2⌋₊

/-- The spatial scale `b = ϵH*/(e*H)` (46), p.26; (126), p.66. -/
noncomputable def bScale (ε H : ℝ) : ℝ := ε * Hstar / (eStar * H)

/-- The value scale `λ = ϵ²H*/(e*²H)` (46), p.26; (126), p.66. -/
noncomputable def lamScale (ε H : ℝ) : ℝ := ε ^ 2 * Hstar / (eStar ^ 2 * H)

/-- The future-projection error `p_bad = 2(N + 1)T exp(-(r - T)/(32R²))` (44), (143), with
`R = 64√T`. -/
noncomputable def pBad (N T r : ℕ) : ℝ :=
  2 * (N + 1) * T * Real.exp (-((r : ℝ) - T) / (32 * Rc T ^ 2))

end ZOGlobalLB


