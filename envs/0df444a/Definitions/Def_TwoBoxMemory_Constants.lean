-- Prove2me | Definitions.Def_TwoBoxMemory_Constants
-- name    : TwoBoxMemory_Constants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:38.451007+00:00
-- url     : https://prove2.me/theorems/7fc1bd73-ed91-4f5e-a360-8dc21f6f8007
-- title:
--   Log-index walk $z_h$ and the constants $\tau$, $Z_0$, $L_0$, $K_0$, $R$, $K_0^\prime$
-- statement:
--   For $r,s\in(0,1)$, $\beta>0$ and costs $C,D>0$:
--
--   $$A=-\log r,\quad B=-\log s,\quad S=A+B,\quad \alpha=B/S,\quad \tau=e^{-AB/S},$$
--
--   $$Z_0=\max(|\log\beta|,A,B),\quad L_0=\frac{|\log\beta|+Z_0}{S},\quad K_0=e^{\max(A,B)L_0},\quad R=\Bigl\lceil\frac{Z_0}{\min(A,B)}\Bigr\rceil+2,$$
--
--   $$K_0'=K_0\,\frac{\max(C,D)}{\min(p,t)}\,\tau^{-(R+1)} .$$
--
--   Along the greedy word $W$ the **log-index walk** is $z_h=\log\beta-A\,N_A(h)+B\,N_B(h)$, where $N_A(h)$, $N_B(h)$ count the commands strictly before time $h$.
--
--   These are the explicit constants of the upper bound $\Delta_M\le K_0'M\tau^{H_M}$.
--
--   **Formalization Note** $\lceil\cdot\rceil$ is the natural-number ceiling and $\tau^{-(R+1)}$ an integer power. $K_0'$ is the constant written $K$ in (B.12).
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §7, (7.1), p.10 (PDF 12); §B.1, p.21 (PDF 23); (B.10)–(B.12), p.23 (PDF 25)

import Mathlib
import Definitions.Def_TwoBoxMemory_Saddle

namespace TwoBoxMemory

/-!
# The log-index walk and the explicit constants `τ`, `Z₀`, `L₀`, `K₀`, `R`, `K′₀`

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§7 and (7.1), p.10 (PDF 12); §B.1, p.21 (PDF 23); (B.10)–(B.12), p.23 (PDF 25).

`A = −log r`, `B = −log s`, `S = A + B`, `α = B/S`, `τ = e^{−AB/S}`,
`Z₀ = max(|log β|, A, B)`, `L₀ = (|log β| + Z₀)/S`, `K₀ = e^{max(A, B) L₀}`,
`R = ⌈Z₀ / min(A, B)⌉ + 2`, `K′₀ = K₀ max(C, D) / min(p, t) · τ^{−(R+1)}` (the `K` of (B.12)),
and the log-index walk `z_h = log β − A N_A(h) + B N_B(h)` along the greedy word.

**Formalization Note.** `⌈·⌉` is `Nat.ceil`; `τ^{−(R+1)}` is an integer power (`zpow`). The
constants are stated for arbitrary reals; the paper uses them for `r, s ∈ (0, 1)`, `β > 0`,
where `A, B > 0` and every logarithm has a positive argument.
-/

noncomputable section

/-- `A = −log r`. -/
def logA (r : ℝ) : ℝ := -Real.log r

/-- `B = −log s`. -/
def logB (s : ℝ) : ℝ := -Real.log s

/-- `S = A + B`. -/
def logS (r s : ℝ) : ℝ := logA r + logB s

/-- The limiting `A` frequency `α = B/S`. -/
def alpha (r s : ℝ) : ℝ := logB s / logS r s

/-- `τ = exp(−AB/S)`. -/
def tau (r s : ℝ) : ℝ := Real.exp (-(logA r * logB s) / logS r s)

/-- `Z₀ = max(|log β|, A, B)`. -/
def Z0 (r s β : ℝ) : ℝ := max |Real.log β| (max (logA r) (logB s))

/-- `L₀ = (|log β| + Z₀)/S`. -/
def L0 (r s β : ℝ) : ℝ := (|Real.log β| + Z0 r s β) / logS r s

/-- `K₀ = exp(max(A, B) L₀)`. -/
def K0 (r s β : ℝ) : ℝ := Real.exp (max (logA r) (logB s) * L0 r s β)

/-- The run bound `R = ⌈Z₀ / min(A, B)⌉ + 2` of (B.11). -/
def runBound (r s β : ℝ) : ℕ := ⌈Z0 r s β / min (logA r) (logB s)⌉₊ + 2

/-- `K′₀ = K₀ max(C, D) / min(p, t) · τ^{−(R+1)}` of (7.1) (the `K` of (B.12)). -/
def K0' (r s β C D : ℝ) : ℝ :=
  K0 r s β * max C D / min (1 - r) (1 - s) * tau r s ^ (-((runBound r s β : ℤ) + 1))

/-- The log-index walk `z_h = log β − A N_A(h) + B N_B(h)` along the greedy word. -/
def logWalk (r s β : ℝ) (h : ℕ) : ℝ :=
  Real.log β - logA r * (greedyCounts r s β h).1 + logB s * (greedyCounts r s β h).2

end

end TwoBoxMemory


