-- Prove2me | Definitions.Def_KMedianPP_Tight_EqualMass
-- name    : KMedianPP_Tight_EqualMass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:02:03.791082+00:00
-- url     : https://prove2.me/theorems/0506a337-7532-4cfe-a941-056ba396ea5a
-- title:
--   §4.2 — the equal-mass process, $R_{r,s}$, $p_{r,s}$, $B_{k,\Delta}$ and the payment $\Phi_{r,s}(A,U)$
-- statement:
--   **Equal-mass process.** For a permanent weight $\Gamma>0$: $r$ removable items of weight $1$ and one permanent item of weight $\Gamma$; each step samples an item with probability proportional to its weight; a sampled removable item is removed (a hit), the permanent item leaves the state unchanged (a miss). With $j$ removable items left a step is a hit with probability $j/(j+\Gamma)$. $J$ is the number of removable items left after $s$ steps.
--
--   `jLaw Γ r s j` $=\Pr[J=j]$, defined by conditioning on the first step: $\Pr_{r,0}[J=j]=[j=r]$ and $\Pr_{r,s+1}[J=j]=\frac{\Gamma}{r+\Gamma}\Pr_{r,s}[J=j]+\frac{r}{r+\Gamma}\Pr_{r-1,s}[J=j]$.
--
--   $$R_{r,s}=\mathbb E[J],\qquad p_{r,s}=\mathbb E\Big[\frac{J}{\Delta+J}\Big],$$
--   where $J/(\Delta+J)$ is read as $1$ when $\Delta=J=0$ (footnote 5). So $R_{r,0}=r$, $R_{0,s}=0$, and (11) $R_{r,s}=\frac{\Gamma}{r+\Gamma}R_{r,s-1}+\frac{r}{r+\Gamma}R_{r-1,s-1}$ holds.
--
--   **The constant.** For integers $k\ge1$, $\Delta\ge0$,
--   $$B_{k,\Delta}=\begin{cases}1+H_{k-1}, & \Delta=0,\\[2pt] 1+\dfrac{R_{k-1,k+\Delta-1}}{\Delta}, & \Delta>0,\end{cases}$$
--   where for $\Delta>0$ the equal-mass process has $\Gamma=\Delta$, and $H_j=\sum_{i=1}^j 1/i$ (Mathlib's `harmonic`, $H_0=0$).
--
--   **Payment (12).** With $m=r+\Delta-s$ past misses, $\bar u=U/r$ and $\bar a=A/\Gamma$,
--   $$\Phi_{r,s}(A,U)=m\,p_{r,s}\,\bar u+\big(R_{r,s}-m\,p_{r,s}\big)\bar a\quad(r\ge1),\qquad \Phi_{0,s}(A,U)=0.$$
--
--   **Formalization Note.** `R Γ r s`, `p Γ Δ r s` are finite sums over $j\le r$ against `jLaw`; `chargeRatio Δ j` is footnote 5's ratio. In `Phi`, $m$ is computed in $\mathbb R$ (no truncated subtraction); the statements using it assume $s\le r+\Delta$. `B` is used for $k\ge1$.
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), pp. 16–18 (PDF 18–20), §4.2: the equal-mass process, (11), the definition of B_{k,Δ}, (12); p. 23 (PDF 25), footnote 5

import Mathlib

set_option autoImplicit false

namespace KMedianPP.Tight

open Finset

/-! Kaplan, Naori, *Tight Bounds for k-Median++ and Improved Bounds for k-Means++*, STOC 2027
submission (manuscript sha256 f017529e…), §4.2 (pp. 16–18, 21, 23): the equal-mass process, the
expected number `R_{r,s}` of removable items left, the charging probability `p_{r,s}`, the
constant `B_{k,Δ}` and the payment `Φ_{r,s}(A, U)` of (12).

The equal-mass process with permanent weight `Γ > 0` starts with `r` removable items of weight `1`
and one permanent item of weight `Γ`; each step samples an item proportionally to its weight; a
removable item sampled is removed (a hit), the permanent item leaves the state unchanged (a miss).
With `j` removable items left, a step is a hit with probability `j/(j + Γ)`. `J` is the number of
removable items left after `s` steps. -/

/-- The law of `J`: `jLaw Γ r s j = Pr[J = j]` for the equal-mass process with permanent weight
`Γ`, started with `r` removable items and run for `s` steps, defined by conditioning on the first
step (a miss with probability `Γ/(r + Γ)` keeps `r` items, a hit with probability `r/(r + Γ)`
leaves `r - 1`). Used for `Γ > 0`. -/
noncomputable def jLaw (Γ : ℝ) : ℕ → ℕ → ℕ → ℝ
  | r, 0, j => if j = r then 1 else 0
  | r, s + 1, j => Γ / (r + Γ) * jLaw Γ r s j + r / (r + Γ) * jLaw Γ (r - 1) s j

/-- `R_{r,s} = E[J]`, the expected number of removable items left after `s` steps from `r`
(`J ≤ r` always). -/
noncomputable def R (Γ : ℝ) (r s : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), (j : ℝ) * jLaw Γ r s j

/-- The charging ratio `J/(Δ + J)`, read as `1` when `Δ = J = 0` (footnote 5, p. 23). -/
noncomputable def chargeRatio (Δ j : ℕ) : ℝ :=
  if Δ + j = 0 then 1 else (j : ℝ) / ((Δ : ℝ) + j)

/-- `p_{r,s} = E[J/(Δ + J)]` (p. 18), with footnote 5's convention at `Δ = J = 0`; the law of `J`
is that of the equal-mass process with permanent weight `Γ`. -/
noncomputable def p (Γ : ℝ) (Δ r s : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), chargeRatio Δ j * jLaw Γ r s j

/-- `B_{k,Δ}` (p. 16): `1 + H_{k-1}` for `Δ = 0`, and `1 + R_{k-1,k+Δ-1}/Δ` for `Δ > 0`, where the
equal-mass process has permanent weight `Γ = Δ`. `H_j = Σ_{i=1}^j 1/i` is Mathlib's `harmonic`
(`H_0 = 0`). Used for `k ≥ 1`. -/
noncomputable def B (k Δ : ℕ) : ℝ :=
  if Δ = 0 then 1 + (harmonic (k - 1) : ℝ)
  else 1 + R (Δ : ℝ) (k - 1) (k + Δ - 1) / (Δ : ℝ)

/-- The payment `Φ_{r,s}(A, U)` of (12) (p. 18): with `m = r + Δ - s` past misses,
`ū = U/r` and `ā = A/Γ`, `Φ_{r,s}(A, U) = m p_{r,s} ū + (R_{r,s} - m p_{r,s}) ā` for `r ≥ 1`, and
`Φ_{0,s}(A, U) = 0`. `m` is computed in `ℝ` (no truncated subtraction); the statements using `Φ`
assume `s ≤ r + Δ`, i.e. `m ≥ 0`. -/
noncomputable def Phi (Γ : ℝ) (Δ r s : ℕ) (A U : ℝ) : ℝ :=
  if r = 0 then 0
  else
    ((r : ℝ) + Δ - s) * p Γ Δ r s * (U / r) +
      (R Γ r s - ((r : ℝ) + Δ - s) * p Γ Δ r s) * (A / Γ)

end KMedianPP.Tight


