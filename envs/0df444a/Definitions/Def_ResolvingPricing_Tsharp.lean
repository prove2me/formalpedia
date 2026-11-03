-- Prove2me | Definitions.Def_ResolvingPricing_Tsharp
-- name    : ResolvingPricing_Tsharp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:32.693684+00:00
-- url     : https://prove2.me/theorems/01433218-b2d1-4032-b288-88d91463a12d
-- title:
--   The stopping time $T^\sharp$ of (8)
-- statement:
--   Let $x_T\in(\underline d,\lambda^u)$ and let $\xi_t$ be the demand noises of a run, with harmonic series $\bar\xi_{\to t}$. Put
--   $$\gamma=\min\Big\{x_T-\underline d,\ \lambda^u-x_T,\ \frac{r'(x_T)}{2|r''(x_T)|}\Big\}.$$
--   The time index $T^\sharp$ is
--   $$T^\sharp:=\max\{\tau\ge1:\ |\bar\xi_{\to\tau-1}|>\gamma\}\ \vee\ \Big\lceil \frac{2|r''(x_T)|B_\xi}{r'(x_T)}+1\Big\rceil,$$
--   and $T^\sharp:=T$ if $T<\lceil 2|r''(x_T)|B_\xi/r'(x_T)\rceil$.
--
--   Intuitively, $T^\sharp$ is the first period (counting backward) at which the resolving heuristic's normalized inventory may leave $[\underline d,\lambda^u]$. Lemma 1 bounds $\mathbb E[T^\sharp]$ independently of $T$, and the regret is reduced to quantities that live before or after $T^\sharp$.
--
--   **Formalization Note** The maximum ranges over $2\le\tau\le T$ (an empty maximum is $0$): the period $\tau=1$ would involve $\bar\xi_{\to0}$, which contains $\xi_1/0$, and it never changes $T^\sharp$ because the second term is at least $1$. As printed, $T^\sharp=T+1$ when $T=\lceil 2|r''(x_T)|B_\xi/r'(x_T)\rceil$; this value is kept.
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4.1 p.3543, Eq. (8)

import Mathlib
import Definitions.Def_ResolvingPricing_Run

open MeasureTheory

namespace ResolvingPricing

/-- `γ = min{x_T − d̲, λᵘ − x_T, r′(x_T)/(2|r″(x_T)|)}`, the threshold in (8), p.3543 (and, written
`−r′(x_T)/2r″(x_T)` for its last entry, the denominator of (10), p.3544). -/
noncomputable def gammaT (P : Model) (x : ℝ) : ℝ :=
  min (min (x - P.dlo) (P.lamU - x)) (P.r1 x / (2 * |P.r2 x|))

/-- **The time index `T♯` of (8)**, Wang & Wang, Oper. Res. 70(6) (2022), p.3543:
`T♯ := max{τ ≥ 1 : |ξ̄→τ−1| > γ} ∨ ⌈2|r″(x_T)|B_ξ/r′(x_T) + 1⌉`, and `T♯ := T` if
`T < ⌈2|r″(x_T)|B_ξ/r′(x_T)⌉`. Here `e τ` is the demand noise `ξ_τ` of period `τ`, `ξ̄→t` its harmonic
series and `x` is `x_T`.

**Formalization Note.** The maximum runs over the periods `2 ≤ τ ≤ T` (an empty maximum is `0`). The
period `τ = 1` would involve `ξ̄→0`, which contains `ξ_1/0`; leaving it out never changes `T♯`, since
the second term `⌈2|r″(x_T)|B_ξ/r′(x_T) + 1⌉` is at least `1`. The ceilings are `Nat.ceil` of
nonnegative reals (under the assumptions `r′(x_T) > 0` for `x_T < λᵘ`). As printed, `T♯ = T + 1` when
`T = ⌈2|r″(x_T)|B_ξ/r′(x_T)⌉`; this value is kept. -/
noncomputable def Tsharp (P : Model) (T : ℕ) (x : ℝ) (e : ℕ → ℝ) : ℕ :=
  if T < ⌈2 * |P.r2 x| * P.Bξ / P.r1 x⌉₊ then T
  else max (((Finset.Icc 2 T).filter (fun τ => gammaT P x < |harm T e (τ - 1)|)).sup id)
    ⌈2 * |P.r2 x| * P.Bξ / P.r1 x + 1⌉₊

/-- `T♯` of (8) along a run: the harmonic series are those of the run's own noises (in the paper, the
noises of the resolving run). -/
noncomputable def Run.Tsharp {P : Model} {T : ℕ} {x : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ℱ : Filtration ℕ mΩ} (ρ : Run P T x μ ℱ) (ω : Ω) : ℕ :=
  ResolvingPricing.Tsharp P T x (fun τ => ρ.xiB τ ω)

end ResolvingPricing


