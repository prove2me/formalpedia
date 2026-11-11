-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_Filter
-- name    : CaiFourierSparse_Learning_Filter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:11:21.321596+00:00
-- url     : https://prove2.me/theorems/505d3169-c2d1-416a-9cf1-fa4fe7dd6e33
-- title:
--   The filter $M_{\ell,r,\delta}$ and the constants $C_M$, $C_H$, $\Delta_{\ell,\delta}$
-- statement:
--   Let $C\ge64$ be an even integer. With $\mathrm{sinc}(u)=\sin(\pi u)/(\pi u)$, $\mathrm{sinc}(0)=1$ (`nsinc`), $\mathrm{rect}_a=\frac1a\mathbf 1_{[-a/2,a/2]}$ (`rect`), $h=\frac\ell\delta\min\{r,\frac\ell\delta\}$ (eq. (70), `filterH`), $\alpha_M=1-\frac1{Ch}$ and
--   $$g_M(t)=\mathrm{sinc}(Cht)^{C\lceil\log(r/\delta)\rceil}\prod_{i=0}^{\lceil\log r\rceil}\mathrm{sinc}\Big(\frac{Ct}{h^{-1}+4^i/r^2}\Big)^{C2^i}\qquad\text{(eq. (71), `gM`)},$$
--   the filter is $M_{\ell,r,\delta}=s_M\,(\mathrm{rect}_{2\alpha_M}*g_M)$, with $s_M$ chosen so that $M_{\ell,r,\delta}(0)=1$ (eq. (72); `filterRaw`, `filterM`), and $M_{\ell,\delta}=M_{\ell,\ell,\delta}$ (`filterMl`); `filtered` is the product $M\cdot z$. Logarithms in the construction are base $2$. The constants are $C_M=4C^2$ (`constCM`), $C_H=8C_M$ (`constCH`) and $\Delta_{\ell,\delta}=C_M\frac{\ell^2}{\delta}\log\frac\ell\delta$ (`filterDelta`).
--
--   **Formalization Note.** $C_M=4C^2$ is read off the paper: (67) states $\operatorname{supp}\widehat M\subset[-\Delta_M,\Delta_M]$ with $\Delta_M=\frac{C_M}2(\frac\ell\delta\min\{r,\frac\ell\delta\}\log\frac{\ell r}\delta+\frac{\ell r}\delta)$, and Claim 6.5(5) bounds the same radius by $2C^2(\cdots)$. The base-2 logarithm follows the printed $\lceil\log_2 r\rceil$ in the Fourier transform of (72).
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), §6, eqs. (67), (70)–(72), Claim 6.5, Lemma 6.3, Corollary 6.4, printed pp. 32–33 (PDF pp. 34–35)

import Mathlib

namespace CaiFourierSparse.Learning

open MeasureTheory

/-! # The filter `M_{ℓ,r,δ}` and the constants `C_M`, `C_H`, `Δ_{ℓ,δ}`
(Cai–Chen–Shao–Wang, §6, eqs. (67), (70)–(72), Claim 6.5, Lemma 6.3, Corollary 6.4)

`C ≥ 64` is an even integer (the construction's constant). With `h = (ℓ/δ) · min{r, ℓ/δ}` and
`α_M = 1 - 1/(Ch)`,
`g_M(t) = sinc(C h t)^{C ⌈log(r/δ)⌉} · ∏_{i=0}^{⌈log r⌉} sinc(C t / (h⁻¹ + 4^i/r²))^{C 2^i}`
and `M_{ℓ,r,δ} = s_M · (rect_{2α_M} * g_M)` with `s_M` chosen so that `M_{ℓ,r,δ}(0) = 1`.
Logarithms in the construction are base 2 (the Fourier transform of (72) prints `⌈log₂ r⌉`).
`C_M = 4C²` is the constant of (67) (`Δ_M = (C_M/2)(…)` in (67) and `Δ_M ≤ 2C²(…)` in Claim 6.5),
`C_H = 8 C_M` and `Δ_{ℓ,δ} = C_M ℓ² log(ℓ/δ)/δ`. -/

/-- The normalized sinc, `sinc(u) = sin(πu)/(πu)`, `sinc(0) = 1`. -/
noncomputable def nsinc (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.sin (Real.pi * u) / (Real.pi * u)

/-- `rect_a(t) = 1/a` on `[-a/2, a/2]` and `0` elsewhere. -/
noncomputable def rect (a t : ℝ) : ℝ := if |t| ≤ a / 2 then 1 / a else 0

/-- `h = (ℓ/δ) · min{r, ℓ/δ}`, eq. (70). -/
noncomputable def filterH (ℓ r : ℕ) (δ : ℝ) : ℝ := ((ℓ : ℝ) / δ) * min (r : ℝ) ((ℓ : ℝ) / δ)

/-- `g_M`, eq. (71). -/
noncomputable def gM (C ℓ r : ℕ) (δ t : ℝ) : ℝ :=
  let h := filterH ℓ r δ
  nsinc (C * h * t) ^ (C * Nat.ceil (Real.logb 2 ((r : ℝ) / δ))) *
    ∏ i ∈ Finset.range (Nat.ceil (Real.logb 2 (r : ℝ)) + 1),
      nsinc (C * t / (h⁻¹ + (4 : ℝ) ^ i / (r : ℝ) ^ 2)) ^ (C * 2 ^ i)

/-- The unnormalized filter `(rect_{2α_M} * g_M)(t) = ∫ rect_{2α_M}(s) g_M(t - s) ds`,
`α_M = 1 - 1/(C h)`. -/
noncomputable def filterRaw (C ℓ r : ℕ) (δ t : ℝ) : ℝ :=
  ∫ s, rect (2 * (1 - 1 / (C * filterH ℓ r δ))) s * gM C ℓ r δ (t - s)

/-- The filter `M_{ℓ,r,δ} = s_M · (rect_{2α_M} * g_M)`, with `s_M` such that `M_{ℓ,r,δ}(0) = 1`,
eq. (72). -/
noncomputable def filterM (C ℓ r : ℕ) (δ t : ℝ) : ℝ :=
  filterRaw C ℓ r δ t / filterRaw C ℓ r δ 0

/-- `M_{ℓ,δ} = M_{ℓ,ℓ,δ}` (Lemma 6.3). -/
noncomputable def filterMl (C ℓ : ℕ) (δ t : ℝ) : ℝ := filterM C ℓ ℓ δ t

/-- The constant `C_M = 4 C²` of (67). -/
def constCM (C : ℕ) : ℝ := 4 * (C : ℝ) ^ 2

/-- The constant `C_H = 8 C_M` of Corollary 6.4. -/
def constCH (C : ℕ) : ℝ := 8 * constCM C

/-- `Δ_{ℓ,δ} = C_M · (ℓ²/δ) · log(ℓ/δ)` (Lemma 6.3), the Fourier-support radius of `M_{ℓ,δ}`. -/
noncomputable def filterDelta (C ℓ : ℕ) (δ : ℝ) : ℝ :=
  constCM C * ((ℓ : ℝ) ^ 2 / δ) * Real.logb 2 ((ℓ : ℝ) / δ)

/-- The signal `M_{ℓ,r,δ} · z`. -/
noncomputable def filtered (C ℓ r : ℕ) (δ : ℝ) (z : ℝ → ℂ) (t : ℝ) : ℂ :=
  (filterM C ℓ r δ t : ℂ) * z t

end CaiFourierSparse.Learning


