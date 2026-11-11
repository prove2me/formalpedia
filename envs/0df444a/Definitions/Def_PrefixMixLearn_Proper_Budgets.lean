-- Prove2me | Definitions.Def_PrefixMixLearn_Proper_Budgets
-- name    : PrefixMixLearn_Proper_Budgets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:44:50.26921+00:00
-- url     : https://prove2.me/theorems/b2f39abd-2f94-4bca-9ce6-56615ae0ee74
-- title:
--   The selector budgets (B.2) and (B.5): $B_\beta,\beta,\lambda,z,L_f,n_f,B_f,B_s,m$
-- statement:
--   For rational $0<\rho\le1$, dimension $T$, list length $N$ and failure $\delta$:
--   $$B_\beta=\lceil\log_2(16T/\rho)\rceil,\ \beta=2^{-B_\beta},\ \lambda=\gamma=\rho/16,\ z=\frac{\lambda\beta}{8T},\ L_f=\Big\lceil\log_2\frac{2T}{\gamma}\Big\rceil,\ n_f=\Big\lceil\frac{L_f}{2z^2}\Big\rceil,\ B_f=\Big\lceil\log_2\frac1z\Big\rceil$$
--   (B.2), and $B_s=\lceil\log_2(16/\rho)\rceil$, $m=\lceil 32\rho^{-2}\lceil\log_2(2N/\delta)\rceil\rceil$ (B.5).
--
--   **Formalization Note.** Ceilings are `⌈·⌉₊` (natural ceilings) of quantities that are nonnegative in the stated ranges.
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 20 (PDF 22), (B.2); p. 20–21 (PDF 22–23), (B.5)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace PrefixMixLearn.Proper

/-!
# The budgets (B.2) and (B.5) of the fresh factor-one selector

Saravanan, *Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional
Samples*, STOC 2027 submission (manuscript sha256 9c359910…), Lemma B.3, p. 20 (PDF 22), (B.2);
Theorem B.4, pp. 20–21 (PDF 22–23), (B.5).

For rational `0 < ρ ≤ 1`, dimension `T` and list length `N`, failure `δ`:
`B_β = ⌈log₂(16T/ρ)⌉`, `β = 2^{-B_β}`, `λ = γ = ρ/16`, `z = λβ/(8T)`, `L_f = ⌈log₂(2T/γ)⌉`,
`n_f = ⌈L_f/(2z²)⌉`, `B_f = ⌈log₂(1/z)⌉` (B.2); `B_s = ⌈log₂(16/ρ)⌉`,
`m = ⌈32 ρ^{-2} ⌈log₂(2N/δ)⌉⌉` (B.5). Every ceiling is of a quantity `≥ 0` in the stated ranges,
so `⌈·⌉₊` is the paper's ceiling.
-/

/-- `B_β = ⌈log₂(16T/ρ)⌉`. -/
def selBbeta (T : ℕ) (ρ : ℝ) : ℕ := ⌈Real.logb 2 (16 * T / ρ)⌉₊

/-- `β = 2^{-B_β}`. -/
def selBeta (T : ℕ) (ρ : ℝ) : ℝ := (2 : ℝ) ^ (-(selBbeta T ρ : ℤ))

/-- `λ = γ = ρ/16`. -/
def selLambda (ρ : ℝ) : ℝ := ρ / 16

/-- `z = λβ/(8T)`. -/
def selZ (T : ℕ) (ρ : ℝ) : ℝ := selLambda ρ * selBeta T ρ / (8 * T)

/-- `L_f = ⌈log₂(2T/γ)⌉` with `γ = ρ/16`. -/
def selLf (T : ℕ) (ρ : ℝ) : ℕ := ⌈Real.logb 2 (2 * T / selLambda ρ)⌉₊

/-- `n_f = ⌈L_f/(2z²)⌉`. -/
def selNf (T : ℕ) (ρ : ℝ) : ℕ := ⌈(selLf T ρ : ℝ) / (2 * selZ T ρ ^ 2)⌉₊

/-- `B_f = ⌈log₂(1/z)⌉`. -/
def selBf (T : ℕ) (ρ : ℝ) : ℕ := ⌈Real.logb 2 (1 / selZ T ρ)⌉₊

/-- `B_s = ⌈log₂(16/ρ)⌉`. -/
def selBs (ρ : ℝ) : ℕ := ⌈Real.logb 2 (16 / ρ)⌉₊

/-- `m = ⌈32 ρ^{-2} ⌈log₂(2N/δ)⌉⌉`. -/
def selM (ρ δ : ℝ) (N : ℕ) : ℕ := ⌈32 * ρ ^ (-2 : ℤ) * (⌈Real.logb 2 (2 * N / δ)⌉₊ : ℝ)⌉₊

end PrefixMixLearn.Proper


