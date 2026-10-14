-- Prove2me | Definitions.Def_IntMul_HvdH_RealExp
-- name    : IntMul_HvdH_RealExp
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T22:21:35.693152+00:00
-- url     : https://prove2.me/theorems/cb8f0289-982c-4879-9621-4b0c6bcf9f42
-- title:
--   Fixed-point real exponentials $e^{-\pi j/k}$ and $2^{-\sigma}e^{\pi j/k}$ (Harvey–van der Hoeven Lemmas 2.13–2.14)
-- statement:
--   Computable integer approximations of real exponentials.
--
--   * `expNegFix n M X` approximates $2^n e^{X/2^M}$ for an integer $X\le0$: writing $X/2^M=z-\tau\log 2$ with $\tau=\lfloor -X/L\rfloor$, where $L$ = `log2Bits M`, it approximates $2^Me^{z}$ with `expBits` and divides by $2^{M-n+\tau}$, rounding to nearest.
--   * `expNeg n k j` approximates $2^n e^{-\pi j/k}$: it returns $0$ when $j>kn$ and otherwise applies `expNegFix` at precision $M=2n+10$ to $-\lfloor \mathrm{piBits}(M)\,j/k\rfloor$.
--   * `expPos n k j σ` approximates $2^n\,2^{-\sigma}e^{\pi j/k}$ by applying `expNegFix` to $\min(0,\lfloor \mathrm{piBits}(M)\,j/k\rfloor-\sigma\,\mathrm{log2Bits}(M))$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemmas 2.13 and 2.14 (real exponentials)

import Definitions.Def_IntMul_HvdH_Numeric
import Definitions.Def_IntMul_HvdH_ExpApprox

/-! Fixed-point real exponentials `e^{-πj/k}` and `2^{-σ} e^{πj/k}`
(Harvey–van der Hoeven Lemmas 2.13 and 2.14). -/

namespace IntMul.HvdH

/-- Approximation of `2^n exp(X / 2^M)` for `X ≤ 0`: write `X / 2^M = z - τ log 2` with
`z ∈ (-log 2, 0]` (using the `M`-bit approximation `log2Bits M`), approximate `2^M e^z` with
`expBits`, and divide by `2^{M - n + τ}` with rounding to nearest. -/
def expNegFix (n M : ℕ) (X : ℤ) : ℤ :=
  let L := log2Bits M
  let τ := (-X) / L
  let u := (expBits M (X + τ * L) 0).1
  let s := M - n - 1 + τ.toNat
  (u + 2 ^ s) / 2 ^ (s + 1)

/-- Approximation of `2^n e^{-πj/k}` (Lemma 2.13). -/
def expNeg (n k j : ℕ) : ℤ :=
  if k * n < j then 0
  else expNegFix n (2 * n + 10) (-(piBits (2 * n + 10) * j / k))

/-- Approximation of `2^n · 2^{-σ} e^{πj/k}`, meaningful when `e^{πj/k} ≤ 2^σ` (Lemma 2.14). -/
def expPos (n k j σ : ℕ) : ℤ :=
  expNegFix n (2 * n + 10)
    (min 0 (piBits (2 * n + 10) * j / k - σ * log2Bits (2 * n + 10)))

end IntMul.HvdH


