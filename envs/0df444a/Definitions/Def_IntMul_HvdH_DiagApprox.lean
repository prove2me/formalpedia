-- Prove2me | Definitions.Def_IntMul_HvdH_DiagApprox
-- name    : IntMul_HvdH_DiagApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T23:16:16.965205+00:00
-- url     : https://prove2.me/theorems/e40dadfd-d564-4fb2-a9f3-a3b5cc04b57e
-- title:
--   Fixed-point approximation of the diagonal resampling map $\mathcal D'$ (Harvey–van der Hoeven Lemma 4.8)
-- statement:
--   Computable approximation of the diagonal map $\mathcal D'=\mathcal D/2^{2\alpha^2-2}$ of Gaussian resampling. Its entries are $d'_\ell=e^{\pi\alpha^2\beta_\ell^2}/2^{2\alpha^2-2}$, where $\beta_\ell=t\ell/s-\mathrm{round}(t\ell/s)$.
--
--   * `kOf s t l` $=k_\ell=(t\ell-s\,\mathrm{round}(t\ell/s))^2$, so that $\alpha^2\beta_\ell^2=\alpha^2k_\ell/s^2$. Here round is computed as $\lfloor(2t\ell+s)/(2s)\rfloor$.
--   * `dTilde p s t α l` is the approximation `expPos p (s²) (α² k_ℓ) (2α²-2)` of $2^pd'_\ell$ (Lemma 2.14).
--   * `Dapprox p s t α U l` multiplies the fixed-point input $U_\ell\in\mathbb Z[i]$ by `dTilde` and divides by $2^p$, rounding each component towards zero.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.8 and Section 4.2 (definition of D)

import Definitions.Def_IntMul_HvdH_RealExp

/-! Fixed-point approximation of the diagonal map `D' = D / 2^{2α²-2}` of Gaussian resampling
(Harvey–van der Hoeven Lemma 4.8). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and a
fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `k_ℓ = (tℓ - s·round(tℓ/s))²`, so that `α² β_ℓ² = α² k_ℓ / s²`. -/
def kOf (s t l : ℕ) : ℕ :=
  (((t * l : ℕ) : ℤ) - (s : ℤ) * (((2 * t * l + s) / (2 * s) : ℕ) : ℤ)).natAbs ^ 2

/-- Approximation of `2^p d'_ℓ = 2^p e^{πα²β_ℓ²} / 2^{2α²-2}` via `expPos` (Lemma 2.14). -/
def dTilde (p s t α l : ℕ) : ℤ := expPos p (s ^ 2) (α ^ 2 * kOf s t l) (2 * α ^ 2 - 2)

/-- Lemma 4.8: `(D̃' U)_ℓ = ρ(d̃'_ℓ U_ℓ)`, rounding each component towards zero. -/
def Dapprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  ((dTilde p s t α l * (U l).1).tdiv (2 ^ p), (dTilde p s t α l * (U l).2).tdiv (2 ^ p))

end IntMul.HvdH


