-- Prove2me | Definitions.Def_IntMul_HvdH_EApprox
-- name    : IntMul_HvdH_EApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T23:59:46.246774+00:00
-- url     : https://prove2.me/theorems/81fa5413-4677-4553-a965-d6a46df28a0b
-- title:
--   Truncated fixed-point approximation of the off-diagonal map $\mathcal E$ (Harvey–van der Hoeven Lemma 4.11)
-- statement:
--   Computable approximation of the map $\mathcal E=\mathcal N-I$ from §4.2 of Harvey–van der Hoeven, where
--   $$(\mathcal Eu)_\ell=\sum_{h\ne0}e^{-\pi\alpha^2\left((th/s+\beta_\ell)^2-\beta_{\ell+h}^2\right)}\,u_{(\ell+h)\bmod s}.$$
--   Here $\beta_\ell=t\ell/s-\mathrm{round}(t\ell/s)$.
--
--   * `bOf s t ℓ` $=b_\ell=s\beta_\ell=t\ell-s\lfloor(2t\ell+s)/(2s)\rfloor$.
--   * `eKz s t ℓ h` $=K_{\ell,h}=(th+b_\ell)^2-b_{\ell+h}^2$, so the $(\ell,\ell+h)$ entry of $\mathcal E$ is $e^{-\pi\alpha^2K_{\ell,h}/s^2}$.
--   * `eWidth p α` $=m=\lceil\lceil\sqrt p\rceil/\alpha\rceil+1$ is the truncation half-width.
--   * `eTerm p s t α ℓ U h` is the rounded product $\lfloor\tilde x_hU_{(\ell+h)\bmod s}/2^p\rceil_0$. Here $\tilde x_h$ = `expNeg p (s²) (α² K)` approximates $2^pe^{-\pi\alpha^2K_{\ell,h}/s^2}$. The term is $0$ for $h=0$.
--   * `Eapprox p s t α U ℓ` sums `eTerm` over $|h|\le m$.
--   * `Eexact s t α u ℓ` is the exact value $(\mathcal Eu)_\ell$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.11

import Definitions.Def_IntMul_HvdH_SApprox

/-! Fixed-point approximation of the off-diagonal part `E = N - I` of the normalised resampling
system (Harvey–van der Hoeven Lemma 4.11). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and a
fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `b_ℓ = tℓ - s·round(tℓ/s) = s β_ℓ`, with `round(x) = ⌊x + 1/2⌋`. -/
def bOf (s t : ℕ) (l : ℤ) : ℤ := t * l - s * ((2 * t * l + s) / (2 * s))

/-- `K_{ℓ,h} = (th + b_ℓ)² - b_{ℓ+h}²`, so that the entry of `E` is `e^{-πα² K_{ℓ,h}/s²}`. -/
def eKz (s t : ℕ) (l h : ℤ) : ℤ := (t * h + bOf s t l) ^ 2 - bOf s t (l + h) ^ 2

/-- Truncation half-width `m = ⌈⌈√p⌉/α⌉ + 1` of Lemma 4.11. -/
def eWidth (p α : ℕ) : ℕ := (ceilSqrt p + α - 1) / α + 1

/-- One term `ρ(x̃_h U_{ℓ+h})` of the truncated sum (zero for `h = 0`), where
`x̃_h ≈ 2^p e^{-πα² K_{ℓ,h}/s²}` is computed by `expNeg` (Lemma 2.13) and the product is rounded
towards zero. -/
def eTerm (p s t α l : ℕ) (U : ℕ → ℤ × ℤ) (h : ℤ) : ℤ × ℤ :=
  if h = 0 then (0, 0) else
  let x := expNeg p (s ^ 2) (α ^ 2 * (eKz s t l h).toNat)
  let V := U ((l + h) % s).toNat
  ((x * V.1).tdiv (2 ^ p), (x * V.2).tdiv (2 ^ p))

/-- Lemma 4.11: `(Ẽ U)_ℓ = ∑_{0 < |h| ≤ m} eTerm h`, i.e. the sum over `h = i - m` for
`i < 2m + 1` (the term `h = 0` vanishes). -/
def Eapprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  let m : ℕ := eWidth p α
  (∑ i ∈ Finset.range (2 * m + 1), (eTerm p s t α l U ((i : ℤ) - m)).1,
    ∑ i ∈ Finset.range (2 * m + 1), (eTerm p s t α l U ((i : ℤ) - m)).2)

/-- The exact entries `e_{ℓ,h} = e^{-πα² K_{ℓ,h}/s²}` for `h ≠ 0`, and `0` for `h = 0`. -/
noncomputable def eEx (s t α : ℕ) (l h : ℤ) : ℝ :=
  if h = 0 then 0 else Real.exp (-(Real.pi * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2))

/-- The exact map `(E u)_ℓ = ∑_{h ≠ 0} e^{-πα²((th/s + β_ℓ)² - β_{ℓ+h}²)} u_{(ℓ+h) mod s}`. -/
noncomputable def Eexact (s t α : ℕ) (u : ℕ → ℂ) (l : ℕ) : ℂ :=
  ∑' h : ℤ, ((eEx s t α l h : ℝ) : ℂ) * u ((l + h) % s).toNat

end IntMul.HvdH


