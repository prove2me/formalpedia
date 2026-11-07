-- Prove2me | Definitions.Def_KMeansTaper_SFI
-- name    : KMeansTaper_SFI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:01.831909+00:00
-- url     : https://prove2.me/theorems/8ce19de6-ab20-46ba-b977-2b01427ac404
-- title:
--   The finite inequality $\mathrm{SFI}(\kappa,c)$
-- statement:
--   Fix reals $\kappa$ and $c$. $\mathrm{SFI}(\kappa,c)$ says: for every finite index set $\mathcal I$ with probability weights $\pi$ (write $\mathbb E_i$ for the $\pi$-average over $i$), every family of data
--
--   1. $D_i\ge0$ with $\mathbb E_iD_i=1$, and $\delta_i=\sqrt{D_i}$;
--   2. $q_{ti}\in[0,1]$ and $r_i=\mathbb E_t q_{ti}$;
--   3. $s_i\in[0,1]$, $x\in[0,1]$, $y\in(0,1]$, and $\lambda=cP(x)$;
--   4. $\rho_i\ge0$ with $\rho_i(1-\lambda q_{ti})\le\delta_i+\delta_t$ whenever $q_{ti}<1$ (2),
--
--   satisfies, with $a=1+m(x)+\kappa P(x)y$, $\Theta=P(x)(y-x)^2/y$ and $X_i=D_i+2\delta_i\rho_i(1-\lambda s_i)+\rho_i^2\bigl(1-(2\lambda-\lambda^2)s_i\bigr)$,
--
--   $$\Phi_{\mathrm{SFI}}:=\mathbb E_i\Bigl[(1-r_i)X_i+ar_iD_i+\kappa Pyr_i+\tfrac{\kappa}{2}Ps_i(1-yr_i)(1+D_i)-\mathbb E_t(1-q_{ti})(D_t-aD_i)_+\Bigr]\le(1+\kappa)+\kappa\Theta. \quad (3)$$
--
--   This finite inequality is the only analytic input of the reduction theorem (Theorem 3.1): the drift of the squared tapered process is an SFI configuration.
--
--   **Formalization Note** The index set is $\{0,\dots,N-1\}$ and expectations are weighted finite sums; the weights are nonnegative with sum $1$. `q t i` is $q_{ti}$ (the first index is $t$). $P$ and $m$ are evaluated at $x$. The left side of (3) is `sfiPhi`.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Definition 2.2, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_KMeansTaper_coefP

namespace KMeansTaper

/-- **The left side `Φ_SFI` of inequality (3)**, Definition 2.2, p.4 (PDF p.7).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

For a finite configuration indexed by `Fin N` with probability weights `wt`, data `D`, `q`
(`q t i` is the paper's `q_{ti}`), `s`, `ρ` and reals `x`, `y`, with `λ = c P(x)`,
`δ_i = √D_i`, `r_i = E_t q_{ti}`, `a = 1 + m(x) + κ P(x) y` and
`X_i = D_i + 2 δ_i ρ_i (1 - λ s_i) + ρ_i² (1 - (2λ - λ²) s_i)`, this is
`E_i[(1 - r_i) X_i + a r_i D_i + κ P y r_i + (κ/2) P s_i (1 - y r_i)(1 + D_i)
  - E_t (1 - q_{ti})(D_t - a D_i)_+]`.

**Formalization Note.** Expectations are `wt`-weighted finite sums over `Fin N`; `P` and `m` are
evaluated at `x`. -/
noncomputable def sfiPhi (κ c : ℝ) (N : ℕ) (wt D : Fin N → ℝ) (q : Fin N → Fin N → ℝ)
    (s ρ : Fin N → ℝ) (x y : ℝ) : ℝ :=
  let lam := c * coefP x
  let a := 1 + coefM κ x + κ * coefP x * y
  let r : Fin N → ℝ := fun i => ∑ t, wt t * q t i
  let X : Fin N → ℝ := fun i =>
    D i + 2 * Real.sqrt (D i) * ρ i * (1 - lam * s i) + ρ i ^ 2 * (1 - (2 * lam - lam ^ 2) * s i)
  ∑ i, wt i * ((1 - r i) * X i + a * r i * D i + κ * coefP x * y * r i
      + κ / 2 * coefP x * s i * (1 - y * r i) * (1 + D i)
      - ∑ t, wt t * ((1 - q t i) * max (D t - a * D i) 0))

/-- **The finite inequality `SFI(κ, c)`**, Definition 2.2, p.4 (PDF p.7): for every finite
index set with probability weights, every `D_i ≥ 0` with `E_i D_i = 1`, `q_{ti} ∈ [0, 1]`,
`s_i ∈ [0, 1]`, `x ∈ [0, 1]`, `y ∈ (0, 1]` and `ρ_i ≥ 0` with
`ρ_i (1 - λ q_{ti}) ≤ δ_i + δ_t` whenever `q_{ti} < 1` (2), where `λ = c P(x)`, inequality (3)
`Φ_SFI ≤ (1 + κ) + κ Θ` holds, `Θ = P(x)(y - x)²/y`.

**Formalization Note.** The finite index set is `Fin N`; the weights `wt` are nonnegative with
sum `1` (so `N ≥ 1`); `q t i` is the paper's `q_{ti}` (first index `t`), so
`r_i = ∑_t wt_t q_{ti}`. The left side is `sfiPhi`. -/
def SFI (κ c : ℝ) : Prop :=
  ∀ (N : ℕ) (wt D : Fin N → ℝ) (q : Fin N → Fin N → ℝ) (s ρ : Fin N → ℝ) (x y : ℝ),
    (∀ i, 0 ≤ wt i) → ∑ i, wt i = 1 →
    (∀ i, 0 ≤ D i) → ∑ i, wt i * D i = 1 →
    (∀ t i, 0 ≤ q t i ∧ q t i ≤ 1) → (∀ i, 0 ≤ s i ∧ s i ≤ 1) →
    0 ≤ x → x ≤ 1 → 0 < y → y ≤ 1 → (∀ i, 0 ≤ ρ i) →
    (∀ t i, q t i < 1 → ρ i * (1 - c * coefP x * q t i) ≤ Real.sqrt (D i) + Real.sqrt (D t)) →
    sfiPhi κ c N wt D q s ρ x y ≤ (1 + κ) + κ * (coefP x * (y - x) ^ 2 / y)

end KMeansTaper


