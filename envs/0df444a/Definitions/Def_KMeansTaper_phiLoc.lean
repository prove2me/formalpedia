-- Prove2me | Definitions.Def_KMeansTaper_phiLoc
-- name    : KMeansTaper_phiLoc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:03.519385+00:00
-- url     : https://prove2.me/theorems/624e829d-4bd2-4f04-b801-70f6235cf9f5
-- title:
--   The certified expression $\Phi$ at the tight point, the majorant $S$, its Taylor data and the region $N$
-- statement:
--   At the constants of the main certificate, $\kappa=8$, $c=c_{0.85}$, $(\alpha_z,\gamma_z)=(2,6)$, thresholds $(\delta_H,\delta_{lo},\delta_{hi})=(3/8,9/16,2)$, row type $s=0$ and multipliers $\alpha=0$, $\beta(D)=D-1$, the expression of Section 6.1 is
--
--   $$\Phi(x,w,\delta,q,\zeta)=e_{\delta^2,0}(q,\zeta^2)-\Gamma(\delta^2;\zeta^2)+\Gamma(\zeta^2;\delta^2)-0\cdot(\delta^2-1)-(\delta^2-1)(\zeta^2-1).$$
--
--   With $D=\delta^2$, $Z=\zeta^2$ and $\nu=1/(1-cP(x)q)$, the **majorant** of Lemma 6.5 is
--
--   $$S=(1-q)\bigl((1+\nu)\delta+\nu\zeta\bigr)^2+q\bigl[(1+m)D+8P(x)(x+w)(1+D)\bigr]-6D-3Z-(2D+6)P(x)w^2-(D-1)(Z-1),$$
--
--   with $m=m(8,x)$. Write $S_0=S|_{q=0}$, $G_1=\partial_qS|_{q=0}$ and $S_{qq}=\partial_q^2S$. The region is
--
--   $$N=\{x\in[0,1],\ 0\le w\le\tfrac1{16},\ 0\le q\le\tfrac1{128},\ |\delta-1|\le\tfrac1{16},\ |\zeta-1|\le\tfrac1{16}\}.$$
--
--   These are the objects of the local lemma at the tight point (Lemma 6.5), which covers the boxes the branch and bound cannot close.
--
--   **Formalization Note** $w$ is used directly (the paper's $\omega=w/(1-x)$ is not needed on $N$); derivatives are `deriv` in $q$.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 6.1, p.13 (PDF p.16) and Lemma 6.5, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_KMeansTaper_coefP
import Definitions.Def_KMeansTaper_c085
import Definitions.Def_KMeansTaper_CertC

namespace KMeansTaper

/-- **The certified expression `Φ` at the choices of Lemma 6.5**, Section 6.1, p.13 (PDF p.16)
and Lemma 6.5, p.16 (PDF p.19): with `κ = 8`, `c = c_{0.85}`, `(α_z, γ_z) = (2, 6)`, `s = 0`,
`α = 0`, `β(D) = D - 1` and the thresholds `(δ_H, δ_lo, δ_hi) = (3/8, 9/16, 2)` of (K1),
`Φ = e_{δ², 0}(q, ζ²) - Γ(δ²; ζ²) + Γ(ζ²; δ²) - α(δ² - 1) - β(δ²)(ζ² - 1)`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** The variable `w` is used directly (Lemma 6.5's region `N` is stated in
`w`); `c_{0.85}` is the exact rational `KMeansTaper.c085`. -/
noncomputable def phiLoc (x w δ q ζ : ℝ) : ℝ :=
  excess 8 (c085 : ℝ) 2 6 x w (δ ^ 2) 0 q (ζ ^ 2)
    - transfer (3 / 8) (9 / 16) 2 (δ ^ 2) (ζ ^ 2) + transfer (3 / 8) (9 / 16) 2 (ζ ^ 2) (δ ^ 2)
    - 0 * (δ ^ 2 - 1) - (δ ^ 2 - 1) * (ζ ^ 2 - 1)

/-- **The majorant `S` of Lemma 6.5**, p.16 (PDF p.19): with `D = δ²`, `Z = ζ²` and
`ν = 1/(1 - c P(x) q)`,
`S = (1 - q)((1 + ν)δ + νζ)² + q[(1 + m)D + 8P(x)(x + w)(1 + D)] - 6D - 3Z
  - (2D + 6) P w² - (D - 1)(Z - 1)`, with `m = m(8, x)` and `c = c_{0.85}`. -/
noncomputable def Sloc (x w δ q ζ : ℝ) : ℝ :=
  let D := δ ^ 2
  let Z := ζ ^ 2
  let ν := 1 / (1 - (c085 : ℝ) * coefP x * q)
  (1 - q) * ((1 + ν) * δ + ν * ζ) ^ 2
    + q * ((1 + coefM 8 x) * D + 8 * coefP x * (x + w) * (1 + D))
    - 6 * D - 3 * Z - (2 * D + 6) * coefP x * w ^ 2 - (D - 1) * (Z - 1)

/-- `S₀ = S|_{q = 0}`, Lemma 6.5 (a). -/
noncomputable def S0 (x w δ ζ : ℝ) : ℝ := Sloc x w δ 0 ζ

/-- `G₁ = ∂_q S|_{q = 0}`, the first Taylor coefficient of `S` in `q`, Lemma 6.5. -/
noncomputable def G1 (x w δ ζ : ℝ) : ℝ := deriv (fun q => Sloc x w δ q ζ) 0

/-- `S_qq = ∂_q² S`, the second `q`-derivative of `S`, Lemma 6.5 (c). -/
noncomputable def Sqq (x w δ q ζ : ℝ) : ℝ := deriv (deriv (fun q' => Sloc x w δ q' ζ)) q

/-- **The region `N`** of Lemma 6.5, p.16 (PDF p.19): `x ∈ [0, 1]`, `0 ≤ w ≤ 1/16`,
`0 ≤ q ≤ 1/128`, `|δ - 1| ≤ 1/16`, `|ζ - 1| ≤ 1/16` (all boundaries included). -/
def NLoc (x w δ q ζ : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ w ∈ Set.Icc (0 : ℝ) (1 / 16) ∧ q ∈ Set.Icc (0 : ℝ) (1 / 128) ∧
    |δ - 1| ≤ 1 / 16 ∧ |ζ - 1| ≤ 1 / 16

end KMeansTaper


