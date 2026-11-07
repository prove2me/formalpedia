-- Prove2me | Definitions.Def_KMeansTaper_CertC
-- name    : KMeansTaper_CertC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:06.682169+00:00
-- url     : https://prove2.me/theorems/0869a6bf-e2f8-47db-afe2-30a5d067d3fd
-- title:
--   The per-column excess $e_{D,s}(q,Z)$, the transfer $\Gamma(D;Z)$ and the certificate statement $[\mathrm C]$
-- statement:
--   Fix $\kappa, c, \alpha_z, \gamma_z$, put $\eta=\kappa-8$, and for $x$, $w$ put $z=P(x)w^2$ and $\nu_s(q)=(1-\lambda)^s/(1-\lambda q)$ with $\lambda=cP(x)$. For a **row** $(D,s)$ with $\delta=\sqrt D$ and a **column** $(q,Z)$ with $\zeta=\sqrt Z$, let $b_s=\frac{\kappa}{2}(2-s)P(x)(x+w)$, $U_s=(1+m)D+b_s(1+D)$, $a=1+m+\kappa P(x)(x+w)$, and
--
--   $$e_{D,s}(q,Z)=(1-q)\bigl((1+\nu_s(q))\delta+\nu_s(q)\zeta\bigr)^2+qU_s+\tfrac{\kappa}{2}Ps(1+D)-(1-q)(Z-aD)_+-6D-3Z-\eta-(\alpha_zD+\gamma_z)z .$$
--
--   For thresholds $\delta_H<\delta_{lo}<\delta_{hi}$ the **transfer** is $\Gamma(D;Z)=\mathbf 1\{\sqrt D\in[\delta_{lo},\delta_{hi}]\}(\delta_H^2-Z)_+$. The statement **$[\mathrm C]$** is: for every $x\in[0,1]$ and $w\in[0,1-x]$ there is $\alpha\in\mathbb R$ such that for every $D\ge0$ and $s\in\{0,1\}$ there is $\beta\in\mathbb R$ such that for all $q\in[0,1]$ and $Z\ge0$
--
--   $$e_{D,s}(q,Z)-\Gamma(D;Z)+\Gamma(Z;D)\le\alpha(D-1)+\beta(Z-1).\quad(13)$$
--
--   $[\mathrm C]$ is the pointwise statement certified by computer; Theorem C.2 derives SFI from it.
--
--   **Formalization Note** The multipliers are chosen in the paper's order: $\alpha$ depends on $(x,w)$ only and $\beta$ on $(x,w,D,s)$ only. $P$ and $m=m(\kappa,\cdot)$ are evaluated at $x$; $s$ is a natural number.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Appendix C, p.31 (PDF p.34) and Definition C.1, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_KMeansTaper_coefP

namespace KMeansTaper

/-- **The factor `ν_s(q) = (1 - λ)^s / (1 - λ q)`**, (R3), Appendix C, p.31 (PDF p.34), with
`λ = c P(x)`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** The type `s` is a natural number (the paper uses `s ∈ {0, 1}`). -/
noncomputable def nu (c x : ℝ) (s : ℕ) (q : ℝ) : ℝ :=
  (1 - c * coefP x) ^ s / (1 - c * coefP x * q)

/-- **The per-column excess `e_{D,s}(q, Z)`**, Appendix C, p.31 (PDF p.34). With `δ = √D`,
`ζ = √Z`, `η = κ - 8`, `z = P(x) w²`, `b_s = (κ/2)(2 - s) P(x)(x + w)`,
`U_s = (1 + m) D + b_s (1 + D)` and `a = 1 + m + κ P(x)(x + w)`:
`e = (1 - q)((1 + ν_s(q)) δ + ν_s(q) ζ)² + q U_s + (κ/2) P s (1 + D) - (1 - q)(Z - a D)_+
  - 6D - 3Z - η - (α_z D + γ_z) z`.

**Formalization Note.** `P` and `m = m(κ, ·)` are evaluated at `x`. -/
noncomputable def excess (κ c αz γz x w D : ℝ) (s : ℕ) (q Z : ℝ) : ℝ :=
  let Px := coefP x
  let mx := coefM κ x
  let ν := nu c x s q
  let bs := κ / 2 * ((2 : ℝ) - (s : ℝ)) * Px * (x + w)
  let U := (1 + mx) * D + bs * (1 + D)
  let a := 1 + mx + κ * Px * (x + w)
  (1 - q) * ((1 + ν) * Real.sqrt D + ν * Real.sqrt Z) ^ 2 + q * U
    + κ / 2 * Px * (s : ℝ) * (1 + D) - (1 - q) * max (Z - a * D) 0
    - 6 * D - 3 * Z - (κ - 8) - (αz * D + γz) * (Px * w ^ 2)

/-- **The transfer `Γ(D; Z) = 1{√D ∈ [δ_lo, δ_hi]} (δ_H² - Z)_+`**, Definition C.1, p.32
(PDF p.35). -/
noncomputable def transfer (δH δlo δhi D Z : ℝ) : ℝ :=
  if δlo ≤ Real.sqrt D ∧ Real.sqrt D ≤ δhi then max (δH ^ 2 - Z) 0 else 0

/-- **The certificate statement `[C]`**, Definition C.1, p.32 (PDF p.35): for every
`x ∈ [0, 1]` and `w ∈ [0, 1 - x]` there is `α ∈ ℝ` such that for every `D ≥ 0` and `s ∈ {0, 1}`
there is `β ∈ ℝ` such that for all `q ∈ [0, 1]` and `Z ≥ 0`
`e_{D,s}(q, Z) - Γ(D; Z) + Γ(Z; D) ≤ α (D - 1) + β (Z - 1)` (13).

**Formalization Note.** The quantifier order `∀ x, w ∃ α ∀ D, s ∃ β ∀ q, Z` is the paper's. -/
def CertC (κ c αz γz δH δlo δhi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) (1 - x), ∃ α : ℝ,
    ∀ D : ℝ, 0 ≤ D → ∀ s ∈ ({0, 1} : Finset ℕ), ∃ β : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ Z : ℝ, 0 ≤ Z →
        excess κ c αz γz x w D s q Z - transfer δH δlo δhi D Z + transfer δH δlo δhi Z D
          ≤ α * (D - 1) + β * (Z - 1)

end KMeansTaper


