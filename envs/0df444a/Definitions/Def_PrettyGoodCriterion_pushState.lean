-- Prove2me | Definitions.Def_PrettyGoodCriterion_pushState
-- name    : PrettyGoodCriterion_pushState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:08.587904+00:00
-- url     : https://prove2.me/theorems/96c32c06-d1ce-4b88-9222-15e87ca20b2f
-- title:
--   Pushforward ensemble $\{(\nu_y,\omega_y)\}$ of an ensemble under a classical map
-- statement:
--   Let $\mathcal E=\{(\pi_x,\sigma_x):x\in\mathcal X\}$ be a finite ensemble and $f:\mathcal X\to\mathcal Y$ a map. The **pushforward ensemble** $\mathcal F=\{(\nu_y,\omega_y):y\in\mathcal Y\}$ of $\mathcal E$ under $f$ has
--   $$\nu_y:=\Pr[f(x)=y]=\sum_{x:\,f(x)=y}\pi_x,\qquad \omega_y:=\mathbb E[\sigma_x\mid f(x)=y]=\frac{1}{\nu_y}\sum_{x:\,f(x)=y}\pi_x\sigma_x .$$
--
--   It describes what is left of the ensemble when only the coarse label $f(x)$ is to be recovered; Lemma 8 of the paper shows that the pretty good measurement commutes with this coarse-graining.
--
--   **Formalization Note** When $\nu_y=0$ the conditional expectation is undefined; Lean's $0^{-1}=0$ makes $\omega_y=0$. Such labels have weight $0$ and contribute neither to the PGM operators nor to the PGM error of $\mathcal F$.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Lemma 8, p.18 (PDF 20)

import Mathlib

namespace PrettyGoodCriterion

/-- The prior `ν_y := Pr[f(x) = y]` of the **pushforward ensemble** of `ℰ = {(π_x, σ_x)}` under a
classical map `f : 𝒳 → 𝒴`, Alrabiah–Guruswami, arXiv:2608.09347 (held version), Lemma 8, p.18
(PDF 20). -/
noncomputable def pushPrior {X Y : Type} [Fintype X] [DecidableEq Y] (p : X → ℝ) (f : X → Y)
    (y : Y) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x

/-- The state `ω_y := E[σ_x | f(x) = y]` of the pushforward ensemble
`ℱ = {(ν_y, ω_y) : y ∈ 𝒴}` of `ℰ` under `f`, arXiv:2608.09347 (held version), Lemma 8, p.18
(PDF 20): `ω_y = ν_y⁻¹ ∑_{x : f(x) = y} π_x σ_x`.

**Formalization Note.** When `ν_y = 0` the conditional expectation is undefined; Lean's
`0⁻¹ = 0` makes `ω_y = 0`. Such `y` carry weight `0` and drop out of every PGM operator and
every PGM error term. -/
noncomputable def pushState {X Y ι : Type} [Fintype X] [DecidableEq Y] (p : X → ℝ)
    (σ : X → Matrix ι ι ℂ) (f : X → Y) (y : Y) : Matrix ι ι ℂ :=
  ((pushPrior p f y : ℂ))⁻¹ • ∑ x ∈ Finset.univ.filter (fun x => f x = y), (p x : ℂ) • σ x

end PrettyGoodCriterion


