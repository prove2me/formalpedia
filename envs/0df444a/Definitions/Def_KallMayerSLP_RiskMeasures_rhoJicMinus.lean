-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoJicMinus
-- name    : KallMayerSLP_RiskMeasures_rhoJicMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:44.291981+00:00
-- url     : https://prove2.me/theorems/d0143b2a-1ec3-46c7-85c6-67b9fb98bad1
-- title:
--   $\rho^-_{\mathrm{jic}}$: expected maximal negative part
-- statement:
--   For an $s$-dimensional random vector $\vartheta=(\vartheta_1,\dots,\vartheta_s)\in\mathcal L^1_s$,
--   $$
--   \rho^-_{\mathrm{jic}}(\vartheta):=\mathbb E\Big[\max_{1\le i\le s}\vartheta_i^-\Big],\qquad t^-=\max\{0,-t\}.
--   $$
--
--   **Formalization Note** $\vartheta$ is an $s$-dimensional random vector with components indexed $0,\dots,s-1$. The maximum over the components is the real supremum over the finite index set; for $s=0$ it is $0$ (the book has $s\ge1$).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, (P), p.188 (PDF 198), and p.189 (PDF 199)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **`ρ⁻_jic`, expected maximal negative part.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, (P), p.188 (PDF 198), and p.189 (PDF 199): `ρ⁻_jic(ϑ) := 𝔼[max_{1≤i≤s} ϑ_i⁻]`, `ϑ ∈ 𝓛¹_s`, with `z⁻ = max{0, −z}`.

**Formalization Note.** `ϑ = (ϑ_1, …, ϑ_s)` is an `s`-dimensional random vector, `ϑ ω : Fin s → ℝ` (index base 0: the book's `ϑ_i`, `1 ≤ i ≤ s`, is `ϑ ω (i − 1)`). The maximum over the finitely many components is the real `⨆ i`; for `s = 0` it is `0` (the book has `s ≥ 1`). -/
noncomputable def rhoJicMinus {Ω : Type*} [MeasurableSpace Ω] {s : ℕ} (P : Measure Ω) (ϑ : Ω → Fin s → ℝ) : ℝ :=
  ∫ ω, (⨆ i : Fin s, max (-ϑ ω i) 0) ∂P

end KallMayerSLP.RiskMeasures


