-- Prove2me | Definitions.Def_ScalarMultiRisk_phiS
-- name    : ScalarMultiRisk_phiS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:47.871989+00:00
-- url     : https://prove2.me/theorems/e09979c6-71bc-4034-8c9c-777cc3306ce7
-- title:
--   (4.6) — the univariate risk measure $\phi^S_t$
-- statement:
--   For $Z\in L^\infty(\mathbb R)$, $\phi^S_t(Z)=\pi^S_t(Ze_1)$: the map $\pi^S_t$ restricted to positions held in cash.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (4.6), p.22

import Mathlib
import Definitions.Def_ScalarMultiRisk_piS
import Definitions.Def_QKPSDP_e1

open MeasureTheory

namespace ScalarMultiRisk

/-- **The univariate risk measure `φ^S_t`.** arXiv:1807.10694v5, (4.6), p.22:
`φ^S_t(Z) := π^S_t(Z e₁)` for `Z ∈ L∞(ℝ)`.

**Formalization Note.** `EReal`-valued, as `π^S_t` is; its values are a.s. real for
`S ∈ 𝒮_t` (Proposition 4.9). -/
noncomputable def phiS {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d] (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t : Fin (T + 1)) (Z : Ω → ℝ) : Ω → EReal :=
  piS A ρ S t fun ω => Z ω • QKPSDP.e1 d

end ScalarMultiRisk


