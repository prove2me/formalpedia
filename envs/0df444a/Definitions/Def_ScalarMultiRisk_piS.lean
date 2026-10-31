-- Prove2me | Definitions.Def_ScalarMultiRisk_piS
-- name    : ScalarMultiRisk_piS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:19.035978+00:00
-- url     : https://prove2.me/theorems/3cf34e39-c7de-4d3d-a8e7-52ff7face278
-- title:
--   Definition 4.2 — the frictionless risk measure $\pi^S_t$
-- statement:
--   For $S\in\mathcal S$ and $X\in L^\infty(\mathbb R^d)$,
--
--   $$\pi^S_t(X)=\operatorname*{ess\,sup}_{\mathbb Q\in\mathcal Q^e(S)}\Big(-\beta_t(\mathbb Q,S)-\mathbb E^{\mathbb Q}[S_T^{\mathsf T}X\mid\mathcal F_t]\Big),$$
--
--   with values in $L^0_t(\mathbb R)\cup\{-\infty\}$. It is the part of the dual representation of $\rho_t$ that belongs to the price process $S$: the risk measure of a frictionless market with prices $S$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 4.2, (4.4), p.18

import Mathlib
import Definitions.Def_ScalarMultiRisk_dualTerm
import Definitions.Def_ScalarMultiRisk_Qe

open MeasureTheory

namespace ScalarMultiRisk

/-- **The frictionless risk measure `π^S_t`.** arXiv:1807.10694v5, Definition 4.2, (4.4), p.18:
`π^S_t(X) := ess sup_{ℚ ∈ 𝒬^e(S)} (−β_t(ℚ,S) − 𝔼^ℚ[S_T^T X | F_t])`.

**Formalization Note.** `π^S_t(X)` takes values in `L⁰_t(ℝ) ∪ {−∞}`, encoded as an `EReal`-valued
function. If `𝒬^e(S)` is empty the essential supremum is `−∞`. -/
noncomputable def piS {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t : Fin (T + 1)) (X : Ω → Fin d → ℝ) : Ω → EReal :=
  essSupE A.P fun Q : Qe A S => dualTerm A ρ S t Q.1 (payoff (S (Fin.last T)) X)

end ScalarMultiRisk


