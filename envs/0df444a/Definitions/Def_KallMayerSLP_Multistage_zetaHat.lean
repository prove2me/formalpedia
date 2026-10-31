-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_zetaHat
-- name    : KallMayerSLP_Multistage_zetaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:17:41.192508+00:00
-- url     : https://prove2.me/theorems/bc9add52-2c36-4350-bba2-454793de8471
-- title:
--   Node realization $\widehat\zeta^n$ of (3.13)
-- statement:
--   For a node $n$ of stage $t$ with history $\{\ell_1,\dots,\ell_t=n\}$, the realization of the discrete process at $n$ is the vector of conditional means along the history,
--   $$
--   \widehat\zeta^n=\big(\mathbb E[\xi_2\mid\xi_2\in\Xi^2_{\ell_2}],\dots,\mathbb E[\xi_t\mid\xi_t\in\Xi^t_{\ell_t}]\big).
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.13), p.262 (PDF 271)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree_anc
import Definitions.Def_KallMayerSLP_Multistage_xiBar

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The realization `ζ̂^n = (𝔼[ξ_2 | ξ_2 ∈ Ξ^2_{ℓ_2}], …, 𝔼[ξ_{t_n} | ξ_{t_n} ∈ Ξ^{t_n}_{ℓ_{t_n}}])`
at a node `n` with history `{ℓ_1, …, ℓ_{t_n} = n}`, the first line of (3.13) (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, (3.13), p.262, PDF 271).

**Formalization Note.** The book derives this from (3.12) under stochastic independence; the
derivation is `eq_3_13`. -/
noncomputable def zetaHat {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    {t : ℕ} (n : 𝒯.Node t) : Hist D.r t :=
  fun s => xiBar 𝒯 P ξ s (𝒯.anc s.2.2 n)

end KallMayerSLP.Multistage


