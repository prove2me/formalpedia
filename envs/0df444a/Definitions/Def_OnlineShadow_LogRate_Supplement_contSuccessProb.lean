-- Prove2me | Definitions.Def_OnlineShadow_LogRate_Supplement_contSuccessProb
-- name    : OnlineShadow_LogRate_Supplement_contSuccessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:54:51.763003+00:00
-- url     : https://prove2.me/theorems/88dfd1f2-0515-4f13-b594-cd84dbbb98c6
-- title:
--   Probability that all $m$ answers of a continuous-outcome protocol are within $\varepsilon$
-- statement:
--   Let $P$ be a continuous-outcome online protocol on $n$ copies, $\mathrm{adv}$ an adaptive adversary, $\rho$ a $d\times d$ density matrix and $\varepsilon\in\mathbb R$. For an outcome sequence $y=(y_0,\dots,y_{m-1})\in\mathbb R^m$ run the interaction: in round $t$ the adversary chooses $A_t$ from the transcript of earlier (observable, answer) pairs, the protocol applies its Kraus operator $K_t=K_{h_t,A_t}(y_t)$ and answers $\widehat\mu_t=\widehat\mu_{h_t,A_t}(y_t)$. The outcome sequence has density
--   $$p(y)=\mathrm{Tr}\big(K_y\,\rho^{\otimes n}K_y^\dagger\big),\qquad K_y=K_{m-1}\cdots K_0,$$
--   with respect to Lebesgue measure on $\mathbb R^m$. The **success probability** is
--   $$\mathrm{succ}_m(P,\rho,\mathrm{adv},\varepsilon)=\int_{\{y:\ |\widehat\mu_t-\mathrm{Tr}(A_t\rho)|\le\varepsilon\ \text{for all }t<m\}}p(y)\,\mathrm dy,$$
--   the probability that all $m$ answers are within $\varepsilon$ simultaneously, as required in Definition 1.1 and Theorem 1.3. It is the continuous analogue of the base mission's `successProb`.
--
--   **Formalization Note** The integral is the lower Lebesgue integral with values in $[0,\infty]$ over the success event, with the product Lebesgue measure on $\mathbb R^m$; the density is clamped at $0$, which changes nothing for positive semidefinite $\rho$. Traces are real parts of complex traces. At $m=0$ the value is $\mathrm{Tr}(\rho^{\otimes n})$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1 and Theorem 1.3, p. 3; integral over transcripts, p. 19

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_OnlineShadow_LogRate_Adversary
import Definitions.Def_OnlineShadow_LogRate_Supplement_ContProtocol

open scoped Matrix
open MeasureTheory

namespace OnlineShadow.LogRate.Supplement

/-- The **success probability** of a continuous-outcome online protocol `P` against the adversary `adv`
over `m` rounds, on `n` copies `ρ^{⊗n}` of the state `ρ` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1 and Theorem 1.3, p.3;
the integral over transcripts, p.19): the probability that every answer is within `ε`,
`|μ̂⁽ᵗ⁾ − Tr(A⁽ᵗ⁾ρ)| ≤ ε` for all `t < m` simultaneously.

For an outcome sequence `y ∈ ℝ^m`, round `t` runs as follows: the adversary chooses `Aₜ` from the
transcript of earlier (observable, answer) pairs, the protocol applies `Kₜ := P.kraus hₜ Aₜ (y t)` and
answers `P.answer hₜ Aₜ (y t)`, where `hₜ` is the list of earlier (observable, outcome) pairs. The outcome
sequence has density `Tr(K_y ρ^{⊗n} K_yᴴ)` with `K_y = K_{m−1} ⋯ K_0` with respect to Lebesgue measure on
`ℝ^m`, and the success probability is the integral of this density over the success event.

**Formalization Note** The continuous analogue of the published `OnlineShadow.LogRate.successProb`: the
finite sum over outcomes becomes the lower Lebesgue integral (`∫⁻`, valued in `ℝ≥0∞`) over the success
event in `ℝ^m`, with the product Lebesgue measure (`volume`). Traces are real parts of complex traces; the density is clamped
at `0` by `ENNReal.ofReal`, which changes nothing when `ρ` is positive semidefinite. At `m = 0`,
`ℝ⁰` is a point of mass `1` and the value is `Tr(ρ^{⊗n})`. -/
noncomputable def contSuccessProb {d n : ℕ} (m : ℕ) (P : ContProtocol d n)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (adv : OnlineShadow.LogRate.Adversary d) (ε : ℝ) : ENNReal :=
  let run : (Fin m → ℝ) → List (Matrix (Fin d) (Fin d) ℂ × ℝ) × List (Matrix (Fin d) (Fin d) ℂ × ℝ) ×
      Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := fun y =>
    (List.ofFn y).foldl
      (fun st yt =>
        let A := adv.obs st.2.1
        (st.1 ++ [(A, yt)], st.2.1 ++ [(A, P.answer st.1 A yt)], P.kraus st.1 A yt * st.2.2))
      ([], [], 1)
  ∫⁻ y in {y : Fin m → ℝ | ∀ p ∈ (run y).2.1, |p.2 - (p.1 * ρ).trace.re| ≤ ε},
    ENNReal.ofReal
      ((run y).2.2 * ShadowTomography.UpperBound.tensorPow ρ n * ((run y).2.2)ᴴ).trace.re

end OnlineShadow.LogRate.Supplement


