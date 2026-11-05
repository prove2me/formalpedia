-- Prove2me | Definitions.Def_FractionalSpectralGP_QsigmaExt
-- name    : FractionalSpectralGP_QsigmaExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:34.136692+00:00
-- url     : https://prove2.me/theorems/e3067d92-5fdb-4664-acf8-3c86f4ac25a3
-- title:
--   Extension of $Q_\sigma$ by uniform approximation (Proposition 5.4)
-- statement:
--   For $f:\mathbb R\to\mathbb C$, if there is a sequence $(s_n)$ of Schwartz functions with $|f-\widehat{s_n}|_\infty\to0$, then
--
--   $$
--   Q_\sigma f=\lim_{n\to\infty}Q_\sigma s_n .
--   $$
--
--   Proposition 5.4 shows that the limit exists in $L^2(\mathbb R,dx)$ and does not depend on the sequence. This extension is what gives meaning to $Q_\sigma1_{[0,t]}$ and hence to $X_\sigma(t)$.
--
--   **Formalization Note** $|\cdot|_\infty$ is the $\sigma$-essential supremum. The definition picks one approximating sequence when one exists and returns $0$ otherwise; the theorem `proposition_5_4` states that every approximating sequence gives this same limit.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Proposition 5.4, p.15

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_paperFourier
import Definitions.Def_FractionalSpectralGP_Qsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The extension of `Q_σ` of Proposition 5.4 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.15):
`Q_σ f = lim_{n→∞} Q_σ s_n` for any sequence of Schwartz functions with `|f − ŝ_n|_∞ → 0`.

**Formalization Note.** The supremum norm is the essential supremum with respect to `σ`
(`eLpNorm · ⊤ σ`). The definition picks one approximating sequence when one exists and is `0`
otherwise; Proposition 5.4 (`proposition_5_4`) states that the limit exists and does not depend on
the sequence, which is what pins this definition down. -/
noncomputable def QsigmaExt (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (f : ℝ → ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  exact if hs : ∃ s : ℕ → 𝓢(ℝ, ℂ),
      Tendsto (fun n => eLpNorm (f - paperFourier (s n)) ⊤ S.σ) atTop (𝓝 0) then
    limUnder atTop (fun n => Qsigma S h (hs.choose n)) else 0

end FractionalSpectralGP


