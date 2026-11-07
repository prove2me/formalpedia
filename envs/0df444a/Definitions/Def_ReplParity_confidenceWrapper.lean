-- Prove2me | Definitions.Def_ReplParity_confidenceWrapper
-- name    : ReplParity_confidenceWrapper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:43:42.321517+00:00
-- url     : https://prove2.me/theorems/f9910eb1-28df-417e-b908-386b0ad9049c
-- title:
--   The confidence wrapper (proof of Proposition 3.5)
-- statement:
--   Compute $U$ by the multistage cover, let $\tau=\min\{\delta/2,\rho/16\}$, and draw a validation block of $N_{\mathrm{val}}=\lceil32\log(1/\tau)/\varepsilon\rceil$ samples. If at most an $\varepsilon/2$ fraction of the validation block lies outside $U$, accept and output $Z=U$. Otherwise output the span $Z$ of a fallback block of $N_{\mathrm{fb}}=\lceil(n^2\log2+\log(2/\delta))/\varepsilon\rceil$ samples. Both blocks are reserved in advance; logarithms are natural.
--
--   The sample is the multistage cover's blocks followed by the validation and fallback blocks, and the seed is that of the multistage cover.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Proposition 3.5, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ReplParity_multistageCover

namespace ReplParity

/-- `τ = min{δ/2, ρ/16}` (proof of Proposition 3.5, p.18). -/
noncomputable def wrapTau (δ ρ : ℝ) : ℝ := min (δ / 2) (ρ / 16)

/-- `N_val = ⌈32 log(1/τ)/ε⌉` (natural logarithm). -/
noncomputable def wrapNval (ε δ ρ : ℝ) : ℕ := ⌈32 * Real.log (1 / wrapTau δ ρ) / ε⌉₊

/-- `N_fb = ⌈(n² log 2 + log(2/δ))/ε⌉` (natural logarithm). -/
noncomputable def wrapNfb (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈((n : ℝ) ^ 2 * Real.log 2 + Real.log (2 / δ)) / ε⌉₊

/-- The total sample size of the confidence wrapper: the multistage cover's blocks, then the
validation block, then the fallback block. -/
noncomputable def wrapM (n : ℕ) (ε δ ρ : ℝ) : ℕ :=
  coverM n ε ρ + wrapNval ε δ ρ + wrapNfb n ε δ

open Classical in
/-- **The confidence wrapper (proof of Proposition 3.5).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), proof of Proposition 3.5, p.18 (PDF p.20): "We compute U by Proposition 3.4, let
τ = min{δ/2, ρ/16}, and draw a validation block of N_val = ⌈32 log(1/τ)/ε⌉ fresh samples. If at
most an ε/2 fraction of the validation block lies outside U, we accept and output Z = U. Otherwise
we output the span Z = F of a fresh fallback block of N_fb = ⌈(n² log 2 + log(2/δ))/ε⌉ samples.
Both blocks are reserved in advance."

The sample is the multistage cover's sample, then the validation block, then the fallback block;
the seed is the multistage cover's seed (the validation and fallback steps use none). -/
noncomputable def confidenceWrapper {n : ℕ} {ε δ ρ : ℝ}
    (impl : (j : ℕ) → TokenHashImpl n (stageK n ε ρ j) (stageEta ε ρ j))
    (S : Fin (wrapM n ε δ ρ) → Vec n) (seed : CoverSeed n ε ρ impl) : Subsp n :=
  let M := coverM n ε ρ
  let U := multistageCover impl (fun i => sampleAt S i) seed
  let Nval := wrapNval ε δ ρ
  let outCount := (Finset.univ.filter (fun i : Fin Nval => sampleAt S (M + i) ∉ U)).card
  if (outCount : ℝ) ≤ ε / 2 * Nval then U
  else Submodule.span (ZMod 2)
    (Set.range (fun i : Fin (wrapNfb n ε δ) => sampleAt S (M + Nval + i)))

end ReplParity


