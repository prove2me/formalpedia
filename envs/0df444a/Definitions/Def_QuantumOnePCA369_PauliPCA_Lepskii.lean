-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_Lepskii
-- name    : QuantumOnePCA369_PauliPCA_Lepskii
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:28.219914+00:00
-- url     : https://prove2.me/theorems/1f47c61b-94d8-4462-b640-830b2f13eec8
-- title:
--   Algorithm 1: Lepskii's method with spectral clipping
-- statement:
--   Algorithm 1 of the paper as a costed program. Inputs: the dimension $d$, thresholds $\beta^2_{\min},\beta^2_{\max}$ (the paper assumes $\beta^2_{\max}\ge8\beta^2_{\min}>0$), block size $M$, confidence $\delta$, and a sequence $X_0,X_1,\dots$ of $d\times d$ Hermitian matrices; the spectral chooser computes spectral extensions and norms.
--
--   1. $I=\lceil\log_2(\beta^2_{\max}/\beta^2_{\min})\rceil$; the samples are organized in $I+1$ blocks of $M$, sample $m$ of block $i$ being $X_{iM+m}$, so exactly $(I+1)M$ samples are read.
--   2. For $i=0,\dots,I$: $\beta_i^2=2^i\beta^2_{\min}$, $\mu_i=\sqrt{M\beta_i^2/\log(4dI/\delta)}$, and
--   $$\hat X_i=\frac1M\sum_{m<M}\operatorname{clip}_{\mu_i}(X_{i,m}),\qquad \operatorname{clip}_\mu(x)=\min\{\mu,\max\{x,-\mu\}\},$$
--   applied to the spectrum (spectral extension).
--   3. $i_0$ is the least index in $\{0,\dots,I\}$ with
--   $$\|\hat X_{i_0}-\hat X_i\|_\infty\le8\sqrt{\frac{\beta_i^2\log(4dI/\delta)}{M}}\quad\text{for all }i>i_0,$$
--   and $i_0=0$ if there is none (line 8; the index $I$ always qualifies). The output is $\hat X:=\hat X_{i_0}$.
--
--   **Formalization Note** $\delta$ is an explicit input: the paper uses it on lines 5 and 7 without listing it. Logarithms are natural.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 7, Algorithm 1 (Lepskii's Method) and the definition of clip_μ

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Cost

namespace QuantumOnePCA369.PauliPCA

open MITMSynthesis

/-! Algorithm 1 (Lepskii's method), p. 7, as a costed program. -/

/-- The scalar clipping map `clip_μ(x) = min{μ, max{x, -μ}}` (p. 7). -/
noncomputable def clip (μ x : ℝ) : ℝ := min μ (max x (-μ))

/-- Line 1 of Algorithm 1: `I = ⌈log₂(β²_max / β²_min)⌉`. -/
noncomputable def lepskiiI (βmin2 βmax2 : ℝ) : ℕ := ⌈Real.logb 2 (βmax2 / βmin2)⌉₊

/-- **Algorithm 1 (Lepskii's method).** Inputs: the dimension `d`, the variance thresholds
`β²_min = βmin2`, `β²_max = βmax2`, the block size `M`, the confidence parameter `δ` (used on
lines 5 and 7), and a sequence `X 0, X 1, …` of `d × d` Hermitian samples; the eigensolver `ch`
is the spectral primitive. With `I = ⌈log₂(β²_max/β²_min)⌉`, sample `X (i·M + m)` is the `m`-th
sample of block `i` (`0 ≤ i ≤ I`, `0 ≤ m < M`), so exactly `(I+1)M` samples are read. For each `i`,
`β²_i = 2^i β²_min`, `μ_i = √(M β²_i / log(4dI/δ))` and `X̂_i = (1/M) ∑_m clip_{μ_i}(X_{i,m})`
(spectral extension). The output is `X̂_{i₀}` for the least `i₀` with
`‖X̂_{i₀} - X̂_i‖_∞ ≤ 8 √(β²_i log(4dI/δ)/M)` for all `i > i₀` (`i₀ = 0` if there is none). -/
noncomputable def lepskii (ch : SpectralChooser) (d M : ℕ) (βmin2 βmax2 δ : ℝ)
    (X : ℕ → Matrix (Fin d) (Fin d) ℂ) : Timed (Matrix (Fin d) (Fin d) ℂ) := do
  let I ← op (lepskiiI βmin2 βmax2)
  let L ← op (Real.log (4 * d * I / δ))
  let Xhat ← tab fun i : Fin (I + 1) => do
    let b ← op ((2 : ℝ) ^ (i : ℕ) * βmin2)
    let μ ← op (Real.sqrt (M * b / L))
    let Y ← tab fun m : Fin M => do
      let idx ← op ((i : ℕ) * M + (m : ℕ))
      funCalcC ch (clip μ) (X idx)
    let S ← tab fun a => tab fun b => sumC fun m : Fin M => op (Y m a b)
    smulMatC ((M : ℂ)⁻¹) S
  let ok ← tab fun i0 : Fin (I + 1) => allC fun i : Fin (I + 1) =>
    if i0 < i then do
      let D ← matSubC (Xhat i0) (Xhat i)
      let nrm ← opNormC ch D
      let t ← op (8 * Real.sqrt ((2 : ℝ) ^ (i : ℕ) * βmin2 * L / M))
      op (decide (nrm ≤ t))
    else pure true
  let i0 ← findFirstC ok
  pure (Xhat i0)

end QuantumOnePCA369.PauliPCA


