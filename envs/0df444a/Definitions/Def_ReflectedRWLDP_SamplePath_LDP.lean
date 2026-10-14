-- Prove2me | Definitions.Def_ReflectedRWLDP_SamplePath_LDP
-- name    : ReflectedRWLDP_SamplePath_LDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:33:43.638115+00:00
-- url     : https://prove2.me/theorems/d1c609fd-56b9-4874-9dc4-fe7f9ec6b9e1
-- title:
--   Large deviation principle at speed $s_n$ and exponential equivalence for random elements of a metric space
-- statement:
--   Let $(S,D)$ be a space with a metric $D$ taking values in $[0,\infty]$, and let $Y_1,Y_2,\dots$ be random elements of $S$ defined on a probability space $(\Omega,\mathcal F,\mathbb P)$. Let $s_n>0$ be a speed and $I:S\to[0,\infty]$ a rate function.
--
--   $Y_n$ **satisfies the large deviation principle** in $(S,D)$ with speed $s_n$ and rate function $I$ if, for every open set $G$ and every closed set $F$,
--   $$-\inf_{\xi\in G}I(\xi)\le\liminf_{n\to\infty}\frac{\log\mathbb P(Y_n\in G)}{s_n},\qquad \limsup_{n\to\infty}\frac{\log\mathbb P(Y_n\in F)}{s_n}\le-\inf_{\xi\in F}I(\xi).$$
--   This is equivalent to the form (2.2) of the paper, $-\inf_{A^\circ}I\le\liminf\le\limsup\le-\inf_{\bar A}I$ for every measurable $A$.
--
--   Two sequences $Y_n$ and $Y_n'$ are **exponentially equivalent** at speed $s_n$ if, for every $\delta>0$,
--   $$\limsup_{n\to\infty}\frac{1}{s_n}\log\mathbb P\big(D(Y_n,Y_n')>\delta\big)=-\infty .$$
--
--   These are the notions of Dembo and Zeitouni used throughout the paper, where the speed is $s_n=n^\alpha$.
--
--   **Formalization Note** Open and closed sets are those of `MFGLimit.LDP.IsOpenD`/`IsClosedD` for the metric $D$. Logarithms are `ENNReal.log` with values in the extended reals ($\log 0=-\infty$), and limits inferior and superior are taken in `EReal`. The probability of a possibly non-measurable event $\{Y_n\in A\}$ is its outer measure.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 6, (2.2); p. 16, Lemma 3.8 and its proof (exponential equivalence, Dembo–Zeitouni Def. 4.2.10)

import Mathlib
import Definitions.Def_MFGLimit_LDP_LDP

namespace ReflectedRWLDP.SamplePath

open MeasureTheory Filter
open scoped ENNReal

/-!
The large deviation vocabulary used by Bazhba, Blanchet, Rhee & Zwart (arXiv:2003.14381v3, (2.2),
p. 6; Lemma 3.8, p. 16), following Dembo and Zeitouni: a large deviation principle at a general speed
`s_n` and exponential equivalence, for random elements of a space `S` carrying a metric
`D : S → S → ℝ≥0∞` (open and closed sets as in `MFGLimit.LDP.IsOpenD` / `IsClosedD`).
-/

variable {Ω S : Type*} [MeasurableSpace Ω]

/-- `s⁻¹ log q` in `EReal`, with `log 0 = −∞`. -/
noncomputable def speedLog (s : ℝ) (q : ℝ≥0∞) : EReal :=
  ((s⁻¹ : ℝ) : EReal) * ENNReal.log q

/-- `Y_n` satisfies the large deviation principle in `(S, D)` with speed `s_n` and rate function
`I : S → [0, ∞]`: for every `D`-open `G`,
`−inf_{ξ ∈ G} I(ξ) ≤ liminf_n s_n⁻¹ log P(Y_n ∈ G)`, and for every `D`-closed `F`,
`limsup_n s_n⁻¹ log P(Y_n ∈ F) ≤ −inf_{ξ ∈ F} I(ξ)`. Probabilities of events `{Y_n ∈ A}` are
evaluated with the outer measure `P`. -/
def SatisfiesLDP (P : Measure Ω) (Y : ℕ → Ω → S) (D : S → S → ℝ≥0∞) (s : ℕ → ℝ)
    (I : S → ℝ≥0∞) : Prop :=
  (∀ G : Set S, MFGLimit.LDP.IsOpenD D G →
    -(((⨅ ξ ∈ G, I ξ : ℝ≥0∞)) : EReal) ≤
      liminf (fun n => speedLog (s n) (P {ω | Y n ω ∈ G})) atTop) ∧
  (∀ F : Set S, MFGLimit.LDP.IsClosedD D F →
    limsup (fun n => speedLog (s n) (P {ω | Y n ω ∈ F})) atTop ≤
      -(((⨅ ξ ∈ F, I ξ : ℝ≥0∞)) : EReal))

/-- `Y_n` and `Y′_n` are exponentially equivalent in `(S, D)` at speed `s_n` (Dembo–Zeitouni,
Definition 4.2.10): for every `δ > 0`, `limsup_n s_n⁻¹ log P(D(Y_n, Y′_n) > δ) = −∞`. -/
def ExpEquivalent (P : Measure Ω) (Y Y' : ℕ → Ω → S) (D : S → S → ℝ≥0∞) (s : ℕ → ℝ) :
    Prop :=
  ∀ δ : ℝ, 0 < δ →
    limsup (fun n => speedLog (s n) (P {ω | ENNReal.ofReal δ < D (Y n ω) (Y' n ω)})) atTop = ⊥

end ReflectedRWLDP.SamplePath


