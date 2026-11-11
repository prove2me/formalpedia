-- Prove2me | Definitions.Def_DPCutRelease_Main_Adaptive
-- name    : DPCutRelease_Main_Adaptive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:11:19.996843+00:00
-- url     : https://prove2.me/theorems/3d2459f0-5626-4809-8bf6-98375d7f1cd4
-- title:
--   Adaptively chosen mechanisms as Markov kernels on transcript prefixes, and the law of their transcript (Lemmas 8, 9, 16)
-- statement:
--   A sequence $M_1,\dots,M_k$ of **adaptively chosen randomized mechanisms** with outputs in a measurable space $Y$ is described, for each input, by Markov kernels $\kappa_i$ ($i=0,1,\dots$, 0-based): $\kappa_i(y_{<i})$ is the law of the $(i+1)$-st output given the prefix $y_{<i}=(y_1,\dots,y_i)$ of earlier outputs. The **adaptive composition** releases the transcript $(y_1,\dots,y_k)$; its law is built recursively,
--   $$\mathcal L_0=\delta_{()},\qquad \mathcal L_{k+1}=\text{law of }(y_{<k},y_k)\text{ with }y_{<k}\sim\mathcal L_k,\ y_k\sim\kappa_k(y_{<k}).$$
--   For a transcript $y$ of length $k$ and a position $t<k$, $y_{<t}$ is its prefix before $t$.
--
--   Mechanisms that may fail output an element of $Y\cup\{\bot\}$, modelled as `Option Y` with `none` $=\bot$; a set $A$ of such outputs is measurable iff $\{y\in Y: y\in A\}$ is measurable, so $\{\bot\}$ is an atom.
--
--   **Formalization Note.** `transcriptLaw κ k : Measure (Fin k → Y)` uses `Measure.compProd` and appends with `Fin.snoc`; `prefixOf y t : Fin t → Y`. The instance `optionMeasurableSpace` is `MeasurableSpace.map some`.
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 11, Lemmas 8–9; p. 23, Lemma 16

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-!
# Adaptively chosen mechanisms and the law of their transcript

Eliáš et al., arXiv:2611.06670v1, p. 11 (Lemmas 8 and 9) and p. 23 (Lemma 16).

A sequence `M₁, …, M_k` of adaptively chosen randomized mechanisms with outputs in a measurable
space `Y` is given, for each input, by Markov kernels `κ i : Kernel (Fin i → Y) Y`, `i = 0, 1, …`
(0-based): the law of the `(i+1)`-st output given the transcript prefix `y<i = (y₁, …, y_i)` of
earlier outputs. The adaptive composition releases the whole transcript `(y₁, …, y_k)`;
`transcriptLaw κ k` is its law on `Fin k → Y`, built step by step: draw the prefix, then the next
output from `κ i` at that prefix, and append it (`Fin.snoc`).

`prefixOf y t` is the prefix `y<t` of a transcript `y : Fin k → Y` before position `t`.

Outputs that may be the failure symbol `⊥` live in `Option Y` (`none = ⊥`), with the σ-algebra
in which `A` is measurable iff `{y | some y ∈ A}` is measurable in `Y` (so `{⊥}` is an atom).
-/

/-- The σ-algebra on `Option Y` (`none` is the failure symbol `⊥`): `A` is measurable iff its
trace `{y | some y ∈ A}` on `Y` is measurable. -/
instance optionMeasurableSpace {Y : Type*} [MeasurableSpace Y] : MeasurableSpace (Option Y) :=
  MeasurableSpace.map some ‹MeasurableSpace Y›

/-- The law of the transcript `(y₁, …, y_k)` of the adaptive composition of the mechanisms with
conditional laws `κ i` (law of output `i` given the prefix of length `i`). -/
noncomputable def transcriptLaw {Y : Type*} [MeasurableSpace Y]
    (κ : (i : ℕ) → Kernel (Fin i → Y) Y) : (k : ℕ) → Measure (Fin k → Y)
  | 0 => Measure.dirac (fun i => i.elim0)
  | k + 1 => ((transcriptLaw κ k) ⊗ₘ (κ k)).map
      (fun q : (Fin k → Y) × Y => Fin.snoc (α := fun _ => Y) q.1 q.2)

/-- The prefix `y<t = (y₁, …, y_t)` of a transcript `y = (y₁, …, y_k)` before position `t`
(0-based: the outputs at positions `0, …, t − 1`). -/
def prefixOf {Y : Type*} {k : ℕ} (y : Fin k → Y) (t : Fin k) : Fin t.val → Y :=
  fun j => y (Fin.castLE t.isLt.le j)

end DPCutRelease.Main


