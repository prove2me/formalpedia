-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
-- name    : KallMayerSLP_RiskMeasures_Lspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:04.869+00:00
-- url     : https://prove2.me/theorems/ed56c97a-5804-4a41-8ffa-cd0d1fc9342f
-- title:
--   The linear spaces $\mathcal L^p_s$ of random vectors
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a measure space, $E$ a real normed space (in the book $E=\mathbb R^s$) and $p\in[1,\infty]$. The space $\mathcal L^p(E)$ is the set of measurable random variables $\vartheta:\Omega\to E$ with finite $p$-th moment,
--   $$
--   \mathcal L^p=\{\vartheta \mid \mathbb E\|\vartheta\|^p<\infty\},\qquad
--   \mathcal L^\infty=\{\vartheta\mid \exists C:\ P(\|\vartheta\|>C)=0\},
--   $$
--   viewed as a linear subspace of all functions $\Omega\to E$ under pointwise addition and scalar multiplication. With $E=\mathbb R$ this is $\mathcal L^p_1$, with $E=\mathbb R^s$ it is $\mathcal L^p_s$.
--
--   These are the spaces $\Upsilon$ of (1.6) on which the risk measures of Section 7 are defined.
--
--   **Formalization Note** Elements are functions, not almost-everywhere equivalence classes; membership is Mathlib's `MemLp f p P`, which includes almost-everywhere strong measurability. The norm on $\mathbb R^s$ (`Fin s → ℝ`) is the sup norm, which defines the same spaces as the Euclidean or $\ell_1$ norm of the book.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §1, (1.6), p.78 (PDF 88)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **The linear spaces `𝓛^p_s` of random variables.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §1, (1.6), p.78 (PDF 88), used in §7 (p.181, PDF 191): the linear space of
(`E`-valued) random variables on `(Ω, 𝓕, P)` with finite `p`-th moment; `𝓛^∞` is the space of
essentially bounded random variables.

**Formalization Note.** Random variables are functions `Ω → E` (not almost-everywhere
equivalence classes); membership is Mathlib's `MemLp f p P`, which includes
(almost-everywhere strong) measurability. `E = ℝ` gives `𝓛^p_1`, `E = Fin s → ℝ` gives
`𝓛^p_s`; `p = ⊤` gives `𝓛^∞`. The submodule structure is the pointwise one. -/
def Lspace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type*}
    [MeasurableSpace Ω] (p : ℝ≥0∞) (P : Measure Ω) : Submodule ℝ (Ω → E) where
  carrier := {f | MemLp f p P}
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := MemLp.zero
  smul_mem' := fun c _ hf => hf.const_smul c

end KallMayerSLP.RiskMeasures


