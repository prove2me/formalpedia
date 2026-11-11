-- Prove2me | Definitions.Def_MemoSDPI_Main_ShannonEntropy
-- name    : MemoSDPI_Main_ShannonEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:07.542519+00:00
-- url     : https://prove2.me/theorems/7fa9aeff-240c-4bee-866a-6ac62965236c
-- title:
--   Shannon entropy H(D) of a distribution on a countable domain
-- statement:
--   For a distribution $D$ on a countable domain $X$, the **Shannon entropy** in nats is
--   $$
--   H(D) \;=\; \sum_{x \in X} D(x) \log \frac{1}{D(x)},
--   $$
--   with the convention $0 \log(1/0) = 0$. It may be infinite. Proposition 6.1 bounds the information revealed by a differentially private algorithm in terms of $H(D)$.
--
--   **Formalization Note** A sum of the nonnegative terms $-p\log p$ (Mathlib's `Real.negMulLog`) over the points of $X$, valued in $[0,\infty]$; $H(D) < \infty$ is written `shannonEntropy D ≠ ∞`. It is meant for a probability measure on a countable type with measurable singletons.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 9, §2 Notation; p. 24, Proposition 6.1

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace MemoSDPI.Main

/-- **Shannon entropy `H(D)` of a distribution on a countable domain** (Feldman, Lyu, Talwar,
*Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing
Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 9, §2 Notation, and p. 24,
Proposition 6.1): `H(D) = ∑_x D(x) log(1/D(x))` in nats, with `0 log 0 = 0`.

**Formalization Note.** A sum of nonnegative terms `−p log p` (Mathlib's `Real.negMulLog`)
over the points of `X`, valued in `ℝ≥0∞`; it is meant for a probability measure on a countable
type with measurable singletons, and `H(D) < ∞` is written `shannonEntropy D ≠ ∞`. -/
noncomputable def shannonEntropy {X : Type} [MeasurableSpace X] (D : Measure X) : ℝ≥0∞ :=
  ∑' x : X, ENNReal.ofReal (Real.negMulLog (D.real {x}))

end MemoSDPI.Main


