-- Prove2me | Definitions.Def_KallMayerSLP_ICC_Supplement_setA
-- name    : KallMayerSLP_ICC_Supplement_setA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:39:52.436288+00:00
-- url     : https://prove2.me/theorems/00648b75-f405-49b5-9fe7-312584b02a64
-- title:
--   Feasible set $\mathcal A(\alpha)=\{x\mid\mathbb P(T(\xi)x\le h(\xi))\ge\alpha\}$
-- statement:
--   For $x\in\mathbb R^n$ let $\zeta(x)=\sum_{i=1}^n\zeta^{(i)}x_i-\zeta^{(n+1)}=T(\xi)x-h(\xi)\in\mathbb R^s$, as in (2.67). For a probability level $\alpha\in\mathbb R$ the feasible set of the joint probability constraint is
--   $$
--   \mathcal A(\alpha)=\{x\in\mathbb R^n\mid \mathbb P(\zeta(x)\le 0)\ge\alpha\}=\{x\in\mathbb R^n\mid \mathbb P(T(\xi)x\le h(\xi))\ge\alpha\},
--   $$
--   where $\zeta(x)\le0$ is required in all $s$ components simultaneously.
--
--   This is the set whose convexity Prékopa's theorem establishes for jointly normal data.
--
--   **Formalization Note** $\zeta(x)$ is the published `KallMayerSLP.ICC.zetaVec`. The probability is taken under the law $P$ of $\xi$ and returned as a real number (`P.real`). No range is imposed on $\alpha$; for $\alpha>1$ the set is empty.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.6, (2.67) p.137 (PDF 147) and p.139 (PDF 149)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_zetaVec

open Matrix MeasureTheory

namespace KallMayerSLP.ICC.Supplement

/-- **The feasible set `𝒜(α) = {x | ℙ(ζ(x) ≤ 0) ≥ α}` of a joint probability constraint.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.6, p.139 (PDF 149), with
`ζ(x) = Σ_{i=1}^n ζ^(i) x_i − ζ^(n+1) = T(ξ)x − h(ξ)` of (2.67), p.137 (PDF 147). The inequality
`ζ(x) ≤ 0` is componentwise and joint in all `s` rows: `𝒜(α) = {x | ℙ(T(ξ)x ≤ h(ξ)) ≥ α}`.

**Formalization Note.** `ζ(x)` is the published `KallMayerSLP.ICC.zetaVec T h x ξ`. `P` is the
law of `ξ` on `Ξ`, and the probability is `P.real` (the measure as a real number), the book's `ℙ`
for a probability measure. `α` is any real number. -/
def setA {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) {s n : ℕ}
    (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ) (α : ℝ) : Set (Fin n → ℝ) :=
  {x | α ≤ P.real {ξ | KallMayerSLP.ICC.zetaVec T h x ξ ≤ 0}}

end KallMayerSLP.ICC.Supplement


