-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsGomoryChvatalCut
-- name    : CombOpt_ChvatalRank_IsGomoryChvatalCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:46.923055+00:00
-- url     : https://prove2.me/theorems/d9a0fb60-39b9-47b1-a124-5edcca93585e
-- title:
--   Gomory–Chvátal cutting plane for a set
-- statement:
--   Let $S\subseteq\mathbb R^n$. A **Gomory–Chvátal cutting plane** for $S$ is an inequality $c^Tx\le\lfloor d\rfloor$, where $c$ is integral, $d\in\mathbb R$, and $c^Tx\le d$ is valid for $S$.
--
--   Every integral vector of $S$ satisfies such a cut, because $c^Tx$ is then an integer.
--
--   **Formalization Note** The predicate takes the pair $(c,t)$ with $t=\lfloor d\rfloor$. The number $d$ is any valid right-hand side, not necessarily $\max\{c^Tx : x\in S\}$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, p. 230 (PDF 238)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsIntegralVector
import Definitions.Def_CombOpt_ChvatalRank_IsValid

open Matrix

namespace CombOpt.ChvatalRank

/-- **Gomory–Chvátal cutting plane for a set.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, p. 230 (PDF 238): "We just take a valid
inequality cᵀx ≤ d for P with c integral and round down to obtain the cutting plane cᵀx ≤ ⌊d⌋."
`IsGomoryChvatalCut S c t` says that `cᵀx ≤ t` is such a cut: `c` is integral and `t = ⌊d⌋` for a
real `d` with `cᵀx ≤ d` valid for `S`.

**Formalization Note.** `d` is real and need not be the maximum of `cᵀx`. On the empty set every
integral `c` and every integer `t` qualify, as validity is vacuous; the closure stays faithful
because it also intersects with `P`. -/
def IsGomoryChvatalCut {n : ℕ} (S : Set (Fin n → ℝ)) (c : Fin n → ℝ) (t : ℝ) : Prop :=
  IsIntegralVector c ∧ ∃ d : ℝ, IsValid S c d ∧ t = (⌊d⌋ : ℤ)

end CombOpt.ChvatalRank


