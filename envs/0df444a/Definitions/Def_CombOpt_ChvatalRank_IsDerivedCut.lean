-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsDerivedCut
-- name    : CombOpt_ChvatalRank_IsDerivedCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:27.854968+00:00
-- url     : https://prove2.me/theorems/26255f7a-bc21-427b-bc0b-f4505377257c
-- title:
--   A cut derived from a system with multipliers $y$, (6.20)–(6.21)
-- statement:
--   Let $a_i^Tx\le b_i$ $(i\in I)$ be a finite system (6.20) and let $y_i\ge0$ be real numbers. Put
--   $$
--   c=\sum_i y_ia_i,\qquad d=\sum_i y_ib_i.
--   $$
--   If $c$ is integral, then $c^Tx\le\lfloor d\rfloor$ (6.21) is the Gomory–Chvátal cut **derived** from the system using the numbers $y_i$.
--
--   **Formalization Note** The index set is an arbitrary finite type, so that both the $m$ rows of a matrix and the $m+k$ rows of a growing cutting-plane proof instantiate it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, pp. 229–230 (PDF 237–238), (6.20), (6.21)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsIntegralVector

open Matrix

namespace CombOpt.ChvatalRank

/-- **A cut derived from a system with given multipliers, (6.20)–(6.21).** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, pp. 229–230
(PDF 237–238): for the system `a_iᵀx ≤ b_i` `(6.20)` and nonnegative reals `y_i`, set
`c = Σ y_i a_i`, `d = Σ y_i b_i`; if `c` is integral, `cᵀx ≤ ⌊d⌋` `(6.21)` is a Gomory–Chvátal
cutting plane, and it is derived from the system "using the numbers" `y_i`.
`IsDerivedCut a β y c t` says that `cᵀx ≤ t` is derived from `a_iᵀx ≤ β_i` using `y`.

**Formalization Note.** The system is indexed by any finite type, so that §6.7's growing system
(`Fin (m + k)` rows at step `k`) and a matrix system both instantiate it. -/
def IsDerivedCut {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ) (β : ι → ℝ) (y : ι → ℝ)
    (c : Fin n → ℝ) (t : ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ c = ∑ i, y i • a i ∧ IsIntegralVector c ∧ t = (⌊∑ i, y i * β i⌋ : ℤ)

end CombOpt.ChvatalRank


