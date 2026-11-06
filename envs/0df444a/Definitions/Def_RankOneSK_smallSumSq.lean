-- Prove2me | Definitions.Def_RankOneSK_smallSumSq
-- name    : RankOneSK_smallSumSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:29.473191+00:00
-- url     : https://prove2.me/theorems/e214a8fc-0bd3-4380-836f-0284721ec8ea
-- title:
--   Partial sum $\|x\|^2_{\le m}$ of the smallest squared coordinates
-- statement:
--   For $x\in\mathbb R^n$ and $m\in[0,n]$,
--   $$\|x\|^2_{\le m}=\min_{S\subseteq[n],\,|S|=\lfloor m\rfloor}\ \sum_{i\in S}x_i^2 ,$$
--   the sum of the $\lfloor m\rfloor$ smallest squared coordinates of $x$.
--
--   It measures how much mass of $x$ sits on its smallest coordinates; Lemma 2.10 uses it to express delocalization of near-top eigenvectors of a GOE matrix.
--
--   **Formalization Note** The source defines it for $m\in[0,n]$. The Lean definition uses the cardinality $\min(\lfloor m\rfloor,n)$ so that it has no junk value: for $m>n$ it is $\|x\|_2^2$, and for $m<1$ it is $0$. Every use has $m=\delta n$ with $\delta\in(0,1)$.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.1, p.10

import Mathlib

namespace RankOneSK

/-- The partial sum `∥x∥²_{⩽m} = min_{S ⊆ [n], |S| = ⌊m⌋} Σ_{i∈S} x_i²`: the sum of the `⌊m⌋`
smallest squared coordinates of `x ∈ ℝⁿ`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.1, p.10.

**Formalization Note** The source defines it for `m ∈ [0, n]`, where `⌊m⌋₊ ≤ n` and the minimum
is over a nonempty family. To have no junk value outside that range the cardinality is
`min ⌊m⌋₊ n`, so `m > n` gives `Σ_i x_i²` and `m < 1` gives `0` (the empty sum); every use in the
paper has `m = δn` with `δ ∈ (0, 1)`. -/
noncomputable def smallSumSq {n : ℕ} (x : Fin n → ℝ) (m : ℝ) : ℝ :=
  (Finset.univ.powersetCard (min ⌊m⌋₊ n)).inf'
    (Finset.powersetCard_nonempty.2 (by simp))
    (fun S => ∑ i ∈ S, x i ^ 2)

end RankOneSK


