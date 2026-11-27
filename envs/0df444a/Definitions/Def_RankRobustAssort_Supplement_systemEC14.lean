-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_systemEC14
-- name    : RankRobustAssort_Supplement_systemEC14
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:32:37.119748+00:00
-- url     : https://prove2.me/theorems/35d209f0-8880-4791-9429-9c865ae1ef2f
-- title:
--   The system (EC.14): constraints of LP (2) at $\eta=0$
-- statement:
--   Let $\mathcal L$ be the set of tuples $(i_1,\dots,i_M)\in S_1\times\cdots\times S_M$ for which some ranking makes $i_m$ the most preferred product of $S_m$ for every $m$. A vector $\lambda=(\lambda_{i_1\cdots i_M})_{(i_1,\dots,i_M)\in\mathcal L}$ **solves the system (EC.14)** if
--
--   $$
--   \sum_{(i_1,\dots,i_M)\in\mathcal L:\ i_m=i}\lambda_{i_1\cdots i_M}=v_{m,i}\ \ (m\in\mathcal M,\ i\in S_m),\qquad \sum_{(i_1,\dots,i_M)\in\mathcal L}\lambda_{i_1\cdots i_M}=1,\qquad \lambda_{i_1\cdots i_M}\ge0\ \ ((i_1,\dots,i_M)\in\mathcal L).
--   $$
--
--   These are the constraints of the linear optimization problem (2) when the radius is $\eta=0$ (the error vector $\epsilon$ must vanish).
--
--   **Formalization Note.** Defined for any instance; the paper writes it for the reverse revenue-ordered past assortments ($M=n$). The weights are a function on all tuples, of which only the entries on $\mathcal L$ are constrained.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Appendix E.1, (EC.14), p.ec27

import Mathlib
import Definitions.Def_RankRobustAssort_InL

open Classical

namespace RankRobustAssort.Supplement

/-- `λ` solves the system (EC.14), the constraints of the linear optimization problem (2) at
`η = 0`:

`∑_{(i₁,…,i_M)∈ℒ : i_m = i} λ_{i₁⋯i_M} = v_{m,i}` for all `m ∈ ℳ`, `i ∈ S_m`,
`∑_{(i₁,…,i_M)∈ℒ} λ_{i₁⋯i_M} = 1`, and `λ_{i₁⋯i_M} ≥ 0` for all `(i₁,…,i_M) ∈ ℒ`.

Sturt, arXiv:2112.05010v4, Appendix E.1, (EC.14), p.ec27 (stated there for `ℳ = S̃`, `M = n`).

Formalization Note: defined for an arbitrary problem instance `P`; the data `v` and the past
assortments are `P.v` and `P.S`, and `η` does not enter. As in the published `lpValue`, the
weights are a function `μ` on all tuples `Fin M → Fin (n+1)`, but only its entries on `ℒ`
(`InL P`) are constrained, so `μ` restricted to `ℒ` is the paper's vector `λ`. -/
def systemEC14 {n M : ℕ} (P : Problem n M) (μ : (Fin M → Fin (n + 1)) → ℝ) : Prop :=
  (∀ m, ∀ i ∈ P.S m,
      ∑ t ∈ Finset.univ.filter (fun t => InL P t ∧ t m = i), μ t = P.v m i) ∧
    ∑ t ∈ Finset.univ.filter (InL P), μ t = 1 ∧
    (∀ t, InL P t → 0 ≤ μ t)

end RankRobustAssort.Supplement


