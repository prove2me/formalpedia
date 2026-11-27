-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_lamEC16
-- name    : RankRobustAssort_Supplement_lamEC16
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:32:14.30345+00:00
-- url     : https://prove2.me/theorems/f3e13b09-5bb2-4174-a0a3-fd0701f46805
-- title:
--   Tuple weights (EC.16) built from an assortment $\bar S$
-- statement:
--   For the reverse revenue-ordered past assortments and an assortment $\bar S\subseteq\mathcal N_0$, the weights (EC.16) on tuples $(i_1,\dots,i_n)$ are
--
--   $$
--   \lambda_{i_1\cdots i_n}=\begin{cases}\tfrac1n, & (i_1,\dots,i_n)=(\underline i^j_1,\dots,\underline i^j_n)\text{ for some }j\in\bar S\setminus\{0,n\},\\ \tfrac1n, & (i_1,\dots,i_n)=(\bar i^j_1,\dots,\bar i^j_n)\text{ for some }j\in\mathcal N\setminus\bar S,\\ \tfrac1n, & (i_1,\dots,i_n)=(n,\dots,n),\\ 0, & \text{otherwise,}\end{cases}
--   $$
--
--   where $\mathcal N=\{1,\dots,n\}$. Lemma EC.5 shows that these weights are the unique solution of the system (EC.14) for the data (EC.15).
--
--   **Formalization Note.** The weights are defined on all tuples; the paper evaluates them on $\mathcal L$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.5, (EC.16), p.ec27

import Mathlib
import Definitions.Def_RankRobustAssort_Supplement_tupleLow
import Definitions.Def_RankRobustAssort_Supplement_tupleHigh

open Classical

namespace RankRobustAssort.Supplement

/-- The tuple weights (EC.16) built from an assortment `S̄`:

`λ_{i₁⋯i_n} = 1/n` if `(i₁,…,i_n) = (i̲ʲ₁,…,i̲ʲ_n)` for some `j ∈ S̄ \ {0,n}`,
`λ_{i₁⋯i_n} = 1/n` if `(i₁,…,i_n) = (īʲ₁,…,īʲ_n)` for some `j ∈ 𝒩 \ S̄`,
`λ_{i₁⋯i_n} = 1/n` if `(i₁,…,i_n) = (n,…,n)`,
`λ_{i₁⋯i_n} = 0` otherwise.

Sturt, arXiv:2112.05010v4, Lemma EC.5, (EC.16), p.ec27.

Formalization Note: tuples are functions `Fin n → Fin (n+1)` (see `tupleLow`, `tupleHigh`);
`𝒩 = {1,…,n}` is `j ≠ 0`; the product `n` is `Fin.last n`. The function is defined on every tuple;
the paper evaluates it on `ℒ`. -/
noncomputable def lamEC16 (n : ℕ) (Sbar : Finset (Fin (n + 1))) : (Fin n → Fin (n + 1)) → ℝ :=
  fun t =>
    if (∃ j ∈ Sbar, j ≠ 0 ∧ j ≠ Fin.last n ∧ t = tupleLow n j) ∨
        (∃ j, j ≠ 0 ∧ j ∉ Sbar ∧ t = tupleHigh n j) ∨
        t = (fun _ => Fin.last n) then
      1 / n
    else 0

end RankRobustAssort.Supplement


