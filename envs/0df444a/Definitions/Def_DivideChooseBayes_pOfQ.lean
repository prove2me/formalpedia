-- Prove2me | Definitions.Def_DivideChooseBayes_pOfQ
-- name    : DivideChooseBayes_pOfQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:19.359324+00:00
-- url     : https://prove2.me/theorems/7231106f-30c9-4b99-aa74-bdc1e89f4a7e
-- title:
--   Division in the variables $p$: $p_i = q_i/2 + 1/2$ (Eq. (2))
-- statement:
--   In divide-and-choose with $n$ divisible goods, a **division** is a vector $p=(p_1,\dots,p_n)\in[0,1]^n$: pile 1 holds the fraction $p_i$ of good $i$ and pile 2 the fraction $1-p_i$. The paper mostly works with the auxiliary variables $q_i = 2p_i-1\in[-1,1]$ (Eq. (1)), and recovers $p$ by Eq. (2):
--
--   $$p_i = \frac{q_i}{2}+\frac12 .$$
--
--   This map turns a division written in the variables $q$ into the fractions $p$ that define the two piles.
--
--   **Formalization Note** Goods are indexed by a finite type $\iota$ (the paper's $[n]$).
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, §3.1, p.6, Eq. (2)

import Mathlib

namespace DivideChooseBayes

/-- **Division in the variables `p` (Eq. (2)).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, §3.1, p.6, Eq. (2): `pᵢ = qᵢ/2 + 1/2`.

A division of the `n` goods (p.5, (ii)) is a vector `p ∈ [0,1]ⁿ`: pile 1 holds the fraction `pᵢ` of
good `i` and pile 2 the fraction `1 − pᵢ`. The paper works with the auxiliary variables
`qᵢ = 2pᵢ − 1 ∈ [−1,1]` (Eq. (1)); this map recovers `p` from `q`.

**Formalization Note.** Goods are indexed by a finite type `ι` (the paper's `[n]`). -/
noncomputable def pOfQ {ι : Type*} (q : ι → ℝ) : ι → ℝ := fun i => q i / 2 + 1 / 2

end DivideChooseBayes


