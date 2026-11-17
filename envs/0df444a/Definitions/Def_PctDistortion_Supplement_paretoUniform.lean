-- Prove2me | Definitions.Def_PctDistortion_Supplement_paretoUniform
-- name    : PctDistortion_Supplement_paretoUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:39.581481+00:00
-- url     : https://prove2.me/theorems/33789e13-07a0-477e-ae83-1a74fd21b397
-- title:
--   Pareto undominated candidates $P(\mathcal E)$ and the uniform lottery on them
-- statement:
--   In an election $\mathcal E=(V,\mathcal C,\vec\succ)$, a candidate $a$ is **Pareto undominated** if for every candidate $b\ne a$ at least one voter prefers $a$ over $b$. Write $P(\mathcal E)$ for the set of Pareto undominated candidates.
--
--   The **uniform lottery on $P(\mathcal E)$** assigns
--   $$p_c=\begin{cases}1/|P(\mathcal E)|,& c\in P(\mathcal E),\\ 0,& \text{otherwise.}\end{cases}$$
--
--   This is the rule of Theorem 9 for the max-cost objective.
--
--   **Formalization Note** $P(\mathcal E)$ is defined directly by the formula above; it is nonempty because Pareto dominance is acyclic, so the weights form a lottery.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), App. A, p.29

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

open Classical in
/-- The set `P(E)` of **Pareto undominated candidates**: the candidates `a` such that for every
candidate `b ≠ a` at least one voter prefers `a` over `b`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), App. A, p.29: "the Pareto undominated candidates, i.e., the candidates a such that for all
candidates b ≠ a, at least one voter v prefers a over b."

**Formalization Note.** Defined directly by this formula; the paper's identification with the
source nodes of `G^α_E` for `α ≥ 1 − 1/n` is a remark, not the definition. -/
noncomputable def paretoUndominated {V C : Type} [Fintype C] (E : Election V C) : Finset C :=
  Finset.univ.filter (fun a => ∀ b, b ≠ a → ∃ v, E.prefers v a b)

open Classical in
/-- The **uniform lottery on the Pareto undominated candidates**: `p_c = 1/|P(E)|` for
`c ∈ P(E)`, and `p_c = 0` otherwise.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 9, p.29: "Choosing uniformly from the Pareto undominated candidates P".

**Formalization Note.** `P(E)` is nonempty (Pareto dominance is acyclic), so this is a lottery;
the value on an empty set (all weights `0`) never occurs. -/
noncomputable def paretoUniform {V C : Type} [Fintype C] (E : Election V C) (c : C) : ℝ :=
  if c ∈ paretoUndominated E then 1 / ((paretoUndominated E).card : ℝ) else 0

end PctDistortion.Supplement


