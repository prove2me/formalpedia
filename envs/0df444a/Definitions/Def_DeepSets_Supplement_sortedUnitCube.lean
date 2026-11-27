-- Prove2me | Definitions.Def_DeepSets_Supplement_sortedUnitCube
-- name    : DeepSets_Supplement_sortedUnitCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:25:15.971778+00:00
-- url     : https://prove2.me/theorems/292ea530-af12-4622-b568-e4f1f3f89295
-- title:
--   §A.2: the sorted domain $\mathcal X=\{x\in[0,1]^M:x_1\le\cdots\le x_M\}$
-- statement:
--   Fix a set size $M\ge 0$. The **sorted domain** of §A.2 of Deep Sets is the set of the tuples of $M$ numbers of $[0,1]$ listed in nondecreasing order:
--   $$
--   \mathcal X=\{(x_1,\dots,x_M)\in[0,1]^M : x_1\le x_2\le\cdots\le x_M\}.
--   $$
--   Repeated entries are allowed. Every point of the cube $[0,1]^M$ is a permutation of exactly one point of $\mathcal X$, so a permutation-invariant function on the cube is determined by its values on $\mathcal X$. Lemmas 4 and 6 are stated on this domain.
--
--   **Formalization Note** A tuple is $x:\mathrm{Fin}\,M\to\mathbb R$ and the inequalities are `Monotone x`. For $M=0$ the set is the single empty tuple.
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.2, p.12 (PDF p.12), "we often define the domain to be the set 𝒳 = …"; also Lemma 4, p.12, and Lemma 6, p.13

import Mathlib

namespace DeepSets.Supplement

/-- **The sorted domain `𝒳`** (Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola,
*Deep Sets*, arXiv:1703.06114v3, §A.2, p.12; also Lemma 4, p.12 and Lemma 6, p.13):
`𝒳 = {(x₁, …, x_M) ∈ [0,1]^M : x₁ ≤ x₂ ≤ ⋯ ≤ x_M}`, for the fixed set size `M`.

**Formalization Note** A tuple is `x : Fin M → ℝ`, and the weak inequalities are `Monotone x`, so
repeated entries are allowed. For `M = 0` the set is the single empty tuple. -/
def sortedUnitCube (M : ℕ) : Set (Fin M → ℝ) :=
  {x | (∀ m, x m ∈ Set.Icc (0 : ℝ) 1) ∧ Monotone x}

end DeepSets.Supplement


