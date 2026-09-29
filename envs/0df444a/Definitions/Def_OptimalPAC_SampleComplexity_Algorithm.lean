-- Prove2me | Definitions.Def_OptimalPAC_SampleComplexity_Algorithm
-- name    : OptimalPAC_SampleComplexity_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:26:22.849981+00:00
-- url     : https://prove2.me/theorems/4d7a4f69-612a-4cf7-95c3-2cb10af66dd6
-- title:
--   The recursive subsample algorithm $\mathbb A(S;T)$ and the learner $\mathrm{Majority}(L(\mathbb A(S;T)))$
-- statement:
--   Hanneke's recursive construction of subsamples.
--
--   For finite data sets $S$ and $T$, the algorithm $\mathbb A(S;T)$ returns a finite sequence of data sets (subsamples of $S\cup T$):
--
--   0. If $|S|\le3$,
--   1. return $\{S\cup T\}$.
--   2. Otherwise let $S_0$ be the first $|S|-3\lfloor|S|/4\rfloor$ elements of $S$, $S_1$ the next $\lfloor|S|/4\rfloor$ elements, $S_2$ the next $\lfloor|S|/4\rfloor$ elements, and $S_3$ the remaining $\lfloor|S|/4\rfloor$ elements.
--   3. Return
--   $$\mathbb A(S_0;S_2\cup S_3\cup T)\cup\mathbb A(S_0;S_1\cup S_3\cup T)\cup\mathbb A(S_0;S_1\cup S_2\cup T),$$
--   where $\cup$ of sequences is concatenation.
--
--   Given a base learner $L$ (a map from data sets to classifiers), the learner of Theorem 2 is
--   $$\hat h=\mathrm{Majority}\big(L(\mathbb A(S;T))\big),$$
--   the majority vote of the classifiers $L(\hat S)$ over the subsamples $\hat S$ in $\mathbb A(S;T)$, in order; Theorem 2 uses $T=\emptyset$.
--
--   For $|S|=4^\ell$ the algorithm returns $3^\ell$ subsamples, each containing the first point of $S$. This is the object whose error the main theorem controls.
--
--   **Formalization Note** Data sets are lists and the recursion is on $|S|$; for $|S|\ge4$ one has $\lfloor|S|/4\rfloor\ge1$, so $|S_0|<|S|$. The paper runs $\mathbb A(S;T)$ only when $\mathbb C[S\cup T]\ne\emptyset$; the definition does not need that condition, and the theorems that use the algorithm assume the target is consistent with $T$.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, p. 7, §4.2, Algorithm A(S;T) and Theorem 2; p. 8 (ĥ_{m,T} = Majority(L(A(S_{1:m};T))))

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

/-!
# Hanneke (2016): the recursive subsample algorithm `𝔸(S; T)` and the learner

S. Hanneke, *The Optimal Sample Complexity of PAC Learning*, arXiv:1507.00473v4, §4.2, p. 7
(Algorithm `𝔸(S;T)`), Theorem 2 (p. 7) and p. 8 (`ĥ_{m,T} = Majority(L(𝔸(𝕊_{1:m}; T)))`).
-/

namespace OptimalPAC.SampleComplexity

/-- **Algorithm `𝔸(S; T)`** (p. 7), returning a finite sequence of data sets (subsamples of
`S ∪ T`):
0. if `|S| ≤ 3`,
1. return `{S ∪ T}`;
2. let `S₀` be the first `|S| − 3⌊|S|/4⌋` elements of `S`, `S₁` the next `⌊|S|/4⌋`, `S₂` the next
   `⌊|S|/4⌋`, and `S₃` the remaining `⌊|S|/4⌋`;
3. return `𝔸(S₀; S₂ ∪ S₃ ∪ T) ∪ 𝔸(S₀; S₁ ∪ S₃ ∪ T) ∪ 𝔸(S₀; S₁ ∪ S₂ ∪ T)`.

Sequences are lists and `∪` of sequences is concatenation (p. 2). -/
def subsamples {X : Type*} (S T : List (X × Bool)) : List (List (X × Bool)) :=
  if S.length ≤ 3 then [S ++ T]
  else
    subsamples (S.take (S.length - 3 * (S.length / 4)))
        ((S.drop (S.length - 2 * (S.length / 4))).take (S.length / 4) ++
          S.drop (S.length - S.length / 4) ++ T) ++
      subsamples (S.take (S.length - 3 * (S.length / 4)))
        ((S.drop (S.length - 3 * (S.length / 4))).take (S.length / 4) ++
          S.drop (S.length - S.length / 4) ++ T) ++
      subsamples (S.take (S.length - 3 * (S.length / 4)))
        ((S.drop (S.length - 3 * (S.length / 4))).take (S.length / 4) ++
          (S.drop (S.length - 2 * (S.length / 4))).take (S.length / 4) ++ T)
termination_by S.length
decreasing_by all_goals (simp only [List.length_take]; omega)

/-- The learner of Theorem 2 (p. 7; p. 8): `ĥ = Majority(L(𝔸(S; T)))`, the majority vote of the
classifiers that the base learner `L` returns on the subsamples `𝔸(S; T)`. Theorem 2 uses
`T = ∅`. -/
def hannekeLearner {X : Type*} (L : List (X × Bool) → X → Bool) (S T : List (X × Bool)) :
    X → Bool :=
  majority ((subsamples S T).map L)

end OptimalPAC.SampleComplexity


