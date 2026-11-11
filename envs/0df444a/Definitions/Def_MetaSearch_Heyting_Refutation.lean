-- Prove2me | Definitions.Def_MetaSearch_Heyting_Refutation
-- name    : MetaSearch_Heyting_Refutation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:21:57.322975+00:00
-- url     : https://prove2.me/theorems/96506099-1785-4452-95a1-dea8387bb804
-- title:
--   Graded refutation tasks: R →_k S for reductions (Definition 3.2) and ¬_k S for algorithms (Definition 3.7)
-- statement:
--   Fix $k\in\mathbb N$ and search problems $R,S$.
--
--   **Refuting a reduction, $R\to_k S$ (Definition 3.2).** An input of the form $\langle\langle f\rangle,\langle g\rangle\rangle$, a pair of codes of machines $f$ and $g$, is well formatted; every other input accepts every output. For a well-formatted input the valid outputs are the pairs $\langle x,y\rangle$ such that
--   1. $f(x)$ does not halt within $p_k(|x|+|\langle f\rangle|)$ steps, or
--   2. $g(x,y)$, the run of $g$ on input $\langle x,y\rangle$, does not halt within $p_k(|x|+|y|+|\langle g\rangle|)$ steps, or
--   3. both halt in time, and their outputs satisfy $(f(x),y)\in S$ but $(x,g(x,y))\notin R$.
--
--   An output not of the form $\langle x,y\rangle$ is invalid for a well-formatted input. A valid output is a counterexample to the claim that $(f,g)$ is an $O(n^k)$-time reduction from $R$ to $S$.
--
--   **Refuting an algorithm, $\neg_k S$ (Definition 3.7).** If the input $z$ is not a code $\langle A\rangle$ of a machine, every output is valid. For $z=\langle A\rangle$, the output $x$ is valid iff $A(x)$ does not halt within $p_k(|x|+|\langle A\rangle|)$ steps, or it halts with an output $y$ such that $(x,y)\notin S$.
--
--   **Formalization Note.** $|\langle f\rangle|$, $|\langle g\rangle|$, $|\langle A\rangle|$ are the lengths of the code strings that appear in the input. The budget of $g$ uses $|x|+|y|$, not the length of $\langle x,y\rangle$.
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 22-23, Definition 3.2; p. 25, Definition 3.7 (informal Definitions 1.1-1.2, pp. 6-7)

import Mathlib
import Definitions.Def_MetaSearch_Heyting_SearchProblem

namespace MetaSearch.Heyting

/-! # Graded refutation tasks: `R →_k S` (Definition 3.2) and `¬_k S` (Definition 3.7) -/

/-- The input `z` is well formatted for `R →_k S`: `z = ⟨⟨f⟩, ⟨g⟩⟩` for codes `cf = ⟨f⟩`,
`cg = ⟨g⟩` of machines `f`, `g`. -/
def IsMachinePair (z : List Bool) : Prop :=
  ∃ cf cg f g, z = pair cf cg ∧ decode cf = some f ∧ decode cg = some g

/-- **Definition 3.2.** `R →_k S`. A poorly formatted input accepts every output. For
`z = ⟨⟨f⟩, ⟨g⟩⟩`, the valid outputs are the pairs `⟨x, y⟩` such that
1. `f(x)` does not halt within `p_k(|x| + |⟨f⟩|)` steps, or
2. `g(x, y)` (the machine `g` on input `⟨x, y⟩`) does not halt within
   `p_k(|x| + |y| + |⟨g⟩|)` steps, or
3. both halt in time and `(f(x), y) ∈ S` but `(x, g(x, y)) ∉ R`.
An output not of the form `⟨x, y⟩` is invalid for a well-formatted input. -/
def arrow (k : ℕ) (R S : SearchProblem) : SearchProblem :=
  {q | ∀ cf cg f g, q.1 = pair cf cg → decode cf = some f → decode cg = some g →
    ∃ x y, q.2 = pair x y ∧
      (f.evalWithin x (p k (x.length + cf.length)) = none ∨
       g.evalWithin (pair x y) (p k (x.length + y.length + cg.length)) = none ∨
       ∃ u v, f.evalWithin x (p k (x.length + cf.length)) = some u ∧
         g.evalWithin (pair x y) (p k (x.length + y.length + cg.length)) = some v ∧
         (u, y) ∈ S ∧ (x, v) ∉ R)}

/-- **Definition 3.7.** `¬_k S`. If the input `z` is not a code `⟨A⟩` of a machine, every
output is valid. For `z = ⟨A⟩`, the output `x` is valid iff `A(x)` does not halt within
`p_k(|x| + |⟨A⟩|)` steps, or it halts with an output `y` such that `(x, y) ∉ S`. -/
def neg (k : ℕ) (S : SearchProblem) : SearchProblem :=
  {q | ∀ A, decode q.1 = some A →
    (A.evalWithin q.2 (p k (q.2.length + q.1.length)) = none ∨
     ∃ y, A.evalWithin q.2 (p k (q.2.length + q.1.length)) = some y ∧ (q.2, y) ∉ S)}

end MetaSearch.Heyting


