-- Prove2me | Definitions.Def_NConjecture_Defs
-- name    : NConjecture_Defs
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T00:43:03.101073+00:00
-- url     : https://prove2.me/theorems/2b1fb365-b1cf-4e4e-ad37-9c063971bcfd
-- title:
--   Admissible tuples and the fixed-$n$ conjecture
-- statement:
--   Fix an integer $n\ge 3$. This file introduces the two predicates on which the $n$-conjecture mission rests.
--
--   An $n$-tuple of integers $a=(a_1,\dots,a_n)$, represented as a function $a:\mathrm{Fin}\,n\to\mathbb Z$, is **admissible** when it satisfies the three Browkin–Brzeziński conditions:
--   $$\sum_{i=1}^n a_i=0,\qquad \gcd(a_1,\dots,a_n)=1,\qquad \sum_{i\in I}a_i\ne 0\ \text{ for every }\varnothing\ne I\subsetneq\{1,\dots,n\}.$$
--   The gcd is taken setwise over the absolute values $|a_i|$. The subsum condition ranges over nonempty proper subsets; applied to singletons it forces $a_i\ne 0$.
--
--   For an admissible tuple put $M(a)=\max_i|a_i|$ and $m(a)=\operatorname{rad}(a_1\cdots a_n)$, where $\operatorname{rad}$ is the product of the distinct prime divisors (the published `Brocard.radical`). The predicate `conjAt n` asserts the **$n$-conjecture at $n$** in $\varepsilon$-form:
--   $$\forall\,\varepsilon>0\ \exists\,C>0\ \forall\text{ admissible }a:\quad M(a)\le C\,m(a)^{\,2n-5+\varepsilon}.$$
--   The constant $C$ may depend on $n$ and $\varepsilon$. For $n\ge 3$ this is equivalent to $\limsup L_n\le 2n-5$; together with the proved lower bound $\limsup L_n\ge 2n-5$ it yields the conjectured equality $\limsup L_n=2n-5$.
--
--   **Formalization Note.** The maximum is `Finset.sup` of the natural absolute values (cast to $\mathbb R$); the radical is applied to $\prod_i|a_i|$. Admissibility gives $m(a)\ge 2$, so all real powers are well defined. The exponent is written in real arithmetic as $2n-5+\varepsilon$ to avoid natural-number truncation.
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939, §2 p. 933, conditions (i)–(iii) and the n-conjecture. https://cr.yp.to/bib/1994/browkin.pdf

import Mathlib
import Definitions.Def_Brocard_Defs

namespace NConjecture

/-- An admissible `n`-tuple of integers for the Browkin–Brzeziński `n`-conjecture
(Browkin–Brzeziński 1994, §2, conditions (i)–(iii)): the entries sum to zero, their
greatest common divisor is `1`, and no nonempty proper subsum vanishes. -/
def admissible (n : ℕ) (a : Fin n → ℤ) : Prop :=
  (∑ i, a i = 0) ∧
  (Finset.univ.gcd (fun i => (a i).natAbs) = 1) ∧
  (∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ → ∑ i ∈ s, a i ≠ 0)

/-- The Browkin–Brzeziński `n`-conjecture for a fixed `n`, in `ε`-form: for every
`ε > 0` there is a constant `C > 0` such that every admissible `n`-tuple satisfies
`max |aᵢ| ≤ C · rad(a₁ ⋯ aₙ) ^ (2n − 5 + ε)`. For `n ≥ 3` this is equivalent to
`limsup Lₙ ≤ 2n − 5`; combined with the proved lower bound `limsup Lₙ ≥ 2n − 5`
(Browkin–Brzeziński Theorem 1) it gives the conjectured equality `limsup Lₙ = 2n − 5`. -/
def conjAt (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a : Fin n → ℤ, admissible n a →
      ((Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℝ) ≤
        C * (Brocard.radical (∏ i, (a i).natAbs) : ℝ) ^ (2 * (n : ℝ) - 5 + ε)

end NConjecture


