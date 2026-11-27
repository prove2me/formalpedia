-- Prove2me | Definitions.Def_Chi2QEC_Supplement_rotationError
-- name    : Chi2QEC_Supplement_rotationError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:07:26.443732+00:00
-- url     : https://prove2.me/theorems/b79fd46a-9a12-5086-9f42-489887cc16ee
-- title:
--   The qudit-rotation errors on at most $t$ qudits
-- statement:
--   For $n$ qudits of dimension $q$ and $t\ge0$, the family of qudit-rotation errors on at most $t$ qudits consists of all generalized Pauli operators $W_e$ of weight $\operatorname{wt}(e)\le t$, the identity ($e=0$) included.
--
--   For $q\ge1$ the family has
--   $$
--   \sum_{j=0}^{t}\binom nj(q^2-1)^j
--   $$
--   members: $\binom nj$ choices of the $j$ affected qudits and $q^2-1$ nontrivial operators on each. This is the count in the qudit-rotation quantum Hamming bound (102). A code "corrects $t$-physical-qudit rotation errors" when it satisfies the error-correction condition (23) for this family.
--
--   **Formalization Note** The family is indexed by the subtype of exponent vectors of weight at most $t$. Its members are linearly independent. The error-correction condition (23) depends on the family only through its linear span, and nondegeneracy is the same for every linearly independent family with that span, so the choice of the Weyl basis of the weight-$\le t$ operators is no restriction.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Sec. I, p.3; Theorem 1 and its proof, p.15

import Mathlib
import Definitions.Def_Chi2QEC_Supplement_weylError
import Definitions.Def_Chi2QEC_Supplement_errorWeight

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. I, p.3 (a code that "corrects t-physical-qudit rotation errors"), and
Sec. V A, Theorem 1 and its proof, p.15: the family of all qudit-rotation errors on at most `t` of
the `n` qudits, the generalized Pauli operators `weylError n q e` of weight `≤ t`, the identity
(`e = 0`) included.

**Formalization Note.** For `q ≥ 1` the index type has `Σ_{j=0}^{t} C(n, j)(q² − 1)ʲ` elements, the
count of (102): `C(n, j)` choices of the `j` affected qudits and `q² − 1` nontrivial operators on
each. The operators are linearly independent, so the family is not a spanning set with repeats.
Condition (23) depends on the family only through its linear span, and nondegeneracy is the same for
every linearly independent family with that span (a family with repeats is never nondegenerate on a
nonzero code), so this choice of operator basis of the weight-`≤ t` operators is no restriction. -/
noncomputable def rotationError (n q t : ℕ) :
    {e : Fin n → Fin q × Fin q // errorWeight e ≤ t} → Matrix (QuditIdx n q) (QuditIdx n q) ℂ :=
  fun e => weylError n q e.1

end Chi2QEC.Supplement


