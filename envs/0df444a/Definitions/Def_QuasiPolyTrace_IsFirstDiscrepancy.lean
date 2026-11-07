-- Prove2me | Definitions.Def_QuasiPolyTrace_IsFirstDiscrepancy
-- name    : QuasiPolyTrace_IsFirstDiscrepancy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:14.371639+00:00
-- url     : https://prove2.me/theorems/798883b0-20b9-4efc-8bca-e1b5670d458f
-- title:
--   The point of first discrepancy $d=\min\{i:x_i\ne y_i\}$
-- statement:
--   For two binary strings $x,y\in\{0,1\}^n$, a natural number $d$ is their **point of first discrepancy** when
--
--   $$
--   x_d\ne y_d\qquad\text{and}\qquad x_i=y_i\ \text{for all } 1\le i<d,
--   $$
--
--   with positions numbered from $1$. Then $x\ne y$ and $1\le d\le n$, and $d=\min\{i:x_i\ne y_i\}$.
--
--   The paper's induction zooms out around $d$: it looks at traces of windows starting $R$ positions before $d$ for growing $R$.
--
--   **Formalization Note** Strings are `Word n = Fin n → Bool` of the reused block `OAI.TraceReconstruction`, indexed from $0$ in Lean, so the paper's $x_d$ is the Lean bit at index $d-1$. Stating the first discrepancy as a predicate avoids a junk value of $\min\emptyset$ when $x=y$.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), §2, p.6 (point of first discrepancy)

import Mathlib
import Definitions.Def_TraceReconstruction

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **The point of first discrepancy.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), §2, p.6: "For two binary strings `x ≠ y`, we will often
focus on the 'point of first discrepancy', `d := min{i : x_i ≠ y_i}`".

`IsFirstDiscrepancy x y d` holds when `d` is the smallest 1-based index at which the `n`-bit strings
`x` and `y` differ. It forces `x ≠ y` and `1 ≤ d ≤ n`.

**Formalization Note.** Strings are `Word n = Fin n → Bool` of the reused block
`OAI.TraceReconstruction`, 0-based in Lean; the bit `x_d` of the paper is `x ⟨d − 1, _⟩`. Stating "d is
the first discrepancy" as a predicate avoids a junk value of `min ∅` when `x = y`. -/
def IsFirstDiscrepancy {n : ℕ} (x y : Word n) (d : ℕ) : Prop :=
  ∃ i : Fin n, i.val + 1 = d ∧ x i ≠ y i ∧ ∀ j : Fin n, j < i → x j = y j

end QuasiPolyTrace


