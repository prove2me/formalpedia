-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_listRel
-- name    : SelectiveDPT_Supplement_listRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:26:19.032221+00:00
-- url     : https://prove2.me/theorems/96bd14aa-3987-4a5b-b88d-ded642321ce5
-- title:
--   List-decoding direct product relation $R^{L(k,m)}$
-- statement:
--   Let $R \subseteq D \times Y$ be a relation with $Y$ finite and let $k, m \ge 0$. The **list-decoding direct product relation** $R^{L(k,m)}$ relates an $m$-copy input $x = (x_1, \dots, x_m) \in D^m$ to a list $L \subseteq Y^m$ of candidate answer vectors with
--   $$|L| \le |Y|^{m-k},$$
--   and $(x, L) \in R^{L(k,m)}$ iff some $(y_1, \dots, y_m) \in L$ satisfies $(x_i, y_i) \in R$ for every $i \in [m]$. For a function $f$, $f^{L(k,m)}$ is $R^{L(k,m)}$ for the graph of $f$: the list must contain $f^{\otimes m}(x)$.
--
--   A selective output (correct values on $k$ chosen copies) is the special case of the list of all $|Y|^{m-k}$ vectors consistent with it, so list decoding is harder to rule out than selective computation.
--
--   **Formalization Note** The size bound is written $|L|\cdot|Y|^k \le |Y|^m$, which is $|L| \le |Y|^{m-k}$ for $k \le m$. Definition 5.1 writes lists of size exactly $|Y|^{m-k}$; the bound "at most" is the one of the introduction (p.6) and of the proofs (p.46), and gives the same query complexity because an algorithm can pad its list.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definition 5.1, p.41; introduction, p.6

import Mathlib
import Definitions.Def_SelectiveDPT_copy

namespace SelectiveDPT.Supplement

/-- The list-decoding direct product relation `R^{L(k,m)}` (arXiv:2609.26678, Definition 5.1,
p.41): for a relation `R ⊆ D × Y`, an output is a list `L ⊆ Y^m` of at most `|Y|^{m−k}` answer
vectors, and `((x_1, …, x_m), L) ∈ R^{L(k,m)}` iff there exists `(y_1, …, y_m) ∈ L` with
`(x_i, y_i) ∈ R` for all `i ∈ [m]`. For a function `f`, `f^{L(k,m)}` is `R^{L(k,m)}` for the graph
of `f`.

**Formalization Note.** The size bound is written `|L| · |Y|^k ≤ |Y|^m`, which is
`|L| ≤ |Y|^{m−k}` for `k ≤ m` without natural-number subtraction (for `k > m` and `|Y| ≥ 2` only
the empty list qualifies, and it is never correct). Definition 5.1 writes lists of size exactly
`|Y|^{m−k}`; the size *at most* `|Y|^{m−k}` is the one of the introduction (p.6) and of the
proofs (p.46: "every output of `f^{L(k,m)}` is of the form `L ⊂ Y^m` with `|L| ≤ |Y|^{m−k}`").
An `m`-copy input is a function on `Fin m × ι` (copy, position), as in the base mission. -/
def listRel {ι α Y : Type*} [Fintype Y] (k m : ℕ) (R : (ι → α) → Y → Prop) :
    (Fin m × ι → α) → Finset (Fin m → Y) → Prop :=
  fun x L => L.card * Fintype.card Y ^ k ≤ Fintype.card Y ^ m ∧
    ∃ y ∈ L, ∀ i, R (copy x i) (y i)

end SelectiveDPT.Supplement


