-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_prefixChangeBound
-- name    : MonoidProdQ_Supplement_prefixChangeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:07:52.673201+00:00
-- url     : https://prove2.me/theorems/899be2dd-fec2-4855-b7c0-9d4427bb6ef7
-- title:
--   Prefix-change count $C_D$ of a promise set
-- statement:
--   For a word $x=x_1\cdots x_n$ over a monoid $M$, let $p_i(x)=x_1\cdots x_i$ be its prefix products, with $p_0=1$. For a set $D\subseteq M^n$ of words,
--
--   $$C_D=\max_{x\in D}\bigl|\{0\le i<n:\ p_i(x)\neq p_{i+1}(x)\}\bigr|$$
--
--   is the largest number of steps at which the prefix product changes along an input of $D$. Theorem 17 bounds the adversary value of the product on $D$ by $8\sqrt{nC_D}$.
--
--   **Formalization Note** Words have letters in an alphabet $G\subseteq M$ (Theorem 17 uses $G=M$). The maximum is a finite supremum, which is $0$ for an empty $D$; Theorem 17 assumes $D$ nonempty.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 17, p.32 (prefix products p.21)

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 17, p.32 (with the prefix products
of §3, p.21: "pᵢ = x₁x₂ ⋯ xᵢ for the prefix products, with p₀ = 1"): for a promise set `D` of
words of length `n`,
`C_D = max_{x ∈ D} |{0 ≤ i < n : pᵢ(x) ≠ pᵢ₊₁(x)}|`, the largest number of prefix-product
changes along an input of `D`.

**Formalization Note.** Words are `x : Fin n → G` with letters in the subtype `↥G` of an
alphabet `G ⊆ M` (Theorem 17 uses `G = M`), as in the published `MonoidProdQ.prodMap`;
`pᵢ(x)` is the product of the first `i` letters, `List.take i`, which is `1` for `i = 0`. The
index `i : Fin n` runs over `0 ≤ i < n`. The maximum over `D` is `Finset.sup`, which is `0` for
an empty `D` (Theorem 17 assumes `D` nonempty). -/
def prefixChangeBound {M : Type*} [Monoid M] [DecidableEq M] {G : Finset M} {n : ℕ}
    (D : Finset (Fin n → G)) : ℕ :=
  D.sup fun x => (Finset.univ.filter fun i : Fin n =>
    ((List.ofFn fun j => (x j : M)).take i).prod ≠
      ((List.ofFn fun j => (x j : M)).take (i + 1)).prod).card

end MonoidProdQ.Supplement


