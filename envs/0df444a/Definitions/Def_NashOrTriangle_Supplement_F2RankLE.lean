-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_F2RankLE
-- name    : NashOrTriangle_Supplement_F2RankLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:32.136116+00:00
-- url     : https://prove2.me/theorems/22c1a073-cc1e-4a59-a276-64de050b1e37
-- title:
--   $\mathbb F_2$ rank of a binary game at most $r$
-- statement:
--   A binary game $M:A\times B\to\{0,1\}$ with countable strategy sets has **$\mathbb F_2$ rank at most $r$** if for every finite set $S\subseteq A$ of rows and every finite set $T\subseteq B$ of columns, the $S\times T$ submatrix of $M$, read over the two-element field $\mathbb F_2$, has rank at most $r$:
--   $$\operatorname{rank}_{\mathbb F_2}\big(M(a,b)\big)_{a\in S,\,b\in T}\le r .$$
--   For a countable game the rank is the supremum of the ranks of its finite submatrices, so this is exactly the promise of Theorem 5.1.
--
--   **Formalization Note** The entry $1$ is read as $1\in\mathbb F_2$ and every other entry as $0$; on a binary game this is the entrywise reduction.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem 5.1, p.12 (PDF p.13); proof of Lemma 5.2, p.13 (PDF p.14)

import Mathlib

namespace NashOrTriangle.Supplement

/-- The **`𝔽₂` rank** of the binary game `M` is at most `r`: for every finite set `S` of rows and
every finite set `T` of columns, the `S × T` submatrix of `M`, read over `𝔽₂ = ZMod 2`, has rank
at most `r`. For a countable game this is "rank at most `r`" as the supremum of the ranks of its
finite submatrices.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 5.1, printed p. 12 (PDF p. 13):
"a countable binary game whose F2 rank is promised to be at most r"; proof of Lemma 5.2, printed
p. 13 (PDF p. 14): "its size is bounded by the supremum of the finite-submatrix ranks".

**Formalization Note** An entry equal to `1` is read as `1 ∈ 𝔽₂` and every other entry as `0`;
on a binary game (values `0` and `1`) this is the entrywise reduction. -/
def F2RankLE {A B : Type*} (M : A → B → ℚ) (r : ℕ) : Prop :=
  ∀ (S : Finset A) (T : Finset B),
    (Matrix.of fun (a : S) (b : T) => (if M a b = 1 then 1 else 0 : ZMod 2)).rank ≤ r

end NashOrTriangle.Supplement


