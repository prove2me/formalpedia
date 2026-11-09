-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
-- name    : AbelianCayleyHDX_IsCayleyComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:52.776422+00:00
-- url     : https://prove2.me/theorems/7ab7e256-c2f1-4c64-bb6d-e6b2defa5c88
-- title:
--   Unweighted two-dimensional Cayley complex over $\mathbb F_2^n$
-- statement:
--   Let $T$ be a set of triangles in $\mathbb F_2^n$, carrying the uniform top-face distribution ("unweighted"), and let $S \subseteq \mathbb F_2^n$. The complex is a **two-dimensional Cayley complex over $\mathbb F_2^n$ with generators $S$** if:
--   1. every member of $T$ has exactly three vertices;
--   2. $S \neq \emptyset$ and $0 \notin S$ (the standing assumption of Section 2.3);
--   3. its one-skeleton is $\mathrm{Cay}(\mathbb F_2^n, S)$: the edges of the complex are exactly the pairs $\{x, x+s\}$ with $x \in \mathbb F_2^n$, $s \in S$;
--   4. it is pure: every vertex of $\mathbb F_2^n$ lies in a triangle;
--   5. its induced edge weights depend only on the generator label: the number of triangles containing $\{x, x+s\}$ depends only on $s$.
--
--   The **Cayley degree** is $|S|$. Translation invariance is a separate condition.
--
--   **Formalization Note** Simple holds by the `Finset` encoding; the uniform distribution has full support on $T$. Edges lie in triangles by construction of the edge set, so clause 4 completes purity.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8 (pure, simple, unweighted); Section 2.3, p.9 (Cayley complex, Cayley degree)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_edges
import Definitions.Def_AbelianCayleyHDX_triCount
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **An unweighted two-dimensional Cayley complex over `𝔽₂ⁿ` with generators `S`**
(Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8, and Section 2.3, p.9): "a pure weighted simplicial complex [is] a
Cayley complex over `𝔽₂ⁿ` if its one-skeleton is `Cay(𝔽₂ⁿ, S)` and its induced edge weights depend
only on the generator label", with the standing assumption `∅ ≠ S ⊆ 𝔽₂ⁿ ∖ {0}` (p.9).

The complex is the downward closure of its triangle set `T`, with the uniform top-face
distribution on `T` ("unweighted", p.8). The clauses are:
1. every top face is a triangle (has three vertices);
2. `S` is nonempty and `0 ∉ S`;
3. the edges of the complex are exactly the edges `{x, x + s}`, `x ∈ 𝔽₂ⁿ`, `s ∈ S`, of
   `Cay(𝔽₂ⁿ, S)` (so the vertex set is all of `𝔽₂ⁿ`);
4. pure: every vertex lies in a triangle (edges lie in triangles by construction);
5. the induced edge weight of `{x, x + s}`, proportional to the number of triangles containing
   it, depends only on `s`.

**Formalization Note** Simple holds by the `Finset` encoding. The uniform distribution has full
support on `T`. Translation invariance is a separate predicate (`IsTranslationInvariant`). -/
def IsCayleyComplex {n : ℕ} (S : Finset (Vec n)) (T : Finset (Finset (Vec n))) : Prop :=
  (∀ τ ∈ T, τ.card = 3) ∧
  S.Nonempty ∧ (0 : Vec n) ∉ S ∧
  edges T = (Finset.univ ×ˢ S).image (fun p : Vec n × Vec n => ({p.1, p.1 + p.2} : Finset (Vec n))) ∧
  (∀ v : Vec n, ∃ τ ∈ T, v ∈ τ) ∧
  (∀ s ∈ S, ∀ x y : Vec n, triCount T {x, x + s} = triCount T {y, y + s})

end AbelianCayleyHDX


