-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_IsWeightedCayleyComplex
-- name    : AbelianCayleyHDX_Supplement_IsWeightedCayleyComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:02:02.06246+00:00
-- url     : https://prove2.me/theorems/b93743ee-6e3b-4e4e-97d5-93a093890b6e
-- title:
--   Weighted $d$-dimensional Cayley complex over $\mathbb F_2^n$ with generators $S$
-- statement:
--   Let $d\ge 1$, $S\subseteq\mathbb F_2^n$, $X(d)$ a finite set of subsets of $\mathbb F_2^n$ and $\mu:X(d)\to\mathbb Q$. The pair $(X,\mu)$, where $X$ is the downward closure of $X(d)$, is a **weighted $d$-dimensional Cayley complex over $\mathbb F_2^n$ with generators $S$** if
--
--   1. every top face has exactly $d+1$ vertices;
--   2. $S\neq\emptyset$ and $0\notin S$;
--   3. the edges (2-element subsets of top faces) are exactly the edges $\{x,x+s\}$, $x\in\mathbb F_2^n$, $s\in S$, of the Cayley graph $\mathrm{Cay}(\mathbb F_2^n,S)$;
--   4. $\mu(\tau)>0$ for every top face and $\sum_{\tau\in X(d)}\mu(\tau)=1$ (a probability distribution with full support on $X(d)$);
--   5. the induced edge weight $\mu_1(\{x,x+s\})$ depends only on the generator $s$, not on $x$.
--
--   The Cayley degree of the complex is $|S|$. This is the class of complexes in Theorem 1.3.
--
--   **Formalization Note** The complex is simple and pure by the encoding (a `Finset` of $(d+1)$-element top faces). Weights are rational so that explicit algorithms can print them exactly. Translation invariance is a separate predicate.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8 (weighted complexes) and Section 2.3, p.9 (Cayley complexes)

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_edges
import Definitions.Def_AbelianCayleyHDX_Supplement_faceMass
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **A weighted `d`-dimensional Cayley complex over `𝔽₂ⁿ` with generators `S`**
(Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8, and Section 2.3, p.9): "a pure weighted simplicial complex [is] a
Cayley complex over `𝔽₂ⁿ` if its one-skeleton is `Cay(𝔽₂ⁿ, S)` and its induced edge weights depend
only on the generator label", with the standing assumption `∅ ≠ S ⊆ 𝔽₂ⁿ ∖ {0}` (p.9), and "a
weighted simplicial complex is a pair `(X, μ_d)`, where `μ_d` is a probability distribution with full
support on `X(d)`" (p.8).

The complex is the downward closure of its set `tops` of top faces, weighted by `μ`. The clauses:
1. every top face has `d + 1` vertices;
2. `S` is nonempty and `0 ∉ S`;
3. the edges of the complex are exactly the edges `{x, x + s}`, `x ∈ 𝔽₂ⁿ`, `s ∈ S`, of
   `Cay(𝔽₂ⁿ, S)` (so the vertex set is all of `𝔽₂ⁿ`);
4. `μ` is positive on every top face and sums to `1` over `tops` (a probability distribution with
   full support on `X(d)`);
5. the induced edge weight of `{x, x + s}` (proportional to `faceMass tops μ {x, x + s}`) depends
   only on `s`.

**Formalization Note** The faces are all subsets of members of `tops`; since all top faces have
`d + 1` elements the complex is pure and `d`-dimensional, and the `Finset` encoding makes it
simple. The weights are rational because explicitness prints them exactly. `edges` is the
base mission's (dimension-free) set of 2-subsets of top faces. Translation invariance is the
separate predicate `IsWeightedTranslationInvariant`. -/
def IsWeightedCayleyComplex {n : ℕ} (d : ℕ) (S : Finset (Vec n)) (tops : Finset (Finset (Vec n)))
    (μ : Finset (Vec n) → ℚ) : Prop :=
  (∀ τ ∈ tops, τ.card = d + 1) ∧
  S.Nonempty ∧ (0 : Vec n) ∉ S ∧
  AbelianCayleyHDX.edges tops =
    (Finset.univ ×ˢ S).image (fun p : Vec n × Vec n => ({p.1, p.1 + p.2} : Finset (Vec n))) ∧
  (∀ τ ∈ tops, 0 < μ τ) ∧ (∑ τ ∈ tops, μ τ = 1) ∧
  (∀ s ∈ S, ∀ x y : Vec n, faceMass tops μ {x, x + s} = faceMass tops μ {y, y + s})

end AbelianCayleyHDX.Supplement


