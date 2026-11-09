-- Prove2me | Definitions.Def_RSSubspaceDesign_decK
-- name    : RSSubspaceDesign_decK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:15.918697+00:00
-- url     : https://prove2.me/theorems/ab52fbbd-f8fa-4597-8bd5-a7860deb9747
-- title:
--   An element of the input field $K=\mathbb F_p[Y]/(f)$ from its coordinates
-- statement:
--   A finite field is given to an algorithm as a prime $p$ and a monic irreducible $f\in\mathbb F_p[Y]$ of degree $m$, so $K=\mathbb F_p[Y]/(f)$ and $|K|=p^m$. A list $[c_0,\dots,c_{m-1}]$ of residues modulo $p$ names the element
--   $$\sum_{i}c_iY^i \bmod f\in K,$$
--   its coordinates in the power basis $1,Y,\dots,Y^{m-1}$.
--
--   This is how the constructions of Theorem 1.1, Theorem 7.2 and Lemma 7.3 read and write elements of $K$.
--
--   **Formalization Note** Decoding is the quotient map $\mathbb F_p[Y]\to K$; a well-formed list (length $m$, entries $<p$) names exactly one element and every element has such a list.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 1.1, p.4 (PDF p.6); Theorem 7.2, p.40 (PDF p.42); Lemma 7.3, p.41 (PDF p.43)

import Mathlib

open Polynomial

namespace RSSubspaceDesign

/-- **An element of the input field `K = 𝔽_p[Y]/(f)` from its coordinates.** Alrabiah–Goyal–
Guruswami, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.1, p.4 ("every
finite field `K`"), Theorem 7.2, p.40 and Lemma 7.3, p.41 (algorithms that take `K` as input).

The list `c = [c₀, …, c_{m−1}]` of natural numbers stands for `∑ᵢ cᵢ Yⁱ mod f`, each `cᵢ` read as a
residue mod `p`.

**Formalization Note.** A finite field is input as a prime `p` and a monic irreducible
`f ∈ 𝔽_p[Y]`, i.e. `K = AdjoinRoot f`; its elements are written in the power basis `1, Y, …,
Y^{m−1}`, `m = deg f`, with residues `< p` (see `IsCoeffList`). Decoding is structural
(`AdjoinRoot.mk`), so every well-formed list names exactly one element. -/
noncomputable def decK (p : ℕ) (f : (ZMod p)[X]) (c : List ℕ) : AdjoinRoot f :=
  AdjoinRoot.mk f (∑ i : Fin c.length, C ((c.get i : ℕ) : ZMod p) * X ^ (i : ℕ))

end RSSubspaceDesign


