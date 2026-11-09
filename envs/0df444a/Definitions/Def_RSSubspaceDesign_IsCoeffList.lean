-- Prove2me | Definitions.Def_RSSubspaceDesign_IsCoeffList
-- name    : RSSubspaceDesign_IsCoeffList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:37.710717+00:00
-- url     : https://prove2.me/theorems/ea85f1dd-81d2-4938-9d0b-bdd7b1405f32
-- title:
--   Well-formed coordinate lists over $K=\mathbb F_p[Y]/(f)$
-- statement:
--   A list of lists is **well formed of length $\ell$** for $K=\mathbb F_p[Y]/(f)$ if it has exactly $\ell$ entries, each a list of exactly $\deg f$ residues in $\{0,\dots,p-1\}$, i.e. $\ell$ elements of $K$ written in its power basis.
--
--   Fixed lengths make the written form of an element, of a polynomial (with nonzero leading coefficient) and of a point of $F=K[X]/(h)$ unique, so a construction's output determines the field and the points.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 1.1, p.4 (PDF p.6); Theorem 7.2, p.40 (PDF p.42); Lemma 7.3, p.41 (PDF p.43)

import Mathlib

open Polynomial

namespace RSSubspaceDesign

/-- **Well-formed coordinate lists over the input field.** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.1, p.4, Theorem 7.2, p.40 and
Lemma 7.3, p.41 (outputs of the constructions).

`IsCoeffList p f len hc` says that `hc` has exactly `len` entries, each a list of exactly
`deg f` residues `< p`, i.e. `len` elements of `K = 𝔽_p[Y]/(f)` written in its power basis.

**Formalization Note.** Fixed lengths and residues `< p` make the written form of an element (and
of a polynomial or a point built from such lists) unique. -/
def IsCoeffList (p : ℕ) (f : (ZMod p)[X]) (len : ℕ) (hc : List (List ℕ)) : Prop :=
  hc.length = len ∧ ∀ c ∈ hc, c.length = f.natDegree ∧ ∀ a ∈ c, a < p

end RSSubspaceDesign


