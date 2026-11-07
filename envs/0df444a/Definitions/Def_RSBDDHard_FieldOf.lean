-- Prove2me | Definitions.Def_RSBDDHard_FieldOf
-- name    : RSBDDHard_FieldOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:54.492108+00:00
-- url     : https://prove2.me/theorems/30b45dcb-f163-4913-ac14-c2ae0b3311a2
-- title:
--   Finite fields in polynomial-basis representation (field codes)
-- statement:
--   A **field code** is a pair $(p,g)$ of a natural number $p$ and a list $g=(g_0,\dots,g_e)$ of natural numbers, read as the polynomial $g(X)=\sum_i g_i X^i\in\mathbb F_p[X]$. The coded ring is $\mathbb F_p[X]/(g)$. A list $v=(v_0,\dots,v_{e-1})$ codes the element $\sum_i v_i X^i \bmod g$.
--
--   The code is **well formed** when
--
--   1. $p$ is prime;
--   2. $g$ has degree $e\ge 1$, every $g_i$ is a residue $<p$, and the leading coefficient $g_e$ equals $1$;
--   3. $g$ is irreducible over $\mathbb F_p$.
--
--   Then $\mathbb F_p[X]/(g)$ is the finite field $\mathbb F_q$ with $q=p^e$. An element code is well formed when it has exactly $e$ coordinates, each $<p$.
--
--   This is the paper's "polynomial-basis representation", in which elements "are represented by their coordinates over $\mathbb F_p$". Every finite field has such a representation, so the coding restricts no instance. All instances of RS-BDD and symmetric subset sum in this mission carry their field in this form.
--
--   **Formalization Note** The ring is `AdjoinRoot` of the coded polynomial; it is a ring for every code and a field exactly for well-formed ones.
-- source:
--   Gandikota, Grigorescu, Venkitesh, NP-Hardness of Bounded Distance Decoding for Reed-Solomon Codes and Variants, via Non-Archimedean Rings, STOC 2027 submission (sha256 0372e933…), §2, p.17

import Mathlib

set_option autoImplicit false

namespace RSBDDHard

/-- The polynomial of `(ZMod p)[X]` whose coefficient list (constant term first) is `l`: the
entry `l[i]` is the coefficient of `X^i`, read modulo `p`. Gandikota, Grigorescu, Venkitesh,
*NP-Hardness of Bounded Distance Decoding for Reed-Solomon Codes and Variants, via
Non-Archimedean Rings*, STOC 2027 submission (sha256 0372e933…), §2, p.17: "Its elements are
represented by their coordinates over Fp." -/
noncomputable def polyOf (p : ℕ) (l : List ℕ) : Polynomial (ZMod p) :=
  (l.mapIdx fun i c => Polynomial.monomial i (c : ZMod p)).sum

/-- The finite field coded by a **field code** `(p, g)`: `F_p[X]/(g)`, where `g` is the
coefficient list of the defining polynomial (STOC 2027 submission, sha256 0372e933…, §2, p.17:
"A finite field F = Fq of characteristic p is supplied by a polynomial-basis representation").

**Formalization Note.** `FieldOf p g` is a commutative ring for every code; it is a field of
size `p ^ (g.length - 1)` exactly when the code is well formed (`FieldCodeWF`). -/
abbrev FieldOf (p : ℕ) (g : List ℕ) : Type := AdjoinRoot (polyOf p g)

/-- The element of `FieldOf p g` with coordinate vector `v` in the polynomial basis
`1, X, X², …`: the class of `Σ v[i] X^i` modulo `g`. -/
noncomputable def elemOf (p : ℕ) (g : List ℕ) (v : List ℕ) : FieldOf p g :=
  AdjoinRoot.mk (polyOf p g) (polyOf p v)

/-- The extension degree `e` coded by `g`: one less than the length of its coefficient list. -/
def fieldDeg (g : List ℕ) : ℕ := g.length - 1

/-- A **well-formed field code** `(p, g)`: `p` is prime, every coefficient of `g` is a residue
`< p`, the leading coefficient of `g` is `1`, `g` has degree `e ≥ 1`, and `g` is irreducible over
`F_p`. Then `FieldOf p g` is the field `F_q` with `q = p ^ e`.

**Formalization Note.** This is the paper's polynomial-basis representation (§2, p.17); it is an
encoding, not a restriction, because every finite field has such a representation. -/
def FieldCodeWF (p : ℕ) (g : List ℕ) : Prop :=
  p.Prime ∧ 2 ≤ g.length ∧ (∀ c ∈ g, c < p) ∧ g.getLast? = some 1 ∧ Irreducible (polyOf p g)

/-- A **well-formed element code** for the field code `(p, g)`: exactly `e = fieldDeg g`
coordinates, each a residue `< p`. -/
def ElemWF (p : ℕ) (g : List ℕ) (v : List ℕ) : Prop :=
  v.length = fieldDeg g ∧ ∀ c ∈ v, c < p

end RSBDDHard


