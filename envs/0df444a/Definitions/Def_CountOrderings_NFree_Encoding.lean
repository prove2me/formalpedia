-- Prove2me | Definitions.Def_CountOrderings_NFree_Encoding
-- name    : CountOrderings_NFree_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:57:23.62773+00:00
-- url     : https://prove2.me/theorems/b8aea76f-c849-4da3-a9e7-512b276fe6de
-- title:
--   Binary encoding of finite posets and the counting function of Theorem 6.3
-- statement:
--   A finite poset is given to a machine as a bit string by its **order matrix**. A string $x \in \{0,1\}^*$ is a **valid poset code** if its length is a perfect square $n^2$ and the relation on $\{0, \dots, n-1\}$ defined by
--   $$i \preceq j \iff x_{i n + j} = 1 \qquad (0 \le i, j < n)$$
--   (row-major reading of an $n \times n$ 0/1 matrix) is a partial order: reflexive, antisymmetric and transitive. A valid code $x$ **decodes** to the poset $P_x = (\{0,\dots,n-1\}, \preceq)$. The code of an $n$-element poset has length $n^2$, and validity and the order can be read off in time polynomial in $n$.
--
--   The **counting function of Theorem 6.3** is the map $f : \{0,1\}^* \to \mathbb{N}$,
--   $$f(x) = \begin{cases} \#\mathrm{LE}(P_x) & \text{if } x \text{ is a valid poset code and } P_x \text{ is N-free of height exactly } 3,\\ 0 & \text{otherwise.}\end{cases}$$
--   N-freeness, height and $\#\mathrm{LE}$ are those of the definition `CountOrderings.NFree.Poset`.
--
--   **Formalization Note.** The value $0$ off the valid inputs is the usual convention that turns a promise problem into a total function on strings; every string is an input.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 19 (PDF p. 20), Theorem 6.3 and p. 6 (PDF p. 7), §1.2 (the counting problem; the input encoding is this formalization's choice)

import Mathlib
import Definitions.Def_CountOrderings_NFree_Poset

namespace CountOrderings.NFree

/-- A relation on `Fin n` is a (non-strict) **partial order**: reflexive, antisymmetric and
transitive. -/
def IsPartialOrderRel {n : ℕ} (R : Fin n → Fin n → Prop) : Prop :=
  (∀ i, R i i) ∧ (∀ i j, R i j → R j i → i = j) ∧ (∀ i j k, R i j → R j k → R i k)

/-- The finite poset with ground set `Fin n` and order `R` (a type synonym of `Fin n`). -/
def RelPoset (n : ℕ) (R : Fin n → Fin n → Prop) (_hR : IsPartialOrderRel R) : Type := Fin n

instance (n : ℕ) (R : Fin n → Fin n → Prop) (hR : IsPartialOrderRel R) :
    PartialOrder (RelPoset n R hR) where
  le := R
  le_refl := hR.1
  le_trans := hR.2.2
  le_antisymm := hR.2.1

instance (n : ℕ) (R : Fin n → Fin n → Prop) (hR : IsPartialOrderRel R) :
    Fintype (RelPoset n R hR) :=
  inferInstanceAs (Fintype (Fin n))

/-- The **adjacency-matrix code** of a relation: a bit string `x` of length `n²` is read row by
row as an `n × n` 0/1 matrix, and `i ⪯ j` holds iff the bit at position `i·n + j` is `1`. -/
def codeRel (x : List Bool) (n : ℕ) (i j : Fin n) : Prop :=
  x.getD (i.val * n + j.val) false = true

/-- `x` is a **valid code of a finite poset**: its length is a perfect square `n²` and the matrix
it encodes is a partial order on `{0, …, n-1}`. -/
def ValidPosetCode (x : List Bool) : Prop :=
  Nat.sqrt x.length * Nat.sqrt x.length = x.length ∧
    IsPartialOrderRel (codeRel x (Nat.sqrt x.length))

/-- The poset encoded by a valid code `x`. -/
abbrev decodePoset (x : List Bool) (hx : ValidPosetCode x) : Type :=
  RelPoset (Nat.sqrt x.length) (codeRel x (Nat.sqrt x.length)) hx.2

open Classical in
/-- **The counting problem of Theorem 6.3** as a function on all binary strings: a string that
encodes a finite poset `P` which is N-free and has height exactly `3` is sent to `#LE(P)`; every
other string (not a valid poset code, or a poset that is not N-free or whose height is not `3`)
is sent to `0`. -/
noncomputable def nfreeHeight3LinExtCount (x : List Bool) : ℕ :=
  if hx : ValidPosetCode x then
    if IsNFree (decodePoset x hx) ∧ height (decodePoset x hx) = 3 then
      numLinExt (decodePoset x hx)
    else 0
  else 0

end CountOrderings.NFree


