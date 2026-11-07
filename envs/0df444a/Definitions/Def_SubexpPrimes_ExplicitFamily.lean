-- Prove2me | Definitions.Def_SubexpPrimes_ExplicitFamily
-- name    : SubexpPrimes_ExplicitFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:30.875849+00:00
-- url     : https://prove2.me/theorems/e535704b-b345-44ee-b601-c0a35b3cebf2
-- title:
--   Explicit family of networks; linear-size explicit functional representation
-- statement:
--   A family $a\mapsto G_a$ of networks is **explicit** if one builder machine and one entry machine, with one constant $C$, serve all valid indices: the builder on the word of $a$ outputs the description of $G_a$ within $C(|a|+1)^C$ steps and cells, and the entry machine computes its entries within a polynomial of its description length.
--
--   A family of relations **has a linear-size explicit functional representation**, with size parameter $s(a)$, if an explicit family represents it functionally with at most $Ks(a)$ edges and degree at most $Ks(a)^{3/4}$, with $K$ fixed before the index.
--
--   **Formalization Note** The entry bound is in the length of the description, which loses nothing, since a builder can copy its input into the description's data field.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Definition 2.3, p.15; proof of Proposition 6.1, p.28

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_NetDesc
import Definitions.Def_SubexpPrimes_IsFunctionalRep

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT.Computation

/-- **An explicit family of networks** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), Definition 2.3, p.15 ("construct, in time
poly(n + L), … whose entries are computable in time poly(n + L)"), and p.28 ("the arithmetic parts
are explicit, and the rotation constants take time poly(p)").

One builder machine `B`, one entry machine `E` and one constant `C` serve the whole family: for
every valid index `a`, the builder on `enc a` outputs the description `G a` within `C(|enc a|+1)^C`
steps and cells, and `E` computes the entries of `G a` within a polynomial of its description
length.

**Formalization Note.** `T` assigns tables to every description, because an entry machine sees only
the description, the vertex and the local assignment. The entry bound is in `|(G a).encode|`, which
loses nothing: a builder can copy `enc a` into the field `data`. -/
def ExplicitFamily {α : Type*} (enc : α → List Bool) (valid : α → Prop) (G : α → NetDesc)
    (T : (D : NetDesc) → D.Tables ℚ) : Prop :=
  ∃ (B : PrimitiveMachine) (outB : Fin B.tapeCount) (E : PrimitiveMachine)
    (outE : Fin E.tapeCount) (C : ℕ),
    ∀ a, valid a →
      RunsWithin B outB (enc a) (G a).encode (polyBound C (enc a).length)
        (polyBound C (enc a).length) ∧
      (G a).EntryComputes E outE (T (G a)) (polyBound C (G a).encode.length)
        (polyBound C (G a).encode.length)

/-- **A linear-size explicit functional representation.** The family of relations `P a` on
`wid a`-bit words has an explicit family of functional representations with `O(size a)` edges and
degree `O((size a)^{3/4})`: the shape shared by Corollary 3.2, Lemma 3.3, Lemma 5.2 and
Definition 2.3. The constant `K` is fixed before the index. -/
def HasLinearRep {α : Type*} (enc : α → List Bool) (valid : α → Prop) (size wid : α → ℕ)
    (P : α → List Bool → Prop) : Prop :=
  ∃ (G : α → NetDesc) (T : (D : NetDesc) → D.Tables ℚ),
    ExplicitFamily enc valid G T ∧
    ∃ K : ℕ, ∀ a, valid a →
      (G a).inputs.length = wid a ∧
      (G a).m ≤ K * size a ∧
      ((G a).maxDeg : ℝ) ≤ (K : ℝ) * (size a : ℝ) ^ ((3 : ℝ) / 4) ∧
      IsFunctionalRep ((G a).net (T (G a))) (G a).inputs (P a)

end SubexpPrimes


