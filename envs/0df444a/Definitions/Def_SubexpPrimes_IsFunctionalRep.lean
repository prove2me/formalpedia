-- Prove2me | Definitions.Def_SubexpPrimes_IsFunctionalRep
-- name    : SubexpPrimes_IsFunctionalRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:15.723683+00:00
-- url     : https://prove2.me/theorems/4ef682f5-d342-4bb7-aa90-bc710f81fdce
-- title:
--   Functional representation of a predicate
-- statement:
--   Let $P$ be a predicate on $k$-bit strings. A network with $k$ distinct designated input edges and all entries in $\{0,1\}$ is a **functional representation** of $P$ if, for each input $a\in\{0,1\}^k$, exactly $P(a)$ assignments to the remaining edges have nonzero product: one accepting extension if $P(a)$ holds, and none otherwise.
--
--   A functional representation never inflates a count: summing over its inputs counts the inputs that satisfy $P$, each exactly once. The condition is a count, not an existence statement, and an encoding of "composite" through factorizations fails it.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Definition 2.2, p.14

import Mathlib
import Definitions.Def_SubexpPrimes_Net

set_option autoImplicit false

namespace SubexpPrimes

/-- **Functional representation** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), Definition 2.2, p.14.

`P` is a predicate on `k`-bit strings and `inputs` lists the `k` designated input edges. All
entries lie in `{0, 1}`, and for each input `a` of length `k`, exactly `P(a)` assignments to the
remaining edges have nonzero product: one if `P a` holds, none otherwise.

**Formalization Note.** This is a count of extensions, never an existence statement: an accepted
input with two accepting extensions fails the definition (p.14, the "composite" example). The
input word is read along `inputs`, in list order, and the input edges are distinct. -/
def IsFunctionalRep {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Net V E ℚ) (inputs : List E) (P : List Bool → Prop) : Prop :=
  inputs.Nodup ∧
  (∀ v z, G.table v z = 0 ∨ G.table v z = 1) ∧
  ∀ a : List Bool, a.length = inputs.length →
    (P a → (Finset.univ.filter fun x : E → Bool =>
        inputs.map x = a ∧ ∏ v, G.table v (fun e => x e.1) ≠ 0).card = 1) ∧
    (¬ P a → (Finset.univ.filter fun x : E → Bool =>
        inputs.map x = a ∧ ∏ v, G.table v (fun e => x e.1) ≠ 0).card = 0)

end SubexpPrimes


