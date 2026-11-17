-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_IsPreservingRecord
-- name    : MonoidProdQ_Supplement_IsPreservingRecord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:11:22.430269+00:00
-- url     : https://prove2.me/theorems/a6f64301-c1b0-4526-ad1f-37863ecdaf38
-- title:
--   Product-preserving record with at most $b$ positions
-- statement:
--   Let $M$ be a monoid, $G\subseteq M$ finite, and $x=x_1\cdots x_n\in G^n$. A **record** is a partial assignment $\rho$ of letters to positions. It is a **product-preserving subword of $x$ with at most $b$ positions** if
--
--   1. it has at most $b$ positions,
--   2. every recorded letter is the input letter at its position, and
--   3. the ordered product of the recorded letters equals $x_1x_2\cdots x_n$.
--
--   Theorems 39 and 46 assert that their algorithms output such a record with probability at least $9/10$.
--
--   **Formalization Note** A record is a map from positions to optional letters; the product of the recorded letters is taken in index order with the identity at unrecorded positions. A decidability instance lets statements sum output probabilities over the event.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorems 39, 46, pp.54, 63 (Eq. (1), p.5)

import Definitions.Def_MonoidProdQ_prodMap

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorems 39 and 46, pp.54, 63 (records and
product-preserving subwords, §1, Eq. (1), p.5, and §7): a record `ρ` on the input
`x = x₁ ⋯ xₙ ∈ Gⁿ` is a product-preserving subword of at most `b` positions if

1. it has at most `b` positions (`ρ i ≠ none`),
2. every recorded letter is the input letter at its position, and
3. the ordered product of the recorded letters equals the product `x₁ ⋯ xₙ`.

**Formalization Note.** A record is a partial assignment `ρ : Fin n → Option G`, its positions
being the `i` with `ρ i = some a`. The product of the recorded letters, in index order, is
computed with the identity in place of the unrecorded positions. The decidability instance below
lets the statements take the probability of this event. -/
def IsPreservingRecord {M : Type*} [Monoid M] {G : Finset M} {n : ℕ} (x : Fin n → G) (b : ℕ)
    (ρ : Fin n → Option G) : Prop :=
  (Finset.univ.filter fun i => (ρ i).isSome).card ≤ b ∧
    (∀ i a, ρ i = some a → a = x i) ∧
    (List.ofFn fun i => ((ρ i).map fun a : G => (a : M)).getD 1).prod = prodMap G n x

instance IsPreservingRecord.instDecidable {M : Type*} [Monoid M] [DecidableEq M] {G : Finset M}
    {n : ℕ} (x : Fin n → G) (b : ℕ) (ρ : Fin n → Option G) :
    Decidable (IsPreservingRecord x b ρ) := by
  unfold IsPreservingRecord; infer_instance

end MonoidProdQ.Supplement


