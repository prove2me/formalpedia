-- Prove2me | Definitions.Def_NestedLogitAssort_General_Light
-- name    : NestedLogitAssort_General_Light
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:43.756159+00:00
-- url     : https://prove2.me/theorems/32df514c-b193-4982-95b7-46a2e4e89af9
-- title:
--   The $k$ lightest products of a weight listing
-- statement:
--   For a permutation $\sigma$ of $N$ and $k\in\{0,\dots,n\}$, this is the set
--
--   $$
--   L_\sigma(k)=\{\sigma(1),\dots,\sigma(k)\}
--   $$
--
--   of the first $k$ products of the listing. When $\sigma$ lists the products of nest $i$ by nondecreasing weight, these are the $k$ products with the smallest preference weights.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 5, p. 25

import Mathlib

namespace NestedLogitAssort.General

/-- **The `k` products with the smallest preference weights.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 5, p. 25 (unnumbered).

For a listing `σ` of the products by nondecreasing weight (`IsWeightOrder`), `Light σ k` is the
set `{σ 0, …, σ (k − 1)}` of the first `k` products of the listing. -/
def Light {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun a : Fin n => a.val < k)).map σ.toEmbedding

end NestedLogitAssort.General


