-- Prove2me | Definitions.Def_MultiSelectPandora_topSum
-- name    : MultiSelectPandora_topSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:43.118353+00:00
-- url     : https://prove2.me/theorems/3561984e-d6be-4958-bc41-5c28b7fc2563
-- title:
--   The sum of the $k$ largest elements
-- statement:
--   $\sum\mathrm{top}_k(S)$ is the sum of the entries of $\mathrm{top}_k(S)$, "the vector of the $k$ largest elements of $S$ together with $k$ zeros, so that its entries are nonnegative". A negative element of $S$ never counts.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.5 (PDF p.6)

import Mathlib

namespace MultiSelectPandora

/-- **`Σ top_k(S)`, the sum of the `k` largest elements of a multiset, padded by `k` zeros.** Beyhaghi–Han–Luqman manuscript,
§2.2, p.5 (PDF p.6): "the vector of the `k` largest elements of `S` together with `k` zeros, so that its entries are
nonnegative". -/
noncomputable def topSum (k : ℕ) (L : List ℝ) : ℝ :=
  (((L ++ List.replicate k 0).insertionSort (· ≥ ·)).take k).sum

end MultiSelectPandora


