-- Prove2me | Definitions.Def_ProofCryptoSynergy_IsSubexp
-- name    : ProofCryptoSynergy_IsSubexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:36.470396+00:00
-- url     : https://prove2.me/theorems/944a938a-49b1-42f5-8b00-53b1e4bdc8a9
-- title:
--   Subexponential functions
-- statement:
--   A function $s:\mathbb N\to\mathbb R$ is **subexponential** if for every integer $c\ge 1$, for all sufficiently large $n$,
--   $$s(n)\le 2^{n^{1/c}}.$$
--   This is the condition $s(n)\le 2^{n^{o(1)}}$ used throughout the paper.
--
--   **Formalization Note** The bound is eventual for each $c$. Read pointwise for each $n$, the printed clause would force $s(n)\le 2$ for all $n\ge1$.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.1, p.16 (PDF 18)

import Mathlib

namespace ProofCryptoSynergy

/-- **Subexponential function** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.1, p.16 (PDF 18): "A subexponential function is any
`p(n) ≤ 2^{n^{o(1)}}`, i.e., `p(n) ≤ 2^{n^{1/c}}` for every `c ≥ 1`").

**Formalization Note** The bound is eventual for each `c`. Read pointwise for each `n`, the printed
clause would force `p(n) ≤ 2` for all `n ≥ 1` (let `c → ∞`); the `o(1)` in the same sentence is
asymptotic. `c` ranges over the positive integers, which is the same condition because
`2^{n^{1/c}}` is decreasing in `c` for `n ≥ 1`. -/
def IsSubexp (s : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∀ᶠ n : ℕ in Filter.atTop, s n ≤ (2 : ℝ) ^ ((n : ℝ) ^ (1 / (c : ℝ)))

end ProofCryptoSynergy


