-- Prove2me | Definitions.Def_DetCCHard_encodeListInput
-- name    : DetCCHard_encodeListInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:35.990622+00:00
-- url     : https://prove2.me/theorems/337026e5-343c-44d8-9a83-213a1c8caf93
-- title:
--   Explicit encodings of the input and output of the tuple-list construction
-- statement:
--   The **input** of the construction of Lemma 7.1 is the tuple length $q$ in unary (a block of $q$ ones), then one block $[p, r]$ per letter $i \in [m]$ with $\mu(i) = p/r$ in lowest terms. The **output** lists, for each label $\ell$ in order, a block $[p, r, z_1(\ell), \dots, z_q(\ell)]$ with $\nu(\ell) = p/r$ in lowest terms and the letters of the decoded tuple, all in binary.
--
--   Both encodings are injective for nonnegative (input) and positive (output) weights (verification file).
--
--   **Formalization Note** $q$ is unary because the output has $q$ letters per label; "polynomial in $q$" is then polynomial in the input length.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 7.1, p.33

import Mathlib
import Definitions.Def_DetCCHard_CodeSym

namespace DetCCHard

/-- The **input of the tuple-list construction** of Lemma 7.1 (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, p.33): the tuple length `q` **in unary** (a
block of `q` ones), then, for each letter `i` of the alphabet `[m]`, a block `[p, r]` with
`μ(i) = p/r` in lowest terms, numerator and denominator in binary.

**Formalization Note** `q` is written in unary because the output has `q` coordinates per label,
so "polynomial in `q`" is polynomial in this input length. Weights are nonnegative, so the
numerator is a natural number. -/
def encodeListInput {m : ℕ} (q : ℕ) (μ : Fin m → ℚ) : List CodeSym :=
  encodeBlocks (List.replicate q 1 :: List.ofFn fun i => [(μ i).num.toNat, (μ i).den])

/-- The **output of the tuple-list construction** of Lemma 7.1 (p.33): for each label
`ℓ ∈ [ℓ₀]`, in order, a block `[p, r, z_1(ℓ), …, z_q(ℓ)]` with `ν(ℓ) = p/r` in lowest terms and the
letters of the decoded tuple, all in binary. -/
def encodeListOutput {ℓ₀ q m : ℕ} (ν : Fin ℓ₀ → ℚ) (z : Fin ℓ₀ → Fin q → Fin m) :
    List CodeSym :=
  encodeBlocks (List.ofFn fun ℓ =>
    (ν ℓ).num.toNat :: (ν ℓ).den :: List.ofFn fun j => ((z ℓ j : Fin m) : ℕ))

end DetCCHard


