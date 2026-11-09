-- Prove2me | Definitions.Def_ModLatSVP_IsChain
-- name    : ModLatSVP_IsChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:37.296922+00:00
-- url     : https://prove2.me/theorems/7e61715a-878b-41f9-93f1-422d59fe8591
-- title:
--   Subfield chains $K=K_0\supsetneq\cdots\supsetneq K_h$ with bounded relative degrees
-- statement:
--   For integers $s_0,d_0$, a **subfield chain** of a number field $K$ with relative degrees at most $s_0$ ending in degree at most $d_0$ is a chain of subfields
--
--   $$K=K_0\supsetneq K_1\supsetneq\cdots\supsetneq K_h,\qquad [K_j:K_{j+1}]\le s_0,\qquad [K_h:\mathbb Q]\le d_0 .$$
--
--   The case $h=0$ ($[K:\mathbb Q]\le d_0$) is allowed. Such chains drive the subfield descent of the paper's algorithms.
--
--   **Formalization Note** The subfields are intermediate fields of $K/\mathbb Q$, indexed by $0,\dots,h$; by the tower law $[K_j:K_{j+1}]\le s_0$ is written $[K_j:\mathbb Q]\le s_0[K_{j+1}:\mathbb Q]$.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 3.4, p.20 (PDF p.20); Lemma 3.6(i), p.21

import Mathlib

namespace ModLatSVP

/-- A subfield chain with bounded relative degrees ending at a field of bounded degree. Kim, Lee, Son,
*Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027
submission (manuscript sha256 e7151fad…), Theorem 3.4, p.20 (PDF p.20) and Lemma 3.6(i), p.21:
"K = K₀ ⊋ K₁ ⊋ ⋯ ⊋ K_h with [K_j : K_{j+1}] ≤ s₀ and [K_h : ℚ] ≤ d₀".

`IsChain K s₀ d₀ F h` says that `F 0 = K`, that `F (j+1) ⊊ F j` and `[F j : ℚ] ≤ s₀ · [F (j+1) : ℚ]` for
every `j < h`, and that `[F h : ℚ] ≤ d₀`. Values of `F` beyond `h` are irrelevant.

**Formalization Note.** Subfields are intermediate fields of `K/ℚ`. By the tower law
`[K_j : K_{j+1}] = [K_j : ℚ] / [K_{j+1} : ℚ]`, so the relative-degree bound is written multiplicatively.
`h = 0` is allowed (then `[K : ℚ] ≤ d₀`). -/
def IsChain (K : Type*) [Field K] [CharZero K] (s₀ d₀ : ℕ) (F : ℕ → IntermediateField ℚ K) (h : ℕ) :
    Prop :=
  F 0 = ⊤ ∧
  (∀ j < h, F (j + 1) < F j ∧ Module.finrank ℚ (F j) ≤ s₀ * Module.finrank ℚ (F (j + 1))) ∧
  Module.finrank ℚ (F h) ≤ d₀

end ModLatSVP


