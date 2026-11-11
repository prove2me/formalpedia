-- Prove2me | Definitions.Def_OptTwoSrcExt_IsBoolDisperser
-- name    : OptTwoSrcExt_IsBoolDisperser
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:29.066909+00:00
-- url     : https://prove2.me/theorems/730901d6-4422-4e78-888d-8ae587ca19f1
-- title:
--   Boolean two-source disperser at side threshold $k$
-- statement:
--   A Boolean kernel $h:\alpha\times\beta\to\mathbb F_2$ is a **two-source disperser at side threshold $k$** if it is nonconstant on every product of sets of sizes at least $2^k$: for all finite $A\subseteq\alpha$, $B\subseteq\beta$ with
--   $$|A|\ge 2^k,\qquad |B|\ge 2^k,$$
--   there are $(a,b),(a',b')\in A\times B$ with $h(a,b)\ne h(a',b')$.
--
--   Dispersion is the one-sided, zero-error analogue of extraction; for kernels of low binary rank it upgrades to extraction with exponentially small error (Corollary 2.20).
--
--   **Formalization Note** $k$ is real and the size condition is the real inequality $2^k\le|A|$.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Definition 2.7, p.16 (PDF p.18)

import Mathlib

namespace OptTwoSrcExt

/-- **Boolean two-source disperser at side threshold `k`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Definition 2.7, printed p.16 (PDF p.18): "A Boolean
two-source disperser at side threshold k is nonconstant on every product of supports of sizes at
least 2^k."

`IsBoolDisperser k h`: for all finite sets `A ⊆ α`, `B ⊆ β` with `|A| ≥ 2^k` and `|B| ≥ 2^k`, the
Boolean kernel `h` takes two different values on `A × B`.

**Formalization Note.** Boolean values are `ZMod 2`; `k` is real (the paper uses thresholds such as
`ρn`), and the size condition is the real inequality `2^k ≤ |A|`. -/
def IsBoolDisperser {α β : Type*} (k : ℝ) (h : α → β → ZMod 2) : Prop :=
  ∀ (A : Finset α) (B : Finset β), (2 : ℝ) ^ k ≤ A.card → (2 : ℝ) ^ k ≤ B.card →
    ∃ a ∈ A, ∃ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, h a b ≠ h a' b'

end OptTwoSrcExt


