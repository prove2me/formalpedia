-- Prove2me | Definitions.Def_RSSubspaceDesign_Supplement_IsListRecoverable
-- name    : RSSubspaceDesign_Supplement_IsListRecoverable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:34:56.251754+00:00
-- url     : https://prove2.me/theorems/95b350a8-7d77-4d26-afe5-798bc1fdb307
-- title:
--   $(\delta, \ell, L)$-list recoverability
-- statement:
--   A code $C \subseteq \Sigma^n$ is **$(\delta, \ell, L)$-list-recoverable** if, for all lists $S_1, \dots, S_n \subseteq \Sigma$ of size $|S_i| \le \ell$, at most $L$ codewords disagree with the lists in at most $\delta n$ coordinates:
--
--   $$
--   \bigl|\{c \in C : |\{i \in [n] : c_i \notin S_i\}| \le \delta n\}\bigr| \le L .
--   $$
--
--   For $\ell = 1$ this is list decoding at radius $\delta$. List recovery is the input-list generalization used in Theorem 3.2.
--
--   **Formalization Note** Coordinates are `Fin n`; $\delta n$ is a real product; set sizes are `Set.encard`.
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Definition 2.6, p.11

import Mathlib

namespace RSSubspaceDesign

namespace Supplement

open Classical in
/-- **Definition 2.6 (List recovery).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version,
sha256 cf26424b…f36206), Definition 2.6, p.11.

A code `C ⊆ Σⁿ` is `(δ, ℓ, L)`-list-recoverable if, for every `S₁, …, Sₙ ⊆ Σ` with `|Sᵢ| ≤ ℓ`,
`|{c ∈ C : |{i ∈ [n] : cᵢ ∉ Sᵢ}| ≤ δn}| ≤ L`.

**Formalization Note.** Coordinates are `Fin n` (0-based). Sizes are `Set.encard` (values in
`ℕ∞`), so an infinite set never takes the junk size `0`. `δ` is real and `δn` is the real product;
`ℓ` and `L` are natural numbers. The code is any set of words (an `F`-linear code is passed as its
carrier). -/
def IsListRecoverable {Sig : Type*} {n : ℕ} (C : Set (Fin n → Sig)) (δ : ℝ) (ℓ L : ℕ) : Prop :=
  ∀ S : Fin n → Set Sig, (∀ i, (S i).encard ≤ ℓ) →
    {c ∈ C | ((Finset.univ.filter fun i => c i ∉ S i).card : ℝ) ≤ δ * n}.encard ≤ L

end Supplement

end RSSubspaceDesign


