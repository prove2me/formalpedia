-- Prove2me | Definitions.Def_RSSubspaceDesign_Supplement_IsListDecodable
-- name    : RSSubspaceDesign_Supplement_IsListDecodable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:34:39.523538+00:00
-- url     : https://prove2.me/theorems/ec4e11b3-733c-45de-8094-ec86a51c6970
-- title:
--   $(\delta, L)$-list decodability
-- statement:
--   Let $C \subseteq \Sigma^n$ be a code, $\delta$ a real number and $L$ a natural number. The code $C$ is **$(\delta, L)$-list-decodable** if every closed ball of relative radius $\delta$ contains at most $L$ codewords: for every $y \in \Sigma^n$,
--
--   $$
--   |\{c \in C : \Delta(c, y) \le \delta\}| \le L .
--   $$
--
--   This is the list-decoding notion of the generalized Singleton bound (Theorem 1.2) and of the strongly explicit construction (Theorem 1.3).
--
--   **Formalization Note** The paper's standing ranges $\delta < 1$ and $L \ge 1$ are not part of the predicate; each statement fixes its own parameters. Sizes are extended natural numbers (`Set.encard`), so an infinite set is never counted as $0$.
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Definition 2.2, p.11

import Mathlib
import Definitions.Def_RSSubspaceDesign_Supplement_relDist

namespace RSSubspaceDesign

namespace Supplement

/-- **Definition 2.2 (List decoding).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Definition 2.2, p.11.

A code `C ⊆ Σⁿ` is `(δ, L)`-list-decodable if, for every `y ∈ Σⁿ`,
`|{c ∈ C : Δ(c, y) ≤ δ}| ≤ L`, where `Δ` is the relative Hamming distance (`relDist`).

**Formalization Note.** The paper's preconditions `δ < 1` and `L ≥ 1` an integer are not bundled:
`δ` is any real and `L` any natural number; statements that use the predicate state their own
parameters. The ball is closed (`≤ δ`). Sizes are `Set.encard`, so an infinite set never takes the
junk size `0`. Coordinates are `Fin n`. -/
def IsListDecodable {Sig : Type*} {n : ℕ} (C : Set (Fin n → Sig)) (δ : ℝ) (L : ℕ) : Prop :=
  ∀ y : Fin n → Sig, {c ∈ C | relDist c y ≤ δ}.encard ≤ L

end Supplement

end RSSubspaceDesign


