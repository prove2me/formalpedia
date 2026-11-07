-- Prove2me | Definitions.Def_MonDepMW_partsHit
-- name    : MonDepMW_partsHit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:04.417166+00:00
-- url     : https://prove2.me/theorems/f87be43a-0d76-4155-b08c-cfa6d7e8eb41
-- title:
--   Counting parts of a partition
-- statement:
--   For a partition $\mathcal P$ of $V=\{0,\dots,n-1\}$ this item defines $|\mathcal P|$, the number of parts, and the number of parts of $\mathcal P$ that a set $X\subseteq V$ intersects.
--
--   **Formalization Note** Partitions are setoids on `Fin n`: $\mathcal P\sqsubseteq\mathcal Q$ ("$\mathcal P$ is finer") is `P ≤ Q`, the partition into singletons is `⊥`, the partition with the one part $V$ is `⊤`. With this convention the empty graph has a merge sequence, as the paper intends. Vertex sets are finite, so the cardinalities are genuine.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, pp.11–14

import Mathlib

set_option autoImplicit false

namespace MonDepMW

/-- `|𝒫|`, the number of parts of a partition of `Fin n`, given as a setoid (Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.11: partitions; `𝒫 ⊑ 𝒬`, "𝒫 is
finer than 𝒬", is `𝒫 ≤ 𝒬`; the partition into singletons is `⊥`, the partition with the one part `V` is `⊤`).

**Formalization Note.** Setoids also give the empty graph its one-element merge sequence (`⊥ = ⊤` on `Fin 0`), as the
paper intends. -/
noncomputable def numParts {n : ℕ} (P : Setoid (Fin n)) : ℕ := Nat.card (Quotient P)

/-- The number of parts of `P` that the set `X` intersects. All sets are finite here, as the vertex set is `Fin n`, so
`Set.ncard` is the true cardinality. -/
noncomputable def partsHit {n : ℕ} (P : Setoid (Fin n)) (X : Set (Fin n)) : ℕ :=
  (Quotient.mk P '' X).ncard

end MonDepMW


