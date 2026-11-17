-- Prove2me | Definitions.Def_ReplicableOL_Supplement_Seed
-- name    : ReplicableOL_Supplement_Seed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:15:46.865718+00:00
-- url     : https://prove2.me/theorems/15ba6330-ecf5-4f62-8850-c5769e8f92fb
-- title:
--   Seed space of DALR
-- statement:
--   The **seed** of DALR is $R=(\chi,(\omega_{i,q}))$: one real level $\chi$ and one real offset $\omega_{i,q}$ for every level $i\in[K]$ and every level-$i$ anchor $q=0,\dots,T/A_i-1$.
--
--   **Formalization Note** Levels are $0$-based in Lean: the index `i : Fin K` is the paper's level $i+1$, with anchors `q : Fin (T / A (i+1))`. The space carries the product measurable structure.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, p.18

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_Chain

namespace ReplicableOL.Supplement

/-- **DALR seed space.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, p.18. "Seed. R = (χ, (ω_{i,q})) with … i ∈ [K] and q = 0, …, T/A_i − 1": one level `χ ∈ ℝ` and one offset `ω_{i,q} ∈ ℝ` per level-`i` anchor `q`.

**Formalization Note.** Levels are 0-based: the Lean index `i : Fin K` is the paper's level `i + 1`, and its anchors are `q : Fin (T / A_{i+1})`. The measurable structure is the product one. -/
abbrev Seed {T : ℕ} (C : Chain T) : Type :=
  ℝ × ((i : Fin C.K) → Fin (T / C.A (i.val + 1)) → ℝ)

end ReplicableOL.Supplement


