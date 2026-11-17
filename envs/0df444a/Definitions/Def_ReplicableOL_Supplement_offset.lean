-- Prove2me | Definitions.Def_ReplicableOL_Supplement_offset
-- name    : ReplicableOL_Supplement_offset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:16:53.493192+00:00
-- url     : https://prove2.me/theorems/dfacc01e-24b8-4fe1-b7c3-9ef000c57e52
-- title:
--   Offset $\omega_{i,q}$ of a seed
-- statement:
--   For a seed $R=(\chi,(\omega_{i,q}))$, this reads the offset $\omega_{i+1,q}$ of the level-$(i+1)$ anchor $q$.
--
--   **Formalization Note** Levels are $0$-based in Lean. The accessor is total: indices outside the seed (level $\ge K$ or anchor $\ge T/A_{i+1}$) return $0$, and DALR never reads them. The module also proves that the offset is a measurable function of the seed.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, p.18

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_Seed

namespace ReplicableOL.Supplement

/-- **The offset $\omega_{i+1,q}$ read from a seed.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, p.18. `offset C r i q` is the paper's `ω_{i+1,q}` (0-based level index `i`).

**Formalization Note.** A total accessor: out-of-range indices return `0`; DALR reads only in-range indices (level `i < K`, anchor `q < T / A_{i+1}`). -/
noncomputable def offset {T : ℕ} (C : Chain T) (r : Seed C) (i q : ℕ) : ℝ :=
  if h : i < C.K ∧ q < T / C.A (i + 1) then r.2 ⟨i, h.1⟩ ⟨q, h.2⟩ else 0

/-- The offset is a measurable function of the seed. -/
theorem measurable_offset {T : ℕ} (C : Chain T) (i q : ℕ) :
    Measurable fun r : Seed C => offset C r i q := by
  unfold offset
  by_cases h : i < C.K ∧ q < T / C.A (i + 1)
  · simp only [h, and_self, dite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
  · simp only [h, dite_false]; exact measurable_const

end ReplicableOL.Supplement


