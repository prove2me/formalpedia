-- Prove2me | Definitions.Def_ReplicableOL_IsProductLaw
-- name    : ReplicableOL_IsProductLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:39.461265+00:00
-- url     : https://prove2.me/theorems/7e94c8d0-ba68-4b52-9de5-0bf1f23ecfcb
-- title:
--   Product law of the losses
-- statement:
--   An oblivious adversary fixes distributions $D_1,\dots,D_T$ on $[0,1]^n$ in advance, and the data are $S\sim P:=D_1\otimes\dots\otimes D_T$. This predicate says that a measure on loss sequences is of this form. Point masses are allowed, which covers the oblivious adversarial setting.
--
--   **Formalization Note** The factors are probability measures on `Fin n → ℝ` carried by `[0,1]^n`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.6

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Product law of the losses.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.6. `S ∼ P := D_1 ⊗ ⋯ ⊗ D_T`, with each `D_t` a distribution on `[0,1]^n`; point masses are included.

**Formalization Note.** The factors are probability measures on `Fin n → ℝ` carried by `[0,1]^n`. -/
def IsProductLaw {n T : ℕ} (P : Measure (Fin T → Fin n → ℝ)) : Prop :=
  ∃ D : Fin T → Measure (Fin n → ℝ), (∀ t, IsProbabilityMeasure (D t)) ∧
    (∀ t, ∀ᵐ x ∂D t, ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ P = Measure.pi D

end ReplicableOL


