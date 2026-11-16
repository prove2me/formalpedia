-- Prove2me | Definitions.Def_LDPSelect_Supplement_Hetero
-- name    : LDPSelect_Supplement_Hetero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:37.061357+00:00
-- url     : https://prove2.me/theorems/8447b76a-7a9e-4698-b03d-08c287a1e22f
-- title:
--   User-specific privacy budgets: $W^{\mathrm N}$ with budgets $a_i$
-- statement:
--   With **user-specific budgets**, user $i$ has its own privacy parameter $a_i$ with $1\le a_i<\infty$: its report kernel must satisfy $Q_i(A\mid x)\le a_i\,Q_i(A\mid x')$ for every measurable $A$, all values $x,x'$, and every realization of the history. Everything else is the mechanism model of Definition 8. The optimal non-interactive reward with these budgets, and its competitive ratio against the prophet, are defined as for a common budget.
--
--   This model states the heterogeneous part of Theorem 5.
--
--   **Formalization Note** With a constant budget $a_i=a$ the constraint and the value coincide with the published ones (checked definitionally in the mission's sanity file).
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 5, p.3 (pdf p.4); A.4, p.17 (pdf p.18)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Supplement_Ratios

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

/-!
# User-specific privacy budgets

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 5, p.3; A.4, p.17.

**Formalization Note.** User `i` has its own budget `a i` (the paper's `a_i`, `1 ≤ a_i < ∞`). The
mechanism model is the published `LDPSelect.Mechanism`, unchanged; only the privacy constraint is
per user. With a constant budget, `PrivateHet M (fun _ => a)` is `M.Private a` and `WNhet` is `WN`
(definitionally; checked in the mission's sanity file).
-/

open LDPSelect

variable {n : ℕ} {Z : Type} [MeasurableSpace Z]

/-- User `i`'s report kernel is `a i`-locally private at every realization of the history. -/
def PrivateHet (M : Mechanism n Z) (a : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (h : Fin i → Z) (x x' : ℝ≥0) (A : Set Z), MeasurableSet A →
    M.Q i (h, x) A ≤ ENNReal.ofReal (a i) * M.Q i (h, x') A

/-- The optimal non-interactive reward with user-specific budgets. -/
noncomputable def WNhet (a : Fin n → ℝ) (F : Family n) (P : Fin n → Measure ℝ≥0) : ℝ≥0∞ :=
  ⨆ (Z : Type) (_ : MeasurableSpace Z) (M : Mechanism n Z) (_ : PrivateHet M a) (_ : M.Respects F)
    (_ : M.NonInteractive), M.reward P

/-- `inf_X W^N_F(X) / M_F(X)` with user-specific budgets. -/
noncomputable def ratioNhet (a : Fin n → ℝ) (F : Family n) : ℝ≥0∞ :=
  ⨅ (P : Fin n → Measure ℝ≥0) (_ : Admissible F P), WNhet a F P / prophet F P

end LDPSelect.Supplement


