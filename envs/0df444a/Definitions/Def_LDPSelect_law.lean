-- Prove2me | Definitions.Def_LDPSelect_law
-- name    : LDPSelect_law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:19.705655+00:00
-- url     : https://prove2.me/theorems/6f58311e-f17e-4f7b-b3dc-a20bf054d7de
-- title:
--   The law of a run of a mechanism and its expected reward
-- statement:
--   Fix a mechanism and independent laws $P_1,\dots,P_n$ of the values. The run is built forward: when user $i$ arrives, draw $X_i\sim P_i$ independently of the past, then the report $Z_i\sim Q_i(\cdot\mid Z_{<i},X_i)$, then the decision $b_i\in\{0,1\}$ from the acceptance kernel applied to the earlier reports and decisions and $Z_i$. The record of user $i$ is $(X_i,Z_i,b_i)$, and the law of the records of the first $i$ users is defined by this recursion.
--
--   The **expected reward** is
--
--   $$\mathbb E\,X(A)=\mathbb E\sum_{i:\,b_i=1}X_i,$$
--
--   computed in $[0,\infty]$.
--
--   **Formalization Note** Each step is a composition-product of kernels with every map measurable, so the law is a probability measure (checked in the mission's sanity file). No kernel ever receives an earlier value.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §2, p.5 (pdf p.6), Definition 8

import Mathlib
import Definitions.Def_LDPSelect_Mechanism

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-!
# The law of a run and its reward

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Definition 8, p.5.

**Formalization Note.** The law of the records `(x_j, z_j, b_j)` of users `j < i` is built forward. At
step `i`, `x_i ∼ P i` is independent of the record, then `z_i ∼ Q i (earlier reports, x_i)`, then
`b_i ∼ dec i (earlier reports and decisions, z_i)`. Neither kernel receives an earlier value. Values
are independent because each is drawn from the constant kernel `P i`. Every map used is measurable,
which the mission's sanity file checks by proving that the law is a probability measure.
-/

variable {n : ℕ} {Z : Type} [MeasurableSpace Z]

/-- The record `(x, z, b)` of one user. -/
abbrev Rec (Z : Type) := ℝ≥0 × Z × Bool

/-- The reports in a record. -/
def reports {i : ℕ} (ω : Fin i → Rec Z) : Fin i → Z := fun j => (ω j).2.1

/-- The reports and decisions in a record; values are dropped. -/
def trail {i : ℕ} (ω : Fin i → Rec Z) : Fin i → Z × Bool := fun j => ((ω j).2.1, (ω j).2.2)

lemma measurable_reports {i : ℕ} : Measurable (reports (Z := Z) (i := i)) :=
  measurable_pi_lambda _ fun j => (measurable_pi_apply j).snd.fst

lemma measurable_trail {i : ℕ} : Measurable (trail (Z := Z) (i := i)) :=
  measurable_pi_lambda _ fun j =>
    ((measurable_pi_apply j).snd.fst).prodMk ((measurable_pi_apply j).snd.snd)

/-- One step of a run: given the record, draw `x ∼ P i`, then the report, then the decision. -/
noncomputable def Mechanism.step (M : Mechanism n Z) (P : Fin n → Measure ℝ≥0) (i : Fin n) :
    Kernel (Fin i → Rec Z) (Rec Z) :=
  Kernel.const _ (P i) ⊗ₖ
    ((M.Q i).comap (fun p : (Fin i → Rec Z) × ℝ≥0 => (reports p.1, p.2))
        ((measurable_reports.comp measurable_fst).prodMk measurable_snd) ⊗ₖ
      (M.dec i).comap (fun p : ((Fin i → Rec Z) × ℝ≥0) × Z => (trail p.1.1, p.2))
        ((measurable_trail.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))

/-- The law of the records of the first `i` users (Definition 8, p.5). -/
noncomputable def Mechanism.law (M : Mechanism n Z) (P : Fin n → Measure ℝ≥0) :
    (i : ℕ) → i ≤ n → Measure (Fin i → Rec Z)
  | 0, _ => Measure.dirac default
  | i + 1, hi =>
    (M.law P i (Nat.le_of_succ_le hi) ⊗ₘ M.step P ⟨i, hi⟩).map
      (fun p => Fin.snoc (α := fun _ => Rec Z) p.1 p.2)

/-- The expected reward `E X(A) = E ∑_{i ∈ A} X_i` (Definition 8, p.5). -/
noncomputable def Mechanism.reward (M : Mechanism n Z) (P : Fin n → Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ i : Fin n, (if (ω i).2.2 = true then ((ω i).1 : ℝ≥0∞) else 0) ∂(M.law P n le_rfl)

end LDPSelect


