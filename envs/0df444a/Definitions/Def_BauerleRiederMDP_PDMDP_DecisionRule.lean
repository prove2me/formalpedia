-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
-- name    : BauerleRiederMDP_PDMDP_DecisionRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:53.537044+00:00
-- url     : https://prove2.me/theorems/839d7af1-9846-43ac-a3cc-89acbd427bb9
-- title:
--   Decision rules $f:S\to A$ and relaxed decision rules $f:S\to\mathcal R$
-- statement:
--   A **decision rule** assigns a control function to each state. The book notes that $f:E\to A$ is measurable if and only if there is a measurable $\tilde f:\mathbb R_+\times E\to U$ with $f(x)(t)=\tilde f(t,x)$, and it does not distinguish between $f$ and $\tilde f$. A **relaxed decision rule** $f:E\to\mathcal R$ is written $f(s,x;du)$.
--
--   A Markov policy is a sequence $(f_n)$ of decision rules, used as $\pi_t=f_n(Z_n)(t-T_n)$ between jumps.
--
--   **Formalization Note** A decision rule is the jointly measurable $\tilde f$, and a relaxed one is a Markov kernel from $\mathbb R_+\times S$ to $U$. The state type $S$ is $E$ here and $[0,T]\times E$ for the finite-horizon chain. The module also proves that a rule is a measurable map into $A$ for the σ-algebra of $A$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.244–245 and Remark 8.2.3 (ii), p.250

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- A **decision rule** `f : S → A` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.244–245, PDF 255–256). By the book, `f` is measurable
if and only if there is a measurable `f̃ : ℝ₊ × S → U` with `f(x)(t) = f̃(t,x)`, and "in the sequel
we will not distinguish between `f` and `f̃`": a decision rule is here that jointly measurable
`f̃`. -/
def DecisionRule (S U : Type*) [MeasurableSpace S] [MeasurableSpace U] : Type _ :=
  {f : ℝ × S → U // Measurable f}

/-- The control function `f(x) ∈ A` of a decision rule `f` at the state `x`. -/
def DecisionRule.control {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]
    (f : DecisionRule S U) (x : S) : ControlFn U :=
  ⟨fun t => f.1 (t, x), f.2.comp (measurable_id.prodMk measurable_const)⟩

/-- A jointly measurable rule is a measurable map into `A`, for the σ-algebra of `ControlFn`
("then `f : E → A` is measurable", Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.244, PDF 255). -/
theorem DecisionRule.measurable_control {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]
    (f : DecisionRule S U) : Measurable f.control := by
  rw [measurable_iff_comap_le, instMeasurableSpaceControlFn, MeasurableSpace.comap_iSup]
  refine iSup_le fun w => ?_
  rw [MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
  have h : Measurable fun p : S × ℝ => Real.exp (-p.2) * w.1 (p.2, f.1 (p.2, p.1)) := by
    have := w.2.1.comp ((measurable_snd).prodMk (f.2.comp (measurable_snd.prodMk measurable_fst)))
    exact ((Real.measurable_exp.comp measurable_snd.neg)).mul this
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

/-- A **relaxed decision rule** `f : S → R`, written `f(s, x; du)` by the book (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 8.2.3
(ii), p.250, PDF 261).

**Formalization Note** As for `DecisionRule`, the rule is the jointly measurable object: a Markov
kernel from `ℝ₊ × S` to `U`. -/
def RelaxedDecisionRule (S U : Type*) [MeasurableSpace S] [MeasurableSpace U] : Type _ :=
  {κ : Kernel (ℝ × S) U // IsMarkovKernel κ}

/-- The relaxed control `f(x) ∈ R` of a relaxed decision rule `f` at the state `x`. -/
noncomputable def RelaxedDecisionRule.control {S U : Type*} [MeasurableSpace S]
    [MeasurableSpace U] (f : RelaxedDecisionRule S U) (x : S) : RelaxedControl U :=
  haveI := f.2
  ⟨f.1.comap (fun t => (t, x)) (measurable_id.prodMk measurable_const), inferInstance⟩

end BauerleRiederMDP.PDMDP


