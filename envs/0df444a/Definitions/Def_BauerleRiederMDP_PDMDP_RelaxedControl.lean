-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
-- name    : BauerleRiederMDP_PDMDP_RelaxedControl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:04.609637+00:00
-- url     : https://prove2.me/theorems/7a281e37-f190-411f-9439-18965f977701
-- title:
--   Relaxed controls $\mathcal R$ (8.6), strong Carathéodory functions and the Young topology
-- statement:
--   The set of **relaxed controls** is $\mathcal R:=\{\alpha:\mathbb R_+\to\mathbb P(U)\text{ measurable}\}$, and a deterministic control is the relaxed control whose $\alpha_t$ are one-point measures. The class $\mathrm{Car}(\mathbb R_+\times U)$ of **strong Carathéodory functions** consists of the $w$ continuous in the second argument, measurable in the first, with
--   $$
--   \int_0^\infty\max_{u\in U}|w(t,u)|\,dt<\infty.
--   $$
--   The **Young topology** on $\mathcal R$ is the coarsest topology making
--   $$
--   \alpha\mapsto\int_0^\infty\int_U w(t,u)\,\alpha_t(du)\,dt
--   $$
--   continuous for all $w\in\mathrm{Car}(\mathbb R_+\times U)$.
--
--   The Young topology is what makes the enlarged action space compact and the target function upper semicontinuous at once.
--
--   **Formalization Note** A measurable map into $\mathbb P(U)$ is a Markov kernel from the time axis to $U$. $\mathcal R$ holds functions, not classes modulo null sets, so the topology is pseudometrizable rather than Hausdorff; the book's metric space is the quotient, and continuity and compactness read the same on both.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.6), p.249, and Remark 8.2.3, pp.249–250

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- The set of **relaxed controls** `R := {α : ℝ₊ → IP(U) measurable}` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.6), p.249,
PDF 260).

**Formalization Note** A measurable map into the probability measures on `U` is a Markov kernel
from the time axis to `U`, and `α.1 t` is the measure `α_t`. Time is `ℝ`, as in `ControlFn`. -/
def RelaxedControl (U : Type*) [MeasurableSpace U] : Type _ :=
  {κ : Kernel ℝ U // IsMarkovKernel κ}

/-- A deterministic control as a relaxed control: the measures `α_t` are one-point measures on
`U` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.249, PDF 260). -/
noncomputable def ControlFn.toRelaxed {U : Type*} [MeasurableSpace U] (α : ControlFn U) :
    RelaxedControl U :=
  ⟨Kernel.deterministic α.1 α.2, inferInstance⟩

/-- The class `Car(ℝ₊ × U)` of **strong Carathéodory functions** (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 8.2.3, p.249,
PDF 260): `w` is continuous in the second argument, measurable in the first, and
`∫_0^∞ max_{u ∈ U} |w(t,u)| dt < ∞`.

**Formalization Note** The maximum is a supremum in `ℝ≥0∞`, so the integrability is a Lebesgue
integral, with no junk value. -/
def IsStrongCaratheodory {U : Type*} [TopologicalSpace U] (w : ℝ × U → ℝ) : Prop :=
  (∀ t, Continuous fun u => w (t, u)) ∧ (∀ u, Measurable fun t => w (t, u)) ∧
    (∫⁻ t in Set.Ioi (0 : ℝ), ⨆ u, ENNReal.ofReal |w (t, u)|) < ⊤

/-- The **Young topology** on `R` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 8.2.3, p.249, PDF 260): the coarsest topology such
that `α ↦ ∫_0^∞ ∫_U w(t,u) α_t(du) dt` is continuous for every `w ∈ Car(ℝ₊ × U)`.

**Formalization Note** `R` holds functions rather than classes modulo Lebesgue-null sets, so the
topology is pseudometrizable on it, not Hausdorff; the book's separable metric space is the
quotient. Continuity and compactness read the same on both. -/
noncomputable instance instTopologicalSpaceRelaxedControl (U : Type*) [MeasurableSpace U] [TopologicalSpace U] :
    TopologicalSpace (RelaxedControl U) :=
  ⨅ w : {w : ℝ × U → ℝ // IsStrongCaratheodory w},
    TopologicalSpace.induced
      (fun α : RelaxedControl U => ∫ t in Set.Ioi (0 : ℝ), ∫ u, w.1 (t, u) ∂(α.1 t))
      inferInstance

end BauerleRiederMDP.PDMDP


