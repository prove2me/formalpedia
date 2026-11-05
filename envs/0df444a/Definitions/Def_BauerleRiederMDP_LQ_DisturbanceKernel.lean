-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_DisturbanceKernel
-- name    : BauerleRiederMDP_LQ_DisturbanceKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:49.875849+00:00
-- url     : https://prove2.me/theorems/498d1a4d-1946-4293-ad73-a3d72ef644c4
-- title:
--   The transition kernel $Q^Z(\cdot\mid x,a)$ of a Markov Decision Model with disturbances
-- statement:
--   Let $E$, $A$ and $\mathcal Z$ be measurable spaces, let $\nu$ be a probability measure on $\mathcal Z$ (the law of the disturbance $Z_{n+1}$) and let $T:E\times A\times\mathcal Z\to E$ be a transition function. The **transition kernel of the model with disturbances** is
--   $$
--   Q(B\mid x,a)=\nu\big(\{z\in\mathcal Z: T(x,a,z)\in B\}\big),
--   $$
--   the law of the next state $T(x,a,Z_{n+1})$ when the current state is $x$ and the action is $a$; the law of the disturbance depends neither on the state nor on the action.
--
--   This is how Bäuerle and Rieder turn a system equation $X_{n+1}=T(X_n,a_n,Z_{n+1})$ with independent disturbances into a Markov Decision Model; in this mission it produces the kernels of the linear-quadratic problem ($T(x,a,(A,B))=Ax+Ba$) and of the cash balance problem ($T(x,a,z)=a-z$).
--
--   **Formalization Note** The kernel is the image of $\delta_{(x,a)}\otimes\nu$ under $((x,a),z)\mapsto T(x,a,z)$, so it is measurable in $(x,a)$. Two structural lemmas record that, for a jointly measurable $T$, $Q(\cdot\mid x,a)$ is the push-forward of $\nu$ under $T(x,a,\cdot)$ and is a probability measure; for a non-measurable $T$ Mathlib's `Kernel.map` would return the zero kernel, so every use in this mission comes with a measurability proof.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.1, p.15 (PDF 30); §2.6.2, p.47 (PDF 62), data list "Q^Z(·|x, a) := distribution of Z_{n+1}"; §2.6.3, p.51 (PDF 66), same

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ

/-- **The transition kernel of a Markov Decision Model with disturbances.** Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), §2.1, p.15 (PDF 30), and the model
summaries of §2.6.2, p.47 (PDF 62) and §2.6.3, p.51 (PDF 66): "`Q^Z(·|x, a)` := distribution of
`Z_{n+1}` (independent of `(x, a)`)", the next state being `T(x, a, Z_{n+1})`. Given the law `ν` of the
disturbance `Z_{n+1}` on `𝒵` and the transition function `T : E × A × 𝒵 → E`, the kernel is
`Q(B | x, a) = ν({z | T(x, a, z) ∈ B})`, the law of `T(x, a, Z_{n+1})`.

**Formalization Note.** Built as the image of `δ_{(x,a)} ⊗ ν` under `((x, a), z) ↦ T(x, a, z)`, so
that it is a kernel (measurable in `(x, a)`). When `T` is jointly measurable this is `ν.map (T x a)`
(`disturbanceKernel_apply`); `Kernel.map` returns the zero kernel for a non-measurable `T`, so every
use in this mission supplies a measurability proof. -/
noncomputable def disturbanceKernel {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν] (T : E → A → Z → E) :
    Kernel (E × A) E :=
  (Kernel.deterministic id measurable_id ×ₖ Kernel.const (E × A) ν).map
    (fun p => T p.1.1 p.1.2 p.2)

/-- For a jointly measurable transition function, `Q(·|x,a)` is the law of `T(x, a, Z)`. -/
lemma disturbanceKernel_apply {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν] {T : E → A → Z → E}
    (hT : Measurable (fun p : (E × A) × Z => T p.1.1 p.1.2 p.2)) (xa : E × A) :
    disturbanceKernel ν T xa = ν.map (T xa.1 xa.2) := by
  rw [disturbanceKernel, Kernel.map_apply _ hT, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hT measurable_prodMk_left]
  rfl

/-- For a jointly measurable transition function, every `Q(·|x,a)` is a probability measure. -/
lemma isProbabilityMeasure_disturbanceKernel {E A Z : Type*} [MeasurableSpace E]
    [MeasurableSpace A] [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν]
    {T : E → A → Z → E} (hT : Measurable (fun p : (E × A) × Z => T p.1.1 p.1.2 p.2))
    (xa : E × A) : IsProbabilityMeasure (disturbanceKernel ν T xa) := by
  rw [disturbanceKernel_apply ν hT]
  exact Measure.isProbabilityMeasure_map (hT.comp measurable_prodMk_left).aemeasurable

end BauerleRiederMDP.LQ


