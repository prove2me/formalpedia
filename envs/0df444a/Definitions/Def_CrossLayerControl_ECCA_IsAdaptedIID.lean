-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_IsAdaptedIID
-- name    : CrossLayerControl_ECCA_IsAdaptedIID
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:46.329693+00:00
-- url     : https://prove2.me/theorems/ad646b2b-d063-4b36-a659-1d4ea94b5411
-- title:
--   The arrival–state pair is i.i.d. over slots (relative to a filtration)
-- statement:
--   On a probability space $(\Omega,\Pr)$ with a filtration $(\mathcal F_t)$, arrivals $A(t)$ and states $S(t)$ are i.i.d. with slot law $\mu$ relative to $(\mathcal F_t)$ when, for every $t$,
--
--   1. $(A(t),S(t))$ is $\mathcal F_t$-measurable;
--   2. the law of $(A(t),S(t))$ is $\mu$;
--   3. $(A(t+1),S(t+1))$ is independent of $\mathcal F_t$.
--
--   This is the paper's assumption that the pair $[S(t);A(t)]$ is i.i.d. over timeslots, with $\mathcal F_t$ the information available to the controller at slot $t$.
--
--   **Formalization Note** For the natural filtration of the pair process this is exactly "i.i.d. over timeslots"; a larger filtration allows randomized tie-breaking by the controller.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §6.1, p. 100; Theorem 6.3, p. 115

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CrossLayerControl.ECCA

/-- **The arrival–state pair is i.i.d. over timeslots, relative to a filtration.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), §6.1, p. 100: "we continue to assume that the pair [S(t);A(t)] is
i.i.d. over timeslots"; Theorem 6.3, p. 115: "if the arrival vector A(t) and topology state S(t) is
i.i.d. over timeslots".

On a probability space `(Ω, Pr)` with filtration `ℱ`, `IsAdaptedIID Pr ℱ A S μ` asserts, for every
slot `t`,
1. the pair `(A(t), S(t))` is `ℱ t`-measurable;
2. its law is `μ` (the same law at every slot);
3. the pair `(A(t + 1), S(t + 1))` is independent of `ℱ t`.

**Formalization Note.** This is the i.i.d. property of the pair process stated relative to a
filtration `ℱ` to which the control decisions are adapted: `ℱ t` is the information available at
slot `t` (past and current arrivals and states, and any randomization of the controller). For the
natural filtration of the pair process it is exactly "i.i.d. over timeslots". -/
def IsAdaptedIID {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Pr : Measure Ω) (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮)
    (μ : Measure ((Fin L → ℝ) × 𝒮)) : Prop :=
  (∀ t, Measurable[ℱ t] (fun ω => (A t ω, S t ω))) ∧
  (∀ t, Pr.map (fun ω => (A t ω, S t ω)) = μ) ∧
  (∀ t, Indep (MeasurableSpace.comap (fun ω => (A (t + 1) ω, S (t + 1) ω)) inferInstance)
    (ℱ t) Pr)

end CrossLayerControl.ECCA


