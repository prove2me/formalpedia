-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_IsAdmissiblePolicy
-- name    : CrossLayerControl_ECCA_IsAdmissiblePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:39.984881+00:00
-- url     : https://prove2.me/theorems/e44a3d39-dd2e-4d33-907e-e3ff6ccf08fa
-- title:
--   Admissible policies
-- statement:
--   On a probability space with arrivals $A(t)$ and states $S(t)$, decisions $R(t)$ (admitted data) and $P(t)$ (power) form an admissible policy from initial backlogs $u_0$ when
--
--   1. $0\le R_i(t)\le A_i(t)$ and $P(t)$ is a feasible power vector, for every slot and sample point;
--   2. every $R(t)$ and $P(t)$ is measurable;
--   3. every data queue is mean-rate stable: $\mathbb E\{U_i(t)\}/t\to0$;
--   4. the average power constraint holds:
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\Big\{\sum_i P_i(\tau)\Big\}\le P_{av}.$$
--
--   These are the policies against which "the optimal throughput over all possible policies" is measured.
--
--   **Formalization Note** No causality is required. Mean-rate stability is implied, by Lemma 3.3, by the paper's strong stability (Definition 3.1), so this class contains the strongly stable policies. The $\limsup$ is taken in the extended reals.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115; §6.3.1, p. 113; Definition 3.1 and Lemma 3.3, p. 24

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_queueU

open MeasureTheory Filter Topology

namespace CrossLayerControl.ECCA

/-- **Admissible policies: the class over which the optimal throughput is taken.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115: "Σi r∗i is the optimal throughput over all
possible policies"; §6.3.1, p. 113: "The goal is to maximize throughput subject to an average power
constraint Pav"; flow control "0 ≤ Ri(t) ≤ Ai(t)" (p. 114); the power constraint "Σ_{i=1}^L Pi(t) ≤
Pmax for all t" (p. 113).

On a probability space `(Ω, Pr)` with arrivals `A` and states `S`, the decisions `R` (admitted data)
and `P` (power) form an admissible policy from the initial backlog `u₀` when
1. `0 ≤ Rᵢ(t, ω) ≤ Aᵢ(t, ω)` and `P(t, ω)` is a feasible power vector, for all `t`, `ω`, `i`;
2. every `R t` and `P t` is measurable;
3. every queue is mean-rate stable: `E[Uᵢ(t)]/t → 0`, where `Uᵢ` follows the queue law of §3.1
   under the policy;
4. the average power constraint holds:
   `limsup_{t→∞} (1/t) Σ_{τ<t} E[Σᵢ Pᵢ(τ)] ≤ Pav`.

**Formalization Note.** No causality is required: the class contains every (possibly anticipating)
policy. Stability is mean-rate stability, which by Lemma 3.3 contains the strongly stable policies
of Definition 3.1 (p. 24), the paper's notion; the class is therefore at least as large as the
paper's. The `limsup` is taken in `EReal`, so it is never a junk value; the sequence lies in
`[0, Pmax]` by clause 1. -/
def IsAdmissiblePolicy {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮)
    (R P : ℕ → Ω → Fin L → ℝ) (u₀ : Fin L → ℝ) : Prop :=
  (∀ t ω i, 0 ≤ R t ω i ∧ R t ω i ≤ A t ω i) ∧
  (∀ t ω, IsFeasiblePower M (P t ω)) ∧
  (∀ t, Measurable (R t) ∧ Measurable (P t)) ∧
  (∀ i, Tendsto (fun t : ℕ =>
      (∫ ω, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i ∂Pr) / (t : ℝ))
    atTop (𝓝 0)) ∧
  limsup (fun t : ℕ =>
      (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, ∑ i, P τ ω i ∂Pr : ℝ) : EReal)) atTop ≤
    (M.Pav : EReal)

end CrossLayerControl.ECCA


