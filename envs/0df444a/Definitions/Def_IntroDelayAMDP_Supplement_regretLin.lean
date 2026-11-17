-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_regretLin
-- name    : IntroDelayAMDP_Supplement_regretLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:46:01.790333+00:00
-- url     : https://prove2.me/theorems/b78a2b50-af47-47b1-8482-db19a70b2b0b
-- title:
--   Regret against a comparator policy on a general state space
-- statement:
--   For the policies $\pi_k$ played in the episodes $k=1,\dots,K$, the losses $\ell_k$ and a comparator policy $\pi$,
--   $$R_K(\pi)=\sum_{k=1}^K\bigl(V^{\pi_k}_k(s_0)-V^{\pi}_k(s_0)\bigr),$$
--   with $V$ the V-function of `vLin`. Bounding $R_K(\pi)$ for every measurable policy on one event is the same as bounding the regret (14) against the optimal policy in hindsight.
--
--
--   **Formalization Note** Episodes are $0$-based.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (14), p.13

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_vLin

namespace IntroDelayAMDP.Supplement

open MeasureTheory ProbabilityTheory

/-- **Regret against a comparator policy, general state space** (Eq. (14), printed p.13, PDF p.15, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "`R_K ≜ ∑_{k=1}^K V^{π_k}_k(s₀) − ∑_{k=1}^K V^{π⋆}_k(s₀)`".
For the policies `πs k` played in the 0-based episodes `k < K`, the losses `ℓ k` and a comparator `π`,
`regretLin L P ℓ πs π K = ∑_{k<K} (V^{πs k}_k(s₀) − V^π_k(s₀))` with `V` of `vLin`.

**Formalization Note.** As in the published `IntroDelayAMDP.regret`, the comparator is an argument and the
theorems bound the regret against every (measurable) policy on one event, which is the bound against
`π⋆`. -/
noncomputable def regretLin {X A : Type} [MeasurableSpace X] [Fintype A] {H : ℕ} (L : LayeredSpace X H)
    (P : A → Kernel X X) (ℓ : ℕ → X → A → ℝ) (πs : ℕ → X → A → ℝ) (π : X → A → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (vLin L P (ℓ k) (πs k) H L.s0 - vLin L P (ℓ k) π H L.s0)

end IntroDelayAMDP.Supplement


