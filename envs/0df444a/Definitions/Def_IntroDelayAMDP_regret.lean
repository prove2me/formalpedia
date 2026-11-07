-- Prove2me | Definitions.Def_IntroDelayAMDP_regret
-- name    : IntroDelayAMDP_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:09.979195+00:00
-- url     : https://prove2.me/theorems/c2b0c14f-daf7-4a40-b616-0f061a7e6ebc
-- title:
--   Regret against a comparator, Eq. (14)
-- statement:
--   For policies $\pi_k$ played in the episodes, losses $\ell_k$ and a comparator policy $\pi$,
--   $$R_K(\pi)=\sum_{k}\bigl(V^{\pi_k}_k(s_0)-V^{\pi}_k(s_0)\bigr).$$
--   The paper's $R_K$ is this quantity for the optimal policy in hindsight.
--
--   **Formalization Note** Episodes are 0-based, $k<K$. The comparator is an argument. The main theorem bounds the regret against every policy on one event, which is the same as bounding it against the optimal policy in hindsight, because that policy is deterministic for oblivious losses.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (14), p.13; Definition 1.3, p.4

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_vFun

namespace IntroDelayAMDP

/-- **Regret against a comparator policy** (Eq. (14), p.13; Definition 1.3, p.4). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed
p.13: "`R_K ≜ ∑_{k=1}^K V^{π_k}_k(s₀) − ∑_{k=1}^K V^{π⋆}_k(s₀)`".

For the policies `πs k` played in the episodes `k = 0, …, K − 1` (the paper's episodes
`1, …, K`), the losses `ℓ k` and a comparator policy `π`,
`regret L P ℓ πs π K = ∑_{k<K} (V^{πs k}_k(s₀) − V^π_k(s₀))`, where `V_k` is the V-function of
Eq. (12) for the loss `ℓ k` under the true transition `P`.

**Formalization Note.** Episodes are 0-based. The paper's regret uses the optimal policy in
hindsight `π⋆`; this definition takes the comparator as an argument, and the main theorem bounds
the regret against every policy on one event, which is the same as bounding it against `π⋆`
(`π⋆` is deterministic, the losses being oblivious). -/
noncomputable def regret {St A : Type} [Fintype St] [Fintype A] {H : ℕ} (L : LayeredSpace St H)
    (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (πs : ℕ → St → A → ℝ) (π : St → A → ℝ)
    (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (vFun L P (ℓ k) (πs k) L.s0 - vFun L P (ℓ k) π L.s0)

end IntroDelayAMDP


