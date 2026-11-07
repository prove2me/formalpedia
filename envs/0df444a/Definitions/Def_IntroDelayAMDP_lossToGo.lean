-- Prove2me | Definitions.Def_IntroDelayAMDP_lossToGo
-- name    : IntroDelayAMDP_lossToGo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:28.920296+00:00
-- url     : https://prove2.me/theorems/2b5dc942-38d6-4416-b7d3-104d50509e96
-- title:
--   Loss from step $h$ to the end of the episode
-- statement:
--   $L_{k,h}=\sum_{h'=h}^{H-1}\ell_k(s_{k,h'},a_{k,h'})$, the loss suffered along the trajectory from step $h$ to the end of the episode.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12

import Mathlib

namespace IntroDelayAMDP

/-- **Loss from step `h` to the end of the episode** `L_{k,h}` (Section 2.1, p.12). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed
p.12: "We use `L_{k,h} ≜ ∑_{h′=h}^{H−1} ℓ_k(s_{k,h′}, a_{k,h′})` to denote the loss suffered from
step `h` to the end of episode `k`."

For the loss function `ℓk` of the episode and its trajectory `τ h' = (s_{k,h'}, a_{k,h'})`,
`lossToGo ℓk H τ h = ∑_{h ≤ h' < H} ℓk(τ h')`. -/
noncomputable def lossToGo {St A : Type} (ℓk : St → A → ℝ) (H : ℕ) (τ : ℕ → St × A) (h : ℕ) : ℝ :=
  ∑ h' ∈ Finset.Ico h H, ℓk (τ h').1 (τ h').2

end IntroDelayAMDP


