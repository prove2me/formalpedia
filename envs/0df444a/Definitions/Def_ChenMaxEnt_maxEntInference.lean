-- Prove2me | Definitions.Def_ChenMaxEnt_maxEntInference
-- name    : ChenMaxEnt_maxEntInference
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:31.196069+00:00
-- url     : https://prove2.me/theorems/a9b215b1-c713-4b61-b05e-88d4280a0bf9
-- title:
--   The maximum entropy inference $\rho^*(\alpha) = \operatorname{argmax}_{\rho\in L(\alpha)} S(\rho)$
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be observables on $\mathcal H = \mathbb C^n$ and $\alpha \in D_F$. The **maximum entropy inference** for the measurement results $\alpha$ is the state of largest von Neumann entropy among all states returning $\alpha$:
--
--   $$
--   \rho^*(\alpha) = \operatorname*{argmax}_{\rho \in L(\alpha)} S(\rho), \qquad S(\rho) = -\operatorname{tr}(\rho \log \rho).
--   $$
--
--   The milestone on eq. (2) asserts that this maximizer exists and is unique for every $\alpha \in D_F$. The central question of the paper is whether $\alpha \mapsto \rho^*(\alpha)$ is continuous on $D_F$.
--
--   **Formalization Note** The entropy is the published `QAlgorithms.vnEntropy`, with the logarithm to base 2; the base does not change the maximizer. The definition picks some maximizer when one exists (by choice); on $D_F$ the maximizer is unique, so the value is the paper's $\rho^*(\alpha)$. When no maximizer exists (exactly when $\alpha \notin D_F$, where $L(\alpha) = \emptyset$) the value is the junk matrix $0$, which is why continuity of $\rho^*$ is always taken within $D_F$.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §2.1, eq. (2), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ChenMaxEnt_linearFamily

namespace ChenMaxEnt

open Classical in
/-- Chen et al., arXiv:1406.5046v2, §2.1, eq. (2), p.5: "for any given measurement results α,
there is a unique state ρ∗ ∈ L(α), given by ρ∗(α) = argmax_{ρ ∈ L(α)} S(ρ), (2) where S(ρ) is the
von Neumann entropy of ρ. We call ρ∗(α) the maximum entropy inference for the given measurement
results α."

`maxEntInference F α` is a state of `L(α)` of largest von Neumann entropy, when one exists.

**Formalization Note.** `S` is the published `QAlgorithms.vnEntropy` (logarithm to base 2; the
base does not change an argmax). The value is chosen among the maximizers; the milestone
`ChenMaxEnt.maxEnt_exists_unique` (eq. (2)) asserts that for every `α ∈ D_F` the maximizer exists
and is unique, so on `D_F` the choice is irrelevant and `maxEntInference F α` is the paper's
`ρ*(α)`. Off `D_F` (where `L(α) = ∅`) the value is the junk `0`, which is why continuity
statements about `ρ*` are taken within `D_F` (`ChenMaxEnt.jointRange`). -/
noncomputable def maxEntInference {n ι : Type*} [Fintype n] [DecidableEq n]
    (F : ι → Matrix n n ℂ) (α : ι → ℝ) : Matrix n n ℂ :=
  if h : ∃ ρ ∈ linearFamily F α, ∀ σ ∈ linearFamily F α,
      QAlgorithms.vnEntropy σ ≤ QAlgorithms.vnEntropy ρ then h.choose else 0

end ChenMaxEnt


