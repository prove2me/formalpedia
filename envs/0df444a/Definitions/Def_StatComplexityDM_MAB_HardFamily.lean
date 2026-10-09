-- Prove2me | Definitions.Def_StatComplexityDM_MAB_HardFamily
-- name    : StatComplexityDM_MAB_HardFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:00.021978+00:00
-- url     : https://prove2.me/theorems/ff6ff175-1280-426d-aef5-cf5464f1e2ce
-- title:
--   Definition 5.1, p. 31 — (α, β, δ)-family of models
-- statement:
--   Let $\Pi$ be a finite decision space, $\mathcal{Y}$ a finite outcome space with reward map $r$, and $M \mapsto \pi_M$ an argmax selector. A model class $\mathcal{M}$, a reference model $\overline{M} \in \mathcal{M}$, and a collection $\{M_1, \dots, M_N\} \subseteq \mathcal{M}$ of models with $N \ge 2$ form an **$(\alpha, \beta, \delta)$-family** if:
--
--   1. **Regret property.** There exist functions $u_i : \Pi \to [0,1]$ with $\sum_{i} u_i(\pi) \le N/2$ for every $\pi$, such that for all $i$ and $\pi$
--   $$
--   f^{M_i}(\pi_{M_i}) - f^{M_i}(\pi) \ge \alpha \cdot (1 - u_i(\pi)).
--   $$
--   2. **Information property.** There exist functions $v_i : \Pi \to [0,1]$ with $\sum_i v_i(\pi) \le 1$ for every $\pi$, such that for all $i$ and $\pi$
--   $$
--   D^2_{\mathrm{H}}\bigl(M_i(\pi), \overline{M}(\pi)\bigr) \le \beta \cdot v_i(\pi) + \delta.
--   $$
--
--   Here $D^2_{\mathrm{H}}(P,Q) = \sum_y (\sqrt{P(y)} - \sqrt{Q(y)})^2$ is the squared Hellinger distance (5). Informally, in such a family a single decision can have low regret, or reveal much information, on at most a few of the models; this is the template for lower bounds on the Decision-Estimation Coefficient used throughout §§5–7 of the paper.
--
--   **Formalization Note** The collection is an indexed family $i \in \{0, \dots, N-1\}$. The predicate includes membership of the reference and each family member in the model class, requires that the class contain only probability models, and requires the selector to maximize mean reward on that class. Finite alphabets, as throughout this series.
-- source:
--   arXiv:2112.13487v3, Definition 5.1, p. 31

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- An `(α, β, δ)`-family of models (arXiv:2112.13487v3, Definition 5.1, p. 31): a reference
model `mbar ∈ 𝓜` and a collection `fam 0, …, fam (N-1) ∈ 𝓜` with `N ≥ 2` such that
1. (regret property) there are `u_i : Π → [0, 1]` with `∑_i u_i(π) ≤ N/2` for every `π` and
   `f^{M_i}(π_{M_i}) − f^{M_i}(π) ≥ α · (1 − u_i(π))`;
2. (information property) there are `v_i : Π → [0, 1]` with `∑_i v_i(π) ≤ 1` for every `π` and
   `D²_H(M_i(π), M̄(π)) ≤ β · v_i(π) + δ`.
Here `π_{M_i}` is `piStar (fam i)` and `f^M(π) = fM rew M π`. -/
def IsHardFamily {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) (mbar : S → Y → ℝ) {N : ℕ} (fam : Fin N → S → Y → ℝ)
    (α β δ : ℝ) : Prop :=
  (∀ m ∈ 𝓜, StatComplexityDM.LowerBound.IsModel m) ∧
  (∀ m ∈ 𝓜, ∀ π, fM rew m π ≤ fM rew m (piStar m)) ∧
  mbar ∈ 𝓜 ∧ (∀ i, fam i ∈ 𝓜) ∧ 2 ≤ N ∧
  (∃ u : Fin N → S → ℝ, (∀ i π, 0 ≤ u i π ∧ u i π ≤ 1) ∧ (∀ π, ∑ i, u i π ≤ (N : ℝ) / 2) ∧
    ∀ i π, α * (1 - u i π) ≤ fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) ∧
  (∃ v : Fin N → S → ℝ, (∀ i π, 0 ≤ v i π ∧ v i π ≤ 1) ∧ (∀ π, ∑ i, v i π ≤ 1) ∧
    ∀ i π, hellingerSq (fam i π) (mbar π) ≤ β * v i π + δ)

end StatComplexityDM.MAB


