-- Prove2me | Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
-- name    : ProcessingNetworks_LyapunovCriteria_LipschitzOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:54:25.378841+00:00
-- url     : https://prove2.me/theorems/bae01ecc-338a-47e3-86e9-bec0e9a6d8b0
-- title:
--   Definition 8.1 — Lipschitz and globally Lipschitz continuity
-- statement:
--   **Definition 8.1.** A function $g : \mathbb{R}^d \to \mathbb{R}^m$ is **Lipschitz** if for
--   every bounded set $B \subset \mathbb{R}^d$ there is a constant $\kappa(B) > 0$ with
--   $|g(x)-g(y)| \le \kappa(B)|x-y|$ for all $x,y \in B$. It is **globally Lipschitz** if
--   $\kappa(B)$ can be chosen independent of $B$. The same definitions apply with
--   $\mathbb{R}^d$ replaced by $\mathbb{R}^d_+$.
--
--   This mission reuses Mathlib's own Lipschitz substrate (`LipschitzOnWith`) rather than
--   restating the $\varepsilon$-$\delta$ inequality from scratch: `IsLipschitzOn g s` says $g$ is
--   `LipschitzOnWith` some constant on `s ∩ B` for every bounded `B`; `IsGloballyLipschitzOn g s`
--   says a single constant works on all of `s`.
--
--   **Formalization note.** The two notions are genuinely different — Lemma 8.3's conclusion is
--   the *global* one, while Lemma 8.2's hypotheses are the (weaker) bounded-set-wise one — and are
--   kept as two separate definitions rather than merged, per this mission's own `BRIEF.md` pitfall
--   warning. Both are stated generically over any two (pseudo)metric spaces `α`, `β`, so the same
--   definition covers $g:\mathbb{R}^d\to\mathbb{R}^m$, $g:\mathbb{R}^m\to\mathbb{R}$ (Lemma 8.2),
--   and the $\mathbb{R}^d_+$ variant (via `s = {z | ∀ i, 0 ≤ z i}`) uniformly.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 135, Definition 8.1

import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

open scoped NNReal

/-- Definition 8.1 (Lipschitz continuity), Dai & Harrison p. 135 (PDF p. 151): `g` is Lipschitz
on `s` if, for every bounded set `B`, there is a constant `κ(B) > 0` such that
`|g(x) - g(y)| ≤ κ(B)|x-y|` for `x, y ∈ s ∩ B` — i.e. `g` is `LipschitzOnWith` some constant on
every bounded subset of `s`. Stated for arbitrary (pseudo)metric domain/codomain types so that it
covers both `g : ℝ^d → ℝ^m` and `g : ℝ^m → ℝ` (Lemma 8.2) with the same definition, matching the
book's own remark that "the same definition applies when `ℝ^d` is replaced by `ℝ^d_+`" (take
`s = Set.univ` for the unrestricted domain, `s = {z | ∀ i, 0 ≤ z i}` for `ℝ^d_+`). -/
def IsLipschitzOn {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (g : α → β)
    (s : Set α) : Prop :=
  ∀ B : Set α, Bornology.IsBounded B → ∃ K : ℝ≥0, LipschitzOnWith K g (s ∩ B)

/-- Definition 8.1's globally Lipschitz continuity: the constant `κ(B)` can be taken independent
of `B`, i.e. `g` is `LipschitzOnWith` a single constant on the whole of `s`. -/
def IsGloballyLipschitzOn {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (g : α → β)
    (s : Set α) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K g s

end ProcessingNetworks.LyapunovCriteria


