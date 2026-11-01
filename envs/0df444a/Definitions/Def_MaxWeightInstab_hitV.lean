-- Prove2me | Definitions.Def_MaxWeightInstab_hitV
-- name    : MaxWeightInstab_hitV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:10.578153+00:00
-- url     : https://prove2.me/theorems/21a1886e-6178-4f0f-9966-6de2a23bcdf2
-- title:
--   Stopping time $V$ of display (21)
-- statement:
--   $V=\min\{t\ge U:Q_{\mathcal A_0}(t)\le\nu\max_{j=1,\dots,J}Q_{\mathcal A_j}(t)\}\wedge T$: the first time after $U$ at which a queue other than $\mathcal A_0$ might be served at component $\mathcal A$.
--
--   **Formalization Note** $V$ is the first integer time $t\ge U$ with $Q_{\mathcal A_0}(t)\le\nu\max_jQ_{\mathcal A_j}(t)$ or $t\ge T$; it agrees with the paper's $V$ when the first condition occurs before $T$ and is $\max(U,\lceil T\rceil)$ otherwise. Lemma 7 asserts $V<T$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (21), p.8

import Mathlib
import Definitions.Def_MaxWeightInstab_hitU
import Definitions.Def_MaxWeightInstab_maxA

namespace MaxWeightInstab

/-- The stopping time `V = min{t ≥ U : Q_{𝒜₀}(t) ≤ ν max_{j=1,…,J} Q_{𝒜_j}(t)} ∧ T` of (21)
(Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.8).

**Formalization Note.** `V` is the first integer time `t ≥ U` with
`Q_{𝒜₀}(t) ≤ ν max_j Q_{𝒜_j}(t)` or `t ≥ T`. It equals the paper's `V` when the first condition
occurs before `T`, and is `max(U, ⌈T⌉)` otherwise, so that `Q(V)` is defined; Lemma 7 asserts
`V < T`, which rules that case out. -/
noncomputable def hitV {J ν : ℕ} (tr : Trajectory J ν) (T : ℝ) : ℕ := by
  classical
  exact Nat.find (p := fun t => hitU tr T ≤ t ∧
      (tr.Q t (Sum.inl 0) ≤ ν * maxA (tr.Q t) ∨ T ≤ t))
    ⟨max (hitU tr T) ⌈T⌉₊, le_max_left _ _, Or.inr ((Nat.le_ceil T).trans
      (by exact_mod_cast le_max_right _ _))⟩

end MaxWeightInstab


