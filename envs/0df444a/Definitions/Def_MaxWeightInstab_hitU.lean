-- Prove2me | Definitions.Def_MaxWeightInstab_hitU
-- name    : MaxWeightInstab_hitU
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:51.69563+00:00
-- url     : https://prove2.me/theorems/619de4c9-1691-4c3a-91eb-0fa60ca46fc9
-- title:
--   Stopping time $U$ of display (21)
-- statement:
--   $U=\min\{t\ge0:Q^\Sigma_{\mathcal B}(t)\le\nu^2\}\wedge T$: the first time component $\mathcal B$ is almost empty.
--
--   **Formalization Note** $U$ is the first integer time $t$ with $Q^\Sigma_{\mathcal B}(t)\le\nu^2$ or $t\ge T$. It agrees with the paper's $U$ when component $\mathcal B$ reaches $\nu^2$ before $T$, and is $\lceil T\rceil$ otherwise, so that $Q(U)$ is defined; Lemma 2 asserts $U<T$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (21), p.8

import Mathlib
import Definitions.Def_MaxWeightInstab_Trajectory
import Definitions.Def_MaxWeightInstab_totalB

namespace MaxWeightInstab

/-- The stopping time `U = min{t ≥ 0 : Q^Σ_ℬ(t) ≤ ν²} ∧ T` of (21) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.8).

**Formalization Note.** `U` is the first integer time `t` with `Q^Σ_ℬ(t) ≤ ν²` or `t ≥ T`. It
equals the paper's `U` whenever component `ℬ` reaches `ν²` before `T`; otherwise it is `⌈T⌉`
instead of `T`, so that `Q(U)` is defined. Every statement about `U` asserts `U < T`, which rules
that case out. -/
noncomputable def hitU {J ν : ℕ} (tr : Trajectory J ν) (T : ℝ) : ℕ := by
  classical
  exact Nat.find (p := fun t => totalB (tr.Q t) ≤ ν ^ 2 ∨ T ≤ t)
    ⟨⌈T⌉₊, Or.inr (Nat.le_ceil T)⟩

end MaxWeightInstab


