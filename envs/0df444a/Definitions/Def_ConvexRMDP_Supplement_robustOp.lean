-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_robustOp
-- name    : ConvexRMDP_Supplement_robustOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:50:15.190922+00:00
-- url     : https://prove2.me/theorems/e48b62a9-7c95-4ea0-b49b-40b89cb963e4
-- title:
--   Robust Bellman operator $T(v)_s = \max_{a}\min_{p\in\mathcal U_{sa}}\{r_{sa}+\gamma p^\top v\}$ (3.8)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust Markov decision process with a nonempty finite action set $\mathcal A$. The **robust Bellman operator** $T : \mathbb R^{\mathcal S} \to \mathbb R^{\mathcal S}$ is
--
--   $$
--   T(v)_s = \max_{a \in \mathcal A} \, \min_{p \in \mathcal U_{sa}} \left\{ r_{sa} + \gamma\, p^\top v \right\}, \qquad s \in \mathcal S .
--   $$
--
--   Its unique fixed point $v^\star$ is the robust value function of the model. Proposition 4.1 and Theorem 4.2 compare $v^\star$ with the fixed point $\tilde v^\star$ of the entropy-regularized operator $\tilde T$.
--
--   **Formalization Note** Since $\gamma > 0$, the inner minimum equals $r_{sa} + \gamma \min_{p \in \mathcal U_{sa}} p^\top v$, and the minimum is the published worst-case term `RMDP.worst` (an infimum over the nonempty set $\mathcal U_{sa} \subseteq \Delta(\mathcal S)$, bounded below), the same term used by the regularized operator `RMDP.regOp`. The maximum over the nonempty finite action set is a finite maximum.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §3.2, display (3.8), p.8

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp

namespace ConvexRMDP

namespace Supplement

variable {S A : Type*} [Fintype S] [Fintype A]

/-- **The (unregularized) sa-rectangular robust Bellman operator** `T : ℝ^S → ℝ^S`
(Grand-Clément & Petrik, arXiv:2209.10187v2, (3.8), p.8):
`T(v)_s = max_{a ∈ A} min_{p ∈ 𝒰_{sa}} {r_{sa} + γ pᵀv}`.

Its fixed point `v⋆` is the robust value function used in Proposition 4.1, items 2–3 and Theorem 4.2.

**Formalization Note.** Since `γ > 0`, `min_{p} {r_{sa} + γ pᵀv} = r_{sa} + γ min_{p} pᵀv`, and the
inner minimum is the published worst-case term `RMDP.worst` (an `sInf` over the nonempty set
`𝒰_{sa} ⊆ Δ(S)`, bounded below, so a genuine infimum, equal to the paper's minimum when attained),
the same term the regularized operator `RMDP.regOp` uses. The maximum over the finite nonempty
action set is `Finset.sup'`. -/
noncomputable def robustOp [Nonempty A] (M : RMDP S A) (v : S → ℝ) : S → ℝ := fun s =>
  Finset.univ.sup' Finset.univ_nonempty (fun a => M.r s a + M.γ * M.worst v s a)

end Supplement

end ConvexRMDP


