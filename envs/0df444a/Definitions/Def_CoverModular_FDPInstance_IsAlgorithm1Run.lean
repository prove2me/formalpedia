-- Prove2me | Definitions.Def_CoverModular_FDPInstance_IsAlgorithm1Run
-- name    : CoverModular_FDPInstance_IsAlgorithm1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:51.006295+00:00
-- url     : https://prove2.me/theorems/47f78161-32f9-4ebf-9fd6-ed27f0f254e2
-- title:
--   A run $\mathcal A_0,\dots,\mathcal A_K$ of Algorithm 1 (greedy-type heuristics)
-- statement:
--   A sequence of structures $\mathcal A_0,\mathcal A_1,\dots,\mathcal A_K$ is a **run of Algorithm 1** with budget $K$ and constant $P$ if
--
--   1. $\mathcal A_0=\emptyset$;
--   2. for each $t=1,\dots,K$: with $\mathcal E_{ij}(\mathcal A_{t-1})$ and $\mathcal E_{\max}(\mathcal A_{t-1})$ computed by (11) from an optimal LP solution for $\mathcal A_{t-1}$ in every scenario, some arc $(i_t,j_t)\in\mathcal F$ satisfies $F(\mathcal A_{t-1}\cup\{(i_t,j_t)\})\ge\mathcal E_{\max}(\mathcal A_{t-1})+F(\mathcal A_{t-1})$, and $\mathcal A_t=\mathcal A_{t-1}\cup\{(i_t,j_t)\}$.
--
--   Every heuristic that fits this description, among them the natural greedy method, produces such a run.
--
--   **Formalization Note** Step $t+1$ (for $t<K$) builds $\mathcal A_{t+1}$ from $\mathcal A_t$. The optimal solutions used to compute $\mathcal E$ are existentially quantified separately at every step, so a run may use any optimal solution of each LP. The arc in line 4 ranges over all of $\mathcal F$, including arcs already in $\mathcal A_t$ ("Choose any arc"). Values beyond index $K$ are unconstrained.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, Algorithm 1, p.15

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_FDPInstance_F
import Definitions.Def_CoverModular_FDPInstance_Emax

namespace CoverModular

namespace FDPInstance

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- `A 0, A 1, …, A K` is a run of **Algorithm 1** ("A Class of Greedy-Type Heuristics",
DeValve, Pekeč, Wei, SSRN 3844987, §3.2, p.15) with budget `K` and constant `P`:

1. `𝒜_0 = ∅`;
2. for `t = 1, …, K`: compute `ℰ_ij(𝒜_{t−1})` and `ℰ_max(𝒜_{t−1})` (11) from an optimal
   solution of the LP for `𝒜_{t−1}` in every scenario; choose any arc `(i_t, j_t)` with
   `F(𝒜_{t−1} ∪ {(i_t, j_t)}) ≥ ℰ_max(𝒜_{t−1}) + F(𝒜_{t−1})`; set
   `𝒜_t = 𝒜_{t−1} ∪ {(i_t, j_t)}`.

**Formalization Note** The iteration index is shifted: step `t + 1` (for `t < K`) builds
`A (t + 1)` from `A t`. The optimal solutions used to compute `ℰ` at each step are
existentially quantified per step, so a run may use any optimal solution of each LP (the paper
says "an optimal solution"). The chosen arc ranges over all of `𝓕`, including arcs already in
`A t` ("Choose any arc"). Values of `A` beyond `K` are unconstrained. -/
def IsAlgorithm1Run (inst : FDPInstance I J Ω) (P : ℝ) (K : ℕ) (A : ℕ → Finset (I × J)) :
    Prop :=
  A 0 = ∅ ∧ ∀ t < K, ∃ x : Ω → I → J → ℝ,
    (∀ ω, IsOptimal (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p (A t) (x ω)) ∧
    ∃ a : I × J, A (t + 1) = insert a (A t) ∧
      inst.Emax P x (A t) + inst.F (A t) ≤ inst.F (A (t + 1))

end FDPInstance

end CoverModular


