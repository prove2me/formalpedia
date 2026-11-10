-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_FTRLTrace
-- name    : FlowOptimalSeparators_MinorFree_FTRLTrace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:07:11.953112+00:00
-- url     : https://prove2.me/theorems/5f7862dc-4d97-4ac9-a343-34b37db15584
-- title:
--   Algorithm 2 connector transitions and actual-prefix weight vectors
-- statement:
--   For the preceding connectors $C_1,\ldots,C_{t-1}$, write $q_t=\sum_{i<t}p_{C_i}$. The round weight is
--   $$w_t(v)=1+\frac{n\deg(v)}{2m}+4D\left(\mu q_t(v)+\iota\sum_{u\in N(v)}q_t(u)\right).$$
--   A connector-producing transition uses a cluster for the ceiling weights, a root absent from all preceding roots, and a shortest-path parent tree spanning that cluster. Its terminal count is the stated ceiling reading, with the root excluded whenever possible. A prefix satisfies every preceding source transition; it is not an arbitrary load vector. The connector indicator ranges over the entire graph's connector family.
--
--   This transition relation describes the choices in Algorithm 2 without assuming objective progress or weight-norm bounds. The purely mathematical round lemmas require $m>0$ because the source fraction is otherwise undefined. The goal includes the preprocessing cases for which no FTRL round is needed.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 14–17, Eq. (18); Algorithm 2; Lemmas 2 and 4

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Connectors

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

noncomputable def prefixLoad {n : ℕ} {G : Graph n} (Cs : List (WideConnector G))
    (v : Fin n) : ℝ := (Cs.map (fun C => load C v)).sum

noncomputable def roundWeight {n : ℕ} (G : Graph n) (D μ ι : ℝ)
    (Cs : List (WideConnector G)) (v : Fin n) : ℝ := by
  classical
  exact 1 + n * ((Finset.univ.filter (G.Adj v)).card : ℝ) / (2 * edgeCount G) +
    4 * D * (μ * prefixLoad Cs v +
      ι * ∑ u ∈ Finset.univ.filter (G.Adj v), prefixLoad Cs u)

noncomputable def ceilingWeight {n : ℕ} (G : Graph n) (D μ ι : ℝ)
    (Cs : List (WideConnector G)) (v : Fin n) : ℝ :=
  (⌈roundWeight G D μ ι Cs v⌉ : ℤ)

/-- Exactly the connector-producing branch of Algorithm 2. K is the returned cluster, the
root is fresh, and the chosen parent tree minimizes full ceiling-weight root paths inside K.
No collision, congestion, progress, feasibility, or weight-norm bound occurs in this definition. -/
def FTRLRound {n : ℕ} (G : Graph n) (D μ ι : ℝ)
    (Cs : List (WideConnector G)) (C : WideConnector G) : Prop :=
  ∃ K : Finset (Fin n), Cluster G (ceilingWeight G D μ ι Cs) D K ∧
    C.val.vertices = K ∧ C.val.root ∉ Cs.map (fun C' => C'.val.root) ∧
    ((3 * n + 3) / 4 ≤ (K.erase C.val.root).card → C.val.root ∉ C.val.terminals) ∧
    ∀ v ∈ K, ∀ P ∈ simplePaths G C.val.root v, (∀ x ∈ P, x ∈ K) →
      vertexWeight (ceilingWeight G D μ ι Cs) (ancestorPath C.val n v) ≤
        vertexWeight (ceilingWeight G D μ ι Cs) P

/-- Every prefix is produced by successive source transitions, not arbitrary load vectors. -/
def IsFTRLPrefix {n : ℕ} (G : Graph n) (D μ ι : ℝ)
    (Cs : List (WideConnector G)) : Prop :=
  ∀ (t : ℕ) (C : WideConnector G), Cs[t]? = some C → FTRLRound G D μ ι (Cs.take t) C

noncomputable def connectorIndicator {n : ℕ} {G : Graph n}
    (Cs : List (WideConnector G)) (C : WideConnector G) : ℝ :=
  by classical exact if C ∈ Cs then 1 else 0

end FlowOptimalSeparators.MinorFree


