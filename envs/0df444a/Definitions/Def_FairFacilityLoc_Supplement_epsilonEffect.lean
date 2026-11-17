-- Prove2me | Definitions.Def_FairFacilityLoc_Supplement_epsilonEffect
-- name    : FairFacilityLoc_Supplement_epsilonEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:28:11.384459+00:00
-- url     : https://prove2.me/theorems/c93b3ce0-b043-45e5-9106-fc8f9d7b6ec5
-- title:
--   The effect $E_\varepsilon$ and the two-by-two group structure
-- statement:
--   For $\varepsilon\ge0$, define the two-member effect
--
--   $$
--   E_\varepsilon(s,t)=\frac{\min\{s,t\}+\varepsilon\max\{s,t\}}{1+\varepsilon}.
--   $$
--
--   The fixed structure used in Lemma E.2 and Theorem E.3 has four agents partitioned into two groups of two agents, with both groups using this same effect.
--
--   This family makes the farther member contribute only an $\varepsilon$ fraction of the weight of the nearer-member term and supplies the explicit instances in the superlinear impossibility theorem.
--
--   **Formalization Note** The two inputs are indexed by `Fin 2`; the two groups and four agents are also 0-based. The theorem separately assumes $0<\varepsilon<1$ and establishes the required group-effect and superlinearity properties.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma E.2 and Theorem E.3, pp.90–91 (PDF pp.92–93), equation (E.3)

import Mathlib
import Definitions.Def_FairFacilityLoc_Supplement_GeneralGroupStructure

open scoped NNReal

namespace FairFacilityLoc.Supplement

set_option autoImplicit false

/-- The two-member effect
`E_ε(s,t) = (min{s,t} + ε max{s,t}) / (1+ε)` from (E.3)
(Yan–Zhou, manuscript, sha256 642a1268…, Theorem E.3, p.91, PDF p.93). -/
noncomputable def epsilonEffect (ε : ℝ≥0) (u : Fin 2 → ℝ≥0) : ℝ≥0 :=
  (min (u 0) (u 1) + ε * max (u 0) (u 1)) / (1 + ε)

/-- Agent `k` of group `j` in the fixed two-disjoint-two-agent structure of Lemma E.2. -/
def pairAgent (j k : Fin 2) : Fin 4 :=
  ⟨2 * j.val + k.val, by omega⟩

/-- The two agents belonging to group `j` in the fixed structure of Lemma E.2. -/
def twoByTwoGroup (j : Fin 2) : Finset (Fin 4) :=
  Finset.univ.filter fun i => i.val / 2 = j.val

private theorem pairAgent_mem (j k : Fin 2) : pairAgent j k ∈ twoByTwoGroup j := by
  simp [pairAgent, twoByTwoGroup]
  omega

/-- The fixed group structure of Lemma E.2: two disjoint groups of two agents, both using
`E_ε` (Yan–Zhou, manuscript, sha256 642a1268…, Lemma E.2 and Theorem E.3, pp.90–91,
PDF pp.92–93). -/
noncomputable def epsilonTwoByTwo (ε : ℝ≥0) : GeneralGroupStructure 4 2 where
  G := twoByTwoGroup
  E := fun j u => epsilonEffect ε (fun k => u ⟨pairAgent j k, pairAgent_mem j k⟩)
  m_pos := by decide
  nonempty := fun j => ⟨pairAgent j 0, pairAgent_mem j 0⟩
  cover := by
    intro i
    let j : Fin 2 := ⟨i.val / 2, by omega⟩
    refine ⟨j, ?_⟩
    simp [twoByTwoGroup, j]

end FairFacilityLoc.Supplement


