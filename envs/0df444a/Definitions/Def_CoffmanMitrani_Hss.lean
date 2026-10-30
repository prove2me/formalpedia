-- Prove2me | Definitions.Def_CoffmanMitrani_Hss
-- name    : CoffmanMitrani_Hss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:20:08.815261+00:00
-- url     : https://prove2.me/theorems/4fbe4510-90bb-4082-977f-3994cbfacea4
-- title:
--   The polyhedron $H^{**}$
-- statement:
--   $H^{**}$ is the set of vectors $W \in \mathbb R^M$ that satisfy the conservation law
--   $$\sum_{i=1}^M \rho_i W_i = \frac{V}{1-\rho} \qquad (1)$$
--   and the $2^M - 2$ inequalities
--   $$\sum_{i\in g} \rho_i W_i \ge \frac{\sum_{i\in g} \rho_i/\mu_i}{1-\sum_{i\in g}\rho_i} \qquad (4)$$
--   for all proper nonempty subsets $g$ of the classes.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 817, Lemma 2

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_rho
import Definitions.Def_CoffmanMitrani_Data_V
import Definitions.Def_CoffmanMitrani_Data_loadBound

namespace CoffmanMitrani

/-- **The polyhedron `H**` of Lemma 2.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 817, Lemma 2: "Let H** be the set of performance vectors which satisfy the
conservation law (1) and the 2^M − 2 inequalities (4), where g runs through all the proper nonempty
subsets of {1, 2, ···, M}."

`W ∈ Hss D` when `Σ_i ρi Wi = V/(1 − ρ)` (the conservation law (1)) and, for every nonempty proper
subset `g` of the classes, `Σ_{i∈g} ρi Wi ≥ (Σ_{i∈g} ρi/μi)/(1 − Σ_{i∈g} ρi)` (inequality (4)). -/
def Hss (D : Data) : Set (Fin D.M → ℝ) :=
  {W | ∑ i, D.rho i * W i = D.V / (1 - ∑ i, D.rho i) ∧
    ∀ g : Finset (Fin D.M), g.Nonempty → g ≠ Finset.univ →
      D.loadBound g ≤ ∑ i ∈ g, D.rho i * W i}

end CoffmanMitrani


