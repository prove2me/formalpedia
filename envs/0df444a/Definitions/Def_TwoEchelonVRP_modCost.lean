-- Prove2me | Definitions.Def_TwoEchelonVRP_modCost
-- name    : TwoEchelonVRP_modCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:25:40.865163+00:00
-- url     : https://prove2.me/theorems/c0762813-ed07-43ee-bf04-1abe66deace4
-- title:
--   Travel costs modified by the vehicle fixed costs $U_1/2$, $U_2/2$
-- statement:
--   Let $I$ be a 2E-CVRP instance with travel costs $d_{ij}$ and vehicle fixed costs $U_1$ (first level) and $U_2$ (second level). The paper absorbs the fixed costs into the travel costs: for each satellite $k \in N_S$ and each customer $i \in N_C$,
--
--   $$
--   d'_{0k} = d_{0k} + \tfrac12 U_1, \qquad d'_{ki} = d_{ki} + \tfrac12 U_2,
--   $$
--
--   and $d'_{ij} = d_{ij}$ on every other edge. A route leaves its depot (resp. its satellite) and returns to it once, so it is charged the full fixed cost $U_1$ (resp. $U_2$). Every route cost $g_r$ and $c_{kl}$ of the formulations is computed with $d'$.
--
--   **Formalization Note** `modCost I u v` is defined on ordered pairs and adds the same amount in both orientations.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2, unnumbered, p. 299 (modification (i)–(ii) of the travel cost matrix)

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance

namespace TwoEchelonVRP

/-- **Travel costs modified to include the vehicle fixed costs.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §2, unnumbered, p. 299: "To consider vehicle fixed costs
U_1 and U_2, we assume that the travel cost matrix [d_ij] is modified as follows: (i) for each
satellite k ∈ N_S, cost (1/2)U_1 is added to d_0k, and (ii) for each satellite k ∈ N_S and each
customer i ∈ N_C, cost (1/2)U_2 is added to d_ki."

`modCost I u v` is `d_uv + U_1/2` on a depot–satellite pair, `d_uv + U_2/2` on a
satellite–customer pair (in either order), and `d_uv` otherwise. A route leaves and re-enters the
depot (resp. its satellite) once, so it is charged the full fixed cost `U_1` (resp. `U_2`).

**Formalization Note.** These modified costs are the `d_ij` of every route cost `g_r` and `c_kl`
used by formulations F, LF and RF. -/
noncomputable def modCost {ns nc : ℕ} (I : Instance ns nc) : Vertex ns nc → Vertex ns nc → ℝ
  | none, some (Sum.inl k) => I.d none (some (Sum.inl k)) + I.U1 / 2
  | some (Sum.inl k), none => I.d (some (Sum.inl k)) none + I.U1 / 2
  | some (Sum.inl k), some (Sum.inr i) => I.d (some (Sum.inl k)) (some (Sum.inr i)) + I.U2 / 2
  | some (Sum.inr i), some (Sum.inl k) => I.d (some (Sum.inr i)) (some (Sum.inl k)) + I.U2 / 2
  | u, v => I.d u v

end TwoEchelonVRP


