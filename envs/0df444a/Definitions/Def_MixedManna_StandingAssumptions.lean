-- Prove2me | Definitions.Def_MixedManna_StandingAssumptions
-- name    : MixedManna_StandingAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:42.796987+00:00
-- url     : https://prove2.me/theorems/841aff96-e7df-4245-a25a-129e646450eb
-- title:
--   Standing assumptions of §§2, 4: unit supplies, SPLC slopes, desire $>1$, Conditions 1 and 2
-- statement:
--   An instance satisfies the **standing assumptions** when:
--
--   1. endowments are nonnegative and every item has unit supply, $\sum_{i\in N}W_{ij}=1$;
--   2. every $u_{ij}$ has at least one segment and every finite segment has positive length;
--   3. slopes are strictly decreasing in $k$; if $U_{ij1}>0$ the last slope is $\ge 0$, otherwise all slopes are $\le 0$;
--   4. on a bad, every agent's slopes are strictly negative: $D_{ijk}=|U_{ijk}|>0$;
--   5. the **desire** for every good exceeds 1, $\mathrm{desire}_j=\sum_{i\in N}\sum_{k:U_{ijk}>0}L_{ijk}>1$, where the infinite last segment makes the desire infinite;
--   6. **Condition 1**: each agent brings a positive amount of some good and a positive amount of some bad;
--   7. **Condition 2**: the **economy graph** is strongly connected. Its vertices are the agents, with an edge from $a$ to $b$ when $a$ is **non-satiated** for some good $l$ that $b$ brings ($U_{alk}>0$ on the last segment $k$ of $u_{al}$, and $W_{bl}>0$);
--   8. there is at least one agent.
--
--   Every theorem of the mission assumes these conditions; together with the LCP of §4.2.2 they are the setting of Theorem 14.
--
--   **Formalization Note** Item 4 is the paper's working assumption in its proofs (p.24, p.43); the p.14 sentence alone would allow a zero first slope on a bad. Indifference to a bad is then $0<1$ and is not stated. Strong connectivity is the reflexive-transitive closure of the edge relation relating every ordered pair, so a single agent is strongly connected.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, pp.5, 14–16 (unit supply, SPLC slope conditions, desire, Condition 1, Definitions 1–2, Condition 2), with p.24 and p.43 (D_ijk > 0)

import Mathlib
import Definitions.Def_MixedManna_Instance

open scoped ENNReal

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **Non-satiated** (Definition 1, p.16): agent `i` is non-satiated for item `j` if the slope of
the last segment of `u_ij` is positive, `U_ijk > 0` with `k = |u_ij|`. -/
def IsNonSatiated (I : Instance N M) (i : N) (j : M) : Prop := 0 < I.U i j (I.K i j - 1)

/-- **Economy graph** (Definition 2, p.16): a directed edge from agent `a` to agent `b` if `a` is
non-satiated for some good `l` that `b` brings (`W_bl > 0`). -/
def economyEdge (I : Instance N M) (a b : N) : Prop :=
  ∃ l, IsGood I l ∧ IsNonSatiated I a l ∧ 0 < I.W b l

/-- **Desire** for item `j` (p.15): `desire_j = Σ_{i ∈ N} Σ_{k : U_ijk > 0} L_ijk`, with the
infinite length of the last segment (p.14), so the value lies in `[0, ∞]`. -/
noncomputable def desire (I : Instance N M) (j : M) : ℝ≥0∞ :=
  ∑ i, ∑ k ∈ (Finset.range (I.K i j)).filter (fun k => 0 < I.U i j k),
    (if k + 1 < I.K i j then ENNReal.ofReal (I.L i j k) else ⊤)

/-- **Standing assumptions on a mixed-manna instance** (Chaudhury, Garg, McGlaughlin, Mehta,
*Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, pp.5, 14–16, 24, 43):

1. endowments are nonnegative and every item has unit supply, `Σ_i W_ij = 1` (p.5, p.14);
2. every `u_ij` has at least one segment, and every finite segment has positive length (p.14);
3. slopes are strictly decreasing in `k`; if `U_ij1 > 0` the last slope is `≥ 0`, otherwise all
   slopes are `≤ 0` (p.14: "`U_ijk > U_ijk′ ≥ 0` … Otherwise, `0 ≥ U_ijk > U_ijk′`");
4. on a bad, every agent's slopes are strictly negative, `D_ijk = |U_ijk| > 0` (p.24 "Recall that
   `0 < D_ij1 < ⋯`", p.43 "`D_ijk = |U_ijk| > 0`, `∀(i, j, k)`");
5. desire for every good is more than 1 (p.15; indifference to every bad is then `0 < 1`);
6. Condition 1 (p.16): each agent brings a positive amount of some good and of some bad;
7. Condition 2 (p.16): the economy graph is strongly connected;
8. there is at least one agent.

**Formalization Note** Item 4 is the paper's working assumption in §5 and App. C; with a zero
first slope on a bad, `(14d)` fails at the starting point `S₀`. Strong connectivity is
`Relation.ReflTransGen economyEdge a b` for all `a, b`, so one agent is strongly connected. -/
structure StandingAssumptions (I : Instance N M) : Prop where
  nonempty_agents : Nonempty N
  W_nonneg : ∀ i j, 0 ≤ I.W i j
  unit_supply : ∀ j, ∑ i, I.W i j = 1
  K_pos : ∀ i j, 1 ≤ I.K i j
  L_pos : ∀ i j k, k + 1 < I.K i j → 0 < I.L i j k
  U_strictAnti : ∀ i j k k', k < k' → k' < I.K i j → I.U i j k' < I.U i j k
  U_last_nonneg : ∀ i j, 0 < I.U i j 0 → 0 ≤ I.U i j (I.K i j - 1)
  bad_slope_neg : ∀ j, ¬ IsGood I j → ∀ i, I.U i j 0 < 0
  desire_gt_one : ∀ j, IsGood I j → 1 < desire I j
  condition1 : ∀ i, (∃ j, IsGood I j ∧ 0 < I.W i j) ∧ (∃ j, ¬ IsGood I j ∧ 0 < I.W i j)
  condition2 : ∀ a b, Relation.ReflTransGen (economyEdge I) a b

end MixedManna


