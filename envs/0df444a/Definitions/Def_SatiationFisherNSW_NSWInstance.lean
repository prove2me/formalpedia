-- Prove2me | Definitions.Def_SatiationFisherNSW_NSWInstance
-- name    : SatiationFisherNSW_NSWInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:38.091097+00:00
-- url     : https://prove2.me/theorems/adbde523-431b-4122-ac1a-b93989ffbf0d
-- title:
--   Nash social welfare instance with budget-additive valuations and its Fisher market
-- statement:
--   An instance of **Nash social welfare with budget-additive valuations** has a finite set $B$ of agents, a finite set $G$ of indivisible items, values $v_{ij}\ge 0$ and utility caps $c_i>0$. An **integral allocation** gives each item to at most one agent; for an allocation $S=(S_1,\dots,S_n)$ the **budget-additive valuation** of agent $i$ is
--   $$
--   v_i(S)=\min\Bigl(c_i,\ \sum_{j\in S_i}v_{ij}\Bigr),
--   $$
--   and the Nash social welfare is the geometric mean $\bigl(\prod_{i\in B}v_i(S)\bigr)^{1/n}$.
--
--   The **Fisher market of the instance** (§4.1) has values $u_{ij}=\min(v_{ij},c_i)$, budgets $m_i=1$, utility caps $c_i$ and earning caps $d_j=1$. The valuations are **normalized** according to prices $p$ if every buyer $i\notin B_0$ has MBB ratio $\alpha_i=1$ in this market.
--
--   The rounding algorithm of the mission runs on equilibria of this market, and its guarantee compares valuations of integral allocations of the instance.
--
--   **Formalization Note** An integral allocation is a map $G\to$ `Option B`; unassigned items are allowed, which changes no optimum since valuations are monotone. The market uses the truncated values $\min(v_{ij},c_i)$ of Lemma 4.1, so it is the paper's market for every instance; when $v\le c$ it has $u=v$. The paper's assumption $m\ge n$ is not part of the instance. The normalization is a predicate on the instance, as in the paper's "we assume that $v$ and $c$ fulfill these conditions directly"; caps of agents in $B_0$ are not rescaled.
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, §2, "Nash Social Welfare", p.7; §4.1, p.23 (the market, Lemma 4.1); normalization, p.24

import Mathlib
import Definitions.Def_SatiationFisherNSW_FisherMarket
open scoped Classical

namespace SatiationFisherNSW

/-- An instance of the Nash social welfare problem with budget-additive valuations
(Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, §2, "Nash Social Welfare", p.7): a finite set `B`
of agents, a finite set `G` of indivisible items, values `v i j ≥ 0` and utility caps `c i > 0`.

**Formalization Note** p.7 also assumes `m ≥ n` (at least as many items as agents). It is not a
field: the statements that need it carry the money-clearing hypothesis, which implies it, and
the goal theorem holds without it (see `rounding_nsw_approx`). -/
structure NSWInstance (B G : Type*) where
  /-- The value `v_{ij}` of agent `i` for item `j`. -/
  v : B → G → ℝ
  /-- The global utility cap `c_i` of agent `i`. -/
  c : B → ℝ
  v_nonneg : ∀ i j, 0 ≤ v i j
  c_pos : ∀ i, 0 < c i

namespace NSWInstance

variable {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)

/-- The budget-additive valuation `v_i(x^S_i) = min(c_i, Σ_{j∈G} v_{ij} x^S_{ij})` of agent `i`
for an integral allocation `S` (arXiv:1707.04428v3, p.7).

**Formalization Note** An integral allocation is a map `S : G → Option B`: item `j` goes to agent
`i` when `S j = some i`, and to nobody when `S j = none`, so each item goes to at most one agent.
The characteristic vector is `x^S_{ij} = 1` iff `S j = some i`. Allowing unassigned items does
not change the optimum, because valuations are monotone. -/
noncomputable def val (i : B) (S : G → Option B) : ℝ :=
  min (I.c i) (∑ j ∈ Finset.univ.filter (fun j => S j = some i), I.v i j)

/-- The Fisher market `M` of the instance (arXiv:1707.04428v3, §4.1, p.23): buyer `i` has linear
utility with `u_{ij} = v'_{ij} = min(v_{ij}, c_i)`, utility limit `c_i` and budget `m_i = 1`, and
every good has earning limit `d_j = 1`.

**Formalization Note** The paper first replaces `v_{ij}` by `v'_{ij} = min(v_{ij}, c_i)`
(Lemma 4.1) and "henceforth" assumes `v_{ij} ≤ c_i`; the market is built from the truncated
values, so that it is the paper's market for every instance. When `v ≤ c` (the standing
assumption of the milestones), `u = v`. -/
noncomputable def market : FisherMarket B G where
  u i j := min (I.v i j) (I.c i)
  m _ := 1
  c := I.c
  d _ := 1
  u_nonneg i j := le_min (I.v_nonneg i j) (I.c_pos i).le
  m_nonneg _ := zero_le_one
  c_pos := I.c_pos
  d_pos _ := one_pos

/-- The valuations are normalized according to the equilibrium prices `p`
(arXiv:1707.04428v3, p.24): every buyer `i ∈ B \ B₀` has MBB ratio `α_i = 1` in the market of
the instance.

**Formalization Note** The paper reaches this by rescaling `v'_{ij} = v_{ij}/α_i`,
`c'_i = c_i/α_i` for `i ∈ B \ B₀`, which changes neither the equilibrium, the integral optimum,
nor the approximation factor, and then "assume[s] that `v` and `c` fulfill these conditions
directly". Statements about normalized valuations (Lemma 4.3, Theorem 4.1, …) therefore take
this predicate as a hypothesis on the instance; caps of agents in `B₀` are not rescaled. -/
def IsNormalized (p : G → ℝ) : Prop :=
  ∀ i, ¬ I.market.InB0 p i → I.market.mbbRatio p i = 1

end NSWInstance

end SatiationFisherNSW


