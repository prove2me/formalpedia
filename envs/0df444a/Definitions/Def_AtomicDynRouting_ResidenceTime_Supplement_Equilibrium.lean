-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium
-- name    : AtomicDynRouting_ResidenceTime_Supplement_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:32:01.821395+00:00
-- url     : https://prove2.me/theorems/61fa81db-8156-418c-9765-a4521031c9d5
-- title:
--   Definitions 4–6, pp. 13–14 — Nash and UFR equilibria, preemption, batches, populations
-- statement:
--   Let $p$ be a path profile of an ADR game and write $(P'_i,p_{-i})$ for the profile in which agent $i$ switches to the $o$-$d$ path $P'_i$.
--
--   1. **Nash equilibrium** (Definition 4): $t^d_i(p)\le t^d_i(P'_i,p_{-i})$ for every agent $i$ and every $P'_i\in\mathcal P$.
--   2. **UFR equilibrium** (Definition 5): for every agent $i$ and every vertex $v$ on his route there is no $P'_i\in\mathcal P$ with $t^v_i(P'_i,p_{-i})<t^v_i(p)$.
--   3. The **equilibria** studied in §§5–6 are the UFR equilibria for $\Gamma_1$, $\Gamma_2$ and the Nash equilibria for $\Gamma_3$.
--   4. **Preemption** (Definition 6): agent $i$ preempts agent $j$ at the vertex $v$ if both pass $v$ and either $t^v_i<t^v_j$, or $t^v_i=t^v_j$ and: for $\Gamma_1,\Gamma_2$, $i$ has higher priority than $j$; for $\Gamma_3$, $i$ comes from an incoming edge of $v$ of higher priority than $j$'s when $v\neq o$, and $i$ has higher original priority when $v=o$.
--   5. A **batch** is the set of agents who reach $d$ at the same time; the agents of the batches up to time $T$ are those with $t^d_i(p)\le T$.
--   6. The **population** of $G$ at time $t$ is the number of agents inside $G$ (entered by $t$, not yet exited), and a set of edges **accommodates** an agent at time $t$ if the agent is in the buffer of one of these edges.
--
--   **Formalization Note** The incoming edge of a route at $v$ is any edge of the route with head $v$; in an acyclic network there is at most one. Counts are `Set.ncard`; the sets counted contain only agents who have entered by time $t$, finitely many under the standing assumptions.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), pp. 13–15 (PDF 14–16), Definitions 4, 5, 6, batches (p. 14), accommodation (§6.1, p. 15)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Game

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

variable {ι V E : Type}

open Classical in
/-- `(P', p_{-i})`: the profile `p` with agent `i`'s route replaced by `P'`. -/
noncomputable def deviate (p : ι → List E) (i : ι) (P' : List E) : ι → List E :=
  Function.update p i P'

namespace Game

variable (G : Game ι V E)

/-- Definition 4 (NE, p. 13): `p` is a path profile and no agent can reach `d` earlier by a
unilateral deviation to another `o`-`d` path: `t^d_i(p) ≤ t^d_i(P'_i, p_{-i})` for every agent `i`
and every `P'_i ∈ 𝒫`. -/
def IsNE (p : ι → List E) : Prop :=
  G.IsProfile p ∧ ∀ i P', G.IsODPath P' → G.arrTime p i G.d ≤ G.arrTime (deviate p i P') i G.d

/-- Definition 5 (UFR equilibrium, p. 13): `p` is a path profile and for every agent `i` and every
vertex `v` on his route under `p` there is no `P'_i ∈ 𝒫` with `t^v_i(P'_i, p_{-i}) < t^v_i(p)`. -/
def IsUFR (p : ι → List E) : Prop :=
  G.IsProfile p ∧ ∀ i v, G.passes p i v → ∀ P', G.IsODPath P' →
    ¬ G.arrTime (deviate p i P') i v < G.arrTime p i v

/-- The equilibria studied in §5–6 (p. 13 and p. 15): a UFR equilibrium for `Γ1` and `Γ2`, a Nash
equilibrium for `Γ3`. -/
def IsEquilibrium (p : ι → List E) : Prop :=
  match G.rule with
  | .r1 _ => G.IsUFR p
  | .r2 _ => G.IsUFR p
  | .r3 _ _ => G.IsNE p

/-- Agent `i`'s route under `p` enters the vertex `v` through the edge `e` (`e` is on the route and
`head e = v`). In an acyclic network there is at most one such edge. -/
def entersVia (p : ι → List E) (i : ι) (v : V) (e : E) : Prop :=
  e ∈ p i ∧ G.N.head e = v

/-- Definition 6 (preemption, p. 14): under the routing `p`, agent `i` preempts agent `j` at the
vertex `v` if both pass `v` and either (i) `i` reaches `v` earlier than `j`, or (ii) they reach `v`
at the same time and
* for `Γ1` and `Γ2`, `i` has a higher priority than `j`;
* for `Γ3`, when `v ≠ o`, `i` comes from an incoming edge of `v` of higher priority than `j`'s, and
  when `v = o`, `i` has a higher original priority than `j`. -/
def preempts (p : ι → List E) (i j : ι) (v : V) : Prop :=
  G.passes p i v ∧ G.passes p j v ∧
    (G.arrTime p i v < G.arrTime p j v ∨
      (G.arrTime p i v = G.arrTime p j v ∧
        match G.rule with
        | .r1 hp => hp i j
        | .r2 hp => hp i j
        | .r3 ep op => (v ≠ G.o ∧ ∃ ei ej, G.entersVia p i v ei ∧ G.entersVia p j v ej ∧ ep v ei ej) ∨
            (v = G.o ∧ op i j)))

/-- The agents of the batches up to time `T` under `p` (p. 14): those who reach the destination `d`
(and exit `G`) no later than `T`. A batch is the set of agents reaching `d` at one time; for `T` a
batch time this is that batch together with all earlier batches. -/
def batchesUpTo (p : ι → List E) (T : ℕ) : Set ι :=
  {i | G.arrTime p i G.d ≤ (T : ℕ∞)}

/-- The number of agents inside `G` at the integer time `t` under the profile `p` (§2.5: agent `i`
is inside during `[entry, exit)`). -/
noncomputable def population (p : ι → List E) (t : ℕ) : ℕ :=
  {i | (G.run p).inside i t}.ncard

/-- The number of agents a set `S` of edges (a subnetwork) accommodates at the integer time `t`
under `p` (§6.1, p. 15): the agents inside the buffer of some edge of `S` at time `t`. -/
noncomputable def accommodates (p : ι → List E) (S : Set E) (t : ℕ) : ℕ :=
  {i | ∃ j e, (G.run p).inBuf i j t ∧ (p i)[j]? = some e ∧ e ∈ S}.ncard

end Game

end AtomicDynRouting.ResidenceTime.Supplement


