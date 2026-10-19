-- Prove2me | Definitions.Def_AtomicDynFlow_IDNE_Model
-- name    : AtomicDynFlow_IDNE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:46.21735+00:00
-- url     : https://prove2.me/theorems/9f4ee0fd-a7bf-40a6-a7de-fd6525250d1f
-- title:
--   §3–§4, pp. 9–11 — edge-priority deterministic-queuing network: instance, strategy sets, queue dynamics (R0)–(R4), arrival times
-- statement:
--   This file fixes the flow model of Cao, Chen, Chen and Wang (§3) and the strategy sets of the normal-form game $\Gamma^N$ (§4).
--
--   **Network.** $G=(V,E)$ is a finite acyclic directed multigraph (parallel edges allowed); edge $e$ goes from its tail $u_e$ to its head. A distinguished vertex $d$ is the destination, and every vertex has a path to $d$. Every edge has unit capacity and unit length. At each vertex $v$ a complete priority order $\prec_v$ is fixed on the edges entering $v$; it is given as the list of these edges from the highest priority to the lowest.
--
--   **Agents.** Time is $0,1,2,\dots$. At time $0$ each edge $e$ carries a (possibly empty) initial ranked queue $Q^0_e$, listed head first. At each time $r\ge 1$ and vertex $v$ a finite ordered set $\Delta_{r,v}$ of agents enters at origin $v$, listed from the highest original rank to the lowest. The agent set $\Delta$ is the disjoint union of all these lists; it may be infinite. The *starting vertex* of $i\in Q^0_e$ is $u_e$, reached at time $0$; that of $i\in\Delta_{r,v}$ is $v$, reached at time $r$.
--
--   **Strategies.** The strategy set $\mathcal P_i$ of $i\in Q^0_e$ is the set of paths to $d$ whose first edge is $e$; that of $i\in\Delta_{r,v}$ is the set of $v$-$d$ paths (for $v=d$, only the empty path).
--
--   **Dynamics (edge-priority DQ rule).** Fix a *partial* path profile $\pi$: each agent either takes a path or is absent from the network. At every time $s$ only the head of the queue at an edge $e$ leaves; it traverses $e$ in one unit and exits at time $s+1$, immediately entering the next edge of its path (or leaving at $d$). Agents entering $e$ are ranked by the rules (R0)–(R4), checked in this order:
--
--   1. (R0) agents of $Q^0_e$ keep their initial order;
--   2. (R1) an agent entering $e$ earlier ranks higher;
--   3. (R2) agents entering at the same time through different edges into $u_e$ are ranked by $\prec_{u_e}$;
--   4. (R3) an agent whose origin is $u_e$ ranks above one entering through an edge into $u_e$ at the same time;
--   5. (R4) agents with the common origin $u_e$ are ranked by their original ranks.
--
--   **Arrival times.** $t^v_i(\pi)$ is the time agent $i$ reaches vertex $v$ under $\pi$: the time at his starting vertex, or $s+1$ if he leaves the queue of an edge of his path into $v$ at time $s$. It is $\infty$ if $i$ is absent or never reaches $v$.
--
--   The model is shared by every statement of the mission: Definitions 1 and 2, the selection procedure of §4.1, Lemma EC.2 and Theorem 1.
--
--   **Formalization Note.** `Instance V E A` bundles the data with its standing hypotheses: a height function strictly increasing along edges (acyclicity), reachability of $d$, the incoming-edge lists `inc v` (highest priority first, each a duplicate-free list of exactly the edges into $v$), no inflow at time $0$, duplicate-free source lists, and that every agent lies in exactly one source list. `queue π s e` is the ranked queue at $e$ just after the entries at time $s$; the queue at $s+1$ is the old queue minus its head, then the origin entrants of $\Delta_{s+1,u_e}$ choosing $e$ (rank order), then the agents served at the edges into $u_e$ at time $s$ whose next edge is $e$, by decreasing priority. `arrival` takes values in `ℕ∞`, with `⊤` for $\infty$ (p. ec4). The starting-vertex times $0$ and $r$ are those of Algorithm 1, Step 2 (p. 20). Partial profiles are `A → Option (List E)`, `none` meaning absent.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), pp. 9–11 (PDF 10–12), §3 (Unit Assumption, ranking rules (R0)–(R4)), §4 (strategy sets); p. 20 (PDF 21), Algorithm 1 Step 2; p. ec4 (PDF 36)

import Mathlib

namespace AtomicDynFlow.IDNE

/-- `PathTo tail head d v P`: the edge list `P` is a directed `v`-`d` path, i.e. `P = [e₁, …, eₘ]`
with `tail e₁ = v`, `head eᵢ = tail eᵢ₊₁` and `head eₘ = d`. The empty list is the (only) `d`-`d`
path. In an acyclic graph every such walk is a simple path. -/
def PathTo {V E : Type} (tail head : E → V) (d : V) : V → List E → Prop
  | v, [] => v = d
  | v, e :: P => tail e = v ∧ PathTo tail head d (head e) P

/-- The ranked list of agents attached to a source: `Sum.inl e` is the initial queue `Q⁰_e`,
`Sum.inr (r, v)` is the inflow `Δ_{r,v}`. -/
def srcList {V E A : Type} (Q0 : E → List A) (inflow : ℕ → V → List A) : E ⊕ (ℕ × V) → List A
  | Sum.inl e => Q0 e
  | Sum.inr rv => inflow rv.1 rv.2

/-- An instance of the atomic dynamic flow game `Γᴺ` (Cao–Chen–Chen–Wang, §3, pp. 9–10).

* `V`, `E` are finite (vertices, edges of a directed multigraph: parallel edges allowed, edge `e`
  goes from `tail e` to `head e`); `A` is the set `Δ` of agents and may be infinite.
* every edge has unit capacity and unit length (built into the dynamics `Instance.queue`).
* `inc v` is the complete priority order `≺_v` on the edges incoming to `v`, listed from the
  **highest** priority to the lowest: `e₁ ≺_v e₂` iff `e₁` occurs before `e₂` in `inc v`.
* `Q0 e` is the initial ranked queue `Q⁰_e` at edge `e` at time `0`, listed **head first**.
* `inflow r v` is the ordered set `Δ_{r,v}` of agents entering at vertex `v` at time `r ≥ 1`,
  listed from the **highest original rank** to the lowest; there is no inflow at time `0`.
* every agent lies in exactly one of these lists, exactly once. -/
structure Instance (V E A : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] where
  tail : E → V
  head : E → V
  /-- the destination -/
  d : V
  /-- acyclicity: a height function strictly increasing along every edge -/
  acyclic : ∃ h : V → ℕ, ∀ e, h (tail e) < h (head e)
  /-- every vertex has a path to `d` -/
  reach : ∀ v, ∃ P, PathTo tail head d v P
  /-- incoming edges of each vertex, highest priority first -/
  inc : V → List E
  inc_mem : ∀ v e, e ∈ inc v ↔ head e = v
  inc_nodup : ∀ v, (inc v).Nodup
  /-- initial ranked queues, head first -/
  Q0 : E → List A
  /-- `inflow r v = Δ_{r,v}`, highest original rank first -/
  inflow : ℕ → V → List A
  inflow_zero : ∀ v, inflow 0 v = []
  nodup : ∀ s, (srcList Q0 inflow s).Nodup
  partition : ∀ a : A, ∃! s, a ∈ srcList Q0 inflow s

namespace Instance

variable {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Instance V E A)

/-- `P` is a `v`-`d` path of `G`. -/
def IsPathTo (v : V) (P : List E) : Prop := PathTo G.tail G.head G.d v P

/-- The strategy set `𝒫_a` (§4, p. 11): for `a ∈ Q⁰_e`, the paths whose first edge is `e` and
which end at `d`; for `a ∈ Δ_{r,v}`, the `v`-`d` paths. -/
def IsStrategy (a : A) (P : List E) : Prop :=
  (∃ e, a ∈ G.Q0 e ∧ P.head? = some e ∧ G.IsPathTo (G.tail e) P) ∨
  (∃ r v, a ∈ G.inflow r v ∧ G.IsPathTo v P)

/-- `StartsAt a v t`: agent `a`'s starting vertex is `v` and he is there at time `t`: `t = 0` and
`v = tail e` for `a ∈ Q⁰_e`, or `a ∈ Δ_{t,v}` (Algorithm 1, Step 2, p. 20). -/
def StartsAt (a : A) (v : V) (t : ℕ) : Prop :=
  (∃ e, a ∈ G.Q0 e ∧ G.tail e = v ∧ t = 0) ∨ a ∈ G.inflow t v

/-- `v` is a vertex of agent `a`'s path `P`: his starting vertex, or the head of an edge of `P`. -/
def OnPath (a : A) (P : List E) (v : V) : Prop :=
  (∃ t, G.StartsAt a v t) ∨ ∃ e ∈ P, G.head e = v

/-- The edge following `e` on the edge list `P` (`none` if `e` is last or not on `P`). -/
def nextAfter (e : E) : List E → Option E
  | [] => none
  | x :: rest => if x = e then rest.head? else nextAfter e rest

/-- The ranked queue at every edge just after the entries at time `s`, under the partial path
profile `π` (`π a = none`: agent `a` is absent from the network). The head of `queue π s e` leaves
`e` at time `s` and exits at its head at time `s + 1` (Unit Assumption). The queue at time `s + 1`
is, in this order:
1. the agents already queuing at `e` (everyone but the head served at time `s`): (R0), (R1);
2. the present agents of `Δ_{s+1, tail e}` whose path starts with `e`, in original-rank order:
   origin entrants rank above through-traffic (R3) and among themselves by original rank (R4);
3. for each edge `e'` into `tail e`, from the highest priority to the lowest, the agent served at
   `e'` at time `s` if his next edge is `e`: (R2). -/
def queue (π : A → Option (List E)) : ℕ → E → List A
  | 0 => fun e => (G.Q0 e).filter (fun a => (π a).isSome)
  | s + 1 => fun e =>
      (queue π s e).tail ++
      (G.inflow (s + 1) (G.tail e)).filter
        (fun a => match π a with
          | some P => decide (P.head? = some e)
          | none => false) ++
      (G.inc (G.tail e)).filterMap
        (fun e' => match queue π s e' with
          | a :: _ => if nextAfter e' ((π a).getD []) = some e then some a else none
          | [] => none)

/-- The arrival time `t^v_i(π)` of agent `i` at vertex `v` under the partial profile `π`: the time
he is at his starting vertex, or `s + 1` if he heads the queue of an edge `e` of his path into `v`
at time `s`. It is `⊤` (`∞`, p. ec4) if `i` is absent or never reaches `v`. -/
noncomputable def arrival (π : A → Option (List E)) (i : A) (v : V) : ℕ∞ :=
  sInf {t : ℕ∞ | (π i).isSome = true ∧
    ((∃ n : ℕ, G.StartsAt i v n ∧ t = (n : ℕ∞)) ∨
     ∃ (e : E) (s : ℕ), e ∈ (π i).getD [] ∧ G.head e = v ∧
       (G.queue π s e).head? = some i ∧ t = ((s + 1 : ℕ) : ℕ∞))}

end Instance

end AtomicDynFlow.IDNE


