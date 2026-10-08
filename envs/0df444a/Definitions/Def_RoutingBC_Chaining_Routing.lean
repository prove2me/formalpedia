-- Prove2me | Definitions.Def_RoutingBC_Chaining_Routing
-- name    : RoutingBC_Chaining_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:05.296014+00:00
-- url     : https://prove2.me/theorems/2bd835ee-e103-40a1-80e4-7b8d6152dd0d
-- title:
--   Loop-free routing scheme R(s,u,v,t), routes, pairwise dependency δ_{s,t}(v), sequence dependency δ̃_{s,t}(S), target dependencies (7), sequence RBC (4)
-- statement:
--   This file sets up the routing model of Dolev, Elovici and Puzis and the dependency quantities built on it.
--
--   **Network and routing scheme.** Let $V$ be a finite set of nodes. A **routing scheme** is a function $R : V\times V\times V\times V\to\mathbb R$, where $R(s,u,v,t)$ is the probability that node $u$ forwards to node $v$ a packet with source address $s$ and target address $t$. The standing assumptions of the paper are bundled as follows:
--
--   1. $R(s,u,v,t)\ge 0$ for all $s,u,v,t$;
--   2. every node $u\ne t$ forwards a packet targeted at $t$ with total probability one: $\sum_{v\in V}R(s,u,v,t)=1$;
--   3. the target forwards nothing: $R(s,t,v,t)=0$ (the packet leaves the network at $t$);
--   4. the scheme is **loop-free**: for every pair $(s,t)$ the directed graph with an arc $a\to b$ whenever $R(s,a,b,t)>0$ has no directed cycle (in particular $R(s,u,u,t)=0$).
--
--   The scheme is **source-oblivious** if $R(s,u,v,t)=R(s',u,v,t)$ for all $s,s',u,v,t$; the paper writes $R(\oslash,u,v,t)$.
--
--   **Routes.** A **route** from $s$ to $t$ is a finite sequence $p=(c_0,\dots,c_m)$ with $c_0=s$, $c_m=t$, $t\notin\{c_0,\dots,c_{m-1}\}$, and $R(s,c_r,c_{r+1},t)>0$ for every $r<m$. Since routing decisions are independent, the probability that a packet from $s$ to $t$ follows $p$ is
--   $$\Pr(p)=\prod_{r=0}^{m-1}R(s,c_r,c_{r+1},t).$$
--   Under loop-freeness every route visits each node at most once, so the routes from $s$ to $t$ form a finite set $\mathcal P_{s,t}$. For $s=t$ the only route is $(t)$, with probability $1$.
--
--   **Dependencies.** For nodes $s,t,v$ and a finite sequence $S=(s_1,\dots,s_k)$ of nodes:
--
--   - the **pairwise dependency** $\delta_{s,t}(v)$, the probability that a packet from $s$ to $t$ passes through $v$, is $\sum\{\Pr(p) : p\in\mathcal P_{s,t},\ v\in p\}$;
--   - the **sequence dependency** $\tilde\delta_{s,t}(S)$, the probability that the packet passes through $s_1$, then $s_2$, …, then $s_k$, is $\sum\{\Pr(p) : p\in\mathcal P_{s,t},\ \hat S \text{ is a subsequence of } p\}$, where $\hat S$ is $S$ with consecutive repetitions collapsed to one occurrence;
--   - given a traffic matrix $T : V\times V\to\mathbb R$ ($T(s,t)$ is the number of packets sent from $s$ to $t$), the **target dependency** is $\delta_{\bullet,t}(v)=\sum_{s\in V}\delta_{s,t}(v)\,T(s,t)$ (Eq. (7)), and on a sequence $\tilde\delta_{\bullet,t}(S)=\sum_{s\in V}\tilde\delta_{s,t}(S)\,T(s,t)$;
--   - given sampling rates $\rho : V\to\mathbb R$, the **routing betweenness centrality of the sequence** is (Eq. (4))
--   $$\tilde\delta_{\bullet,\bullet}(S_\rho)=\prod_{r\in S}\rho_r\cdot\sum_{s,t\in V}\tilde\delta_{s,t}(S)\,T(s,t).$$
--
--   These objects are the vocabulary of every statement of the mission: dependency chaining, its product form, the target dependency chain and the sequence RBC formula behind Algorithm 6.
--
--   **Formalization Note.** The paper never writes assumption 2; it is implicit in "destined to leave the network at target node $t$" and in $\delta_{s,t}(t)=1$ (p. 6), and without it Lemma 1 fails. Assumption 3 is likewise implicit. The paper's convention $R(\oslash,v,v,\oslash)=1$ (p. 5) is not adopted, since it contradicts loop-freeness; the collapsing of consecutive repetitions in $S$ reproduces its only use, $\tilde\delta_{s,t}((u,v,v,v,w))=\tilde\delta_{s,t}((u,v,w))$ (p. 8). The paper's probabilities are informal; here they are sums of route probabilities over a finite set, which is exactly the probability of the corresponding event when decisions are independent. Sequences are Lean lists (0-based), and the routes are drawn from the repetition-free lists of nodes. $T$ is an arbitrary real matrix and $\rho$ an arbitrary real function in this file; bounds are stated where the theorems need them.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Section 3 (p. 5), Section 4.1 (p. 6), Section 4.2 and Eq. (4) (p. 8), Section 5.1 and Eq. (7) (p. 11), Section 5.2 (p. 12)

import Mathlib

namespace RoutingBC.Chaining

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Standing hypotheses on a routing scheme `R s u v t` (Dolev–Elovici–Puzis, §3, p. 5):
`R s u v t` is the probability that node `u` forwards to node `v` a packet with source `s` and
target `t`. Probabilities are nonnegative; every node other than the target forwards with total
probability `1`; the target forwards nothing (the packet leaves the network there); and the
routing graph `{(a, b) | R s a b t > 0}` of every source–target pair is acyclic (loop-free). -/
structure IsRoutingScheme (R : V → V → V → V → ℝ) : Prop where
  nonneg : ∀ s u v t, 0 ≤ R s u v t
  forward_one : ∀ s u t, u ≠ t → ∑ v, R s u v t = 1
  target_silent : ∀ s v t, R s t v t = 0
  loopFree : ∀ s t u, ¬ Relation.TransGen (fun a b => 0 < R s a b t) u u

/-- Source-oblivious routing (§5, p. 11): the forwarding probabilities do not depend on the
source address, `R(∅, u, v, t)`. -/
def IsSourceOblivious (R : V → V → V → V → ℝ) : Prop :=
  ∀ s s' u v t, R s u v t = R s' u v t

/-- `p` is a route from `s` to `t` under `R`: it starts at `s`, ends at `t`, visits `t` only at
its end, and every hop `a → b` along it has positive forwarding probability `R s a b t`. -/
def IsRoute (R : V → V → V → V → ℝ) (s t : V) (p : List V) : Prop :=
  p.head? = some s ∧ p.getLast? = some t ∧ t ∉ p.dropLast ∧
    p.IsChain (fun a b => 0 < R s a b t)

/-- The probability that a packet from `s` to `t` follows the route `p`: the product of the
forwarding probabilities of its hops (routing decisions are independent, p. 5). -/
noncomputable def routeProb (R : V → V → V → V → ℝ) (s t : V) (p : List V) : ℝ :=
  ((p.zip p.tail).map (fun ab => R s ab.1 ab.2 t)).prod

/-- The finite set of simple routes from `s` to `t` (repetition-free lists of nodes). Under a
loop-free scheme every route is repetition-free, so this is the set of all routes. -/
noncomputable def routes (R : V → V → V → V → ℝ) (s t : V) : Finset (List V) :=
  ((Finset.univ : Finset {l : List V // l.Nodup}).map
      ⟨Subtype.val, Subtype.val_injective⟩).filter (fun p => IsRoute R s t p)

/-- Pairwise dependency `δ_{s,t}(v)` (§4.1, p. 6): the probability that a packet from `s` to `t`
passes through `v`, i.e. the total probability of the routes from `s` to `t` that contain `v`. -/
noncomputable def delta (R : V → V → V → V → ℝ) (s t v : V) : ℝ :=
  ∑ p ∈ (routes R s t).filter (fun p => v ∈ p), routeProb R s t p

/-- Sequence dependency `δ̃_{s,t}(S)` (§4.2, p. 8): the probability that a packet from `s` to `t`
passes through all nodes of `S = (s_1, …, s_k)`, first `s_1`, then `s_2`, …, then `s_k`. It is the
total probability of the routes that contain `S` as a (not necessarily contiguous) sublist, after
consecutive repetitions in `S` are collapsed to one occurrence. -/
noncomputable def seqDelta (R : V → V → V → V → ℝ) (s t : V) (S : List V) : ℝ :=
  ∑ p ∈ (routes R s t).filter (fun p => (S.destutter (· ≠ ·)).Sublist p), routeProb R s t p

/-- Target dependency `δ_{•,t}(v) = Σ_{s ∈ V} δ_{s,t}(v) · T(s, t)` (Eq. (7), p. 11). -/
noncomputable def targetDelta (R : V → V → V → V → ℝ) (T : V → V → ℝ) (t v : V) : ℝ :=
  ∑ s, delta R s t v * T s t

/-- Target dependency on a sequence `δ̃_{•,t}(S) = Σ_{s ∈ V} δ̃_{s,t}(S) · T(s, t)` (§5.2, p. 12). -/
noncomputable def targetSeqDelta (R : V → V → V → V → ℝ) (T : V → V → ℝ) (t : V)
    (S : List V) : ℝ :=
  ∑ s, seqDelta R s t S * T s t

/-- Routing betweenness centrality of a sequence with sampling rates `ρ` (Eq. (4), p. 8):
`δ̃_{•,•}(S_ρ) = ∏_{r ∈ S} ρ_r · Σ_{s,t ∈ V} δ̃_{s,t}(S) · T(s, t)`. -/
noncomputable def seqRBC (R : V → V → V → V → ℝ) (T : V → V → ℝ) (ρ : V → ℝ)
    (S : List V) : ℝ :=
  (S.map ρ).prod * ∑ s, ∑ t, seqDelta R s t S * T s t

end RoutingBC.Chaining


