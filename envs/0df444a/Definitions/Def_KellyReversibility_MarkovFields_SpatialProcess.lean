-- Prove2me | Definitions.Def_KellyReversibility_MarkovFields_SpatialProcess
-- name    : KellyReversibility_MarkovFields_SpatialProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:49.851881+00:00
-- url     : https://prove2.me/theorems/5bb5d94f-b31a-49c2-b719-1ec8821b1fba
-- title:
--   Spatial processes: conditions (i)–(iii) of §9.2
-- statement:
--   Let $G$ be a graph on a finite set of sites, let site $j$ carry attributes from $\mathcal N_j$, and let $q(\mathbf n,\mathbf n')$ be the transition rates of a Markov process $\mathbf n(t)$ on $\mathcal S=\prod_j\mathcal N_j$. Write $T_j^m\mathbf n$ for $\mathbf n$ with the attribute of site $j$ changed to $m$, and $\partial j$ for the neighbours of $j$. The process is a **spatial process** if
--
--   1. only one component of $\mathbf n$ can change at a time: $q(\mathbf n,\mathbf n')\neq 0$ only if $\mathbf n'$ and $\mathbf n$ differ in at most one site;
--   2. the transition rate $q(\mathbf n, T_j^m\mathbf n)$ does not depend on $\mathbf n_{G-j-\partial j}$: whenever $\mathbf n$ and $\mathbf n'$ agree at $j$ and at every neighbour of $j$,
--   $$q(\mathbf n,T_j^m\mathbf n) = q(\mathbf n',T_j^m\mathbf n');$$
--   3. for any states $\mathbf n$, $T_j^m\mathbf n$ it is possible to reach $T_j^m\mathbf n$ from $\mathbf n$ by a sequence of transitions (jumps of positive rate) which do not alter $\mathbf n_{G-j}$.
--
--   Condition 3 is a strengthened form of irreducibility. These are the processes of Kelly's §9.2, whose reversible members have Markov fields as equilibrium distributions.
--
--   **Formalization Note** The process is represented by its rate function `q`; a "transition" in condition 3 is a pair of states with `0 < q a b`, and the sequence is the reflexive–transitive closure of that relation restricted to jumps that change only site $j$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 189 (PDF 192), §9.2, definition of a spatial process, conditions (i)–(iii)

import Mathlib

namespace KellyReversibility.MarkovFields

/-! Kelly, *Reversibility and Stochastic Networks* (1979), §9.2, p. 189: spatial processes.

States are `n : (j : V) → N j`; `T_j^m n = Function.update n j m`; `q n n'` is the transition
rate from `n` to `n'` of a Markov process on these states. -/

/-- **Spatial process** (p. 189). The transition rates `q` on the state space `∏ⱼ 𝒩ⱼ` define a
spatial process with respect to the graph `G` if

* (i) only one component of `n` can change at a time: `q(n, n') ≠ 0` only if `n'` and `n`
  differ in at most one site;
* (ii) the rate `q(n, T_j^m n)` does not depend on `n_{G-j-∂j}`: if `n` and `n'` agree at `j`
  and at every neighbour of `j`, then `q(n, T_j^m n) = q(n', T_j^m n')`;
* (iii) for any states `n`, `T_j^m n` it is possible to reach `T_j^m n` from `n` by a sequence of
  transitions (jumps of positive rate) which do not alter `n_{G-j}`. -/
def IsSpatialProcess {V : Type*} [DecidableEq V] {N : V → Type*} (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ) : Prop :=
  (∀ n n' : (k : V) → N k, q n n' ≠ 0 → ∃ j : V, ∀ k, k ≠ j → n' k = n k) ∧
  (∀ (j : V) (m : N j) (n n' : (k : V) → N k), n j = n' j →
      (∀ k, G.Adj j k → n k = n' k) →
      q n (Function.update n j m) = q n' (Function.update n' j m)) ∧
  (∀ (j : V) (m : N j) (n : (k : V) → N k),
      Relation.ReflTransGen
        (fun a b : (k : V) → N k => 0 < q a b ∧ ∀ k, k ≠ j → b k = a k)
        n (Function.update n j m))

end KellyReversibility.MarkovFields


