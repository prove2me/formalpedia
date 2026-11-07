-- Prove2me | Definitions.Def_MeanBudgetXC_hostGraph
-- name    : MeanBudgetXC_hostGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:40.103867+00:00
-- url     : https://prove2.me/theorems/0ca0ed4b-a1de-4b54-b3b3-bf2bc686061b
-- title:
--   The host graph $Q$
-- statement:
--   The **host graph** $Q$ is built from two groups of $n_0$ Boolean source variables, with interaction graph $K_{n_0,n_0}$ and $m=n_0^2$ source edges, as follows. Each of the $2n_0$ variables $i$ has a private path $v_{i,0}-a_i-b_i-v_{i,1}$. Every left/right source edge $ij$ has all four interaction edges $v_{i,s}v_{j,t}$ with $s,t\in\{0,1\}$. The rest of the graph is $\ell$ disjoint copies of a padding graph $T$, $c$ disjoint marker edges and $n_{\mathrm{iso}}$ isolated vertices.
--
--   **Formalization Note** The graph is the symmetrization of a one-way relation `hostRel`, recorded in the same module together with decidability of adjacency.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19

import Mathlib
import Definitions.Def_MeanBudgetXC_HostV

namespace MeanBudgetXC

/-- One orientation of the edges of the host graph (Section 4.3, p.19): the path edges
`(s,i,k) — (s,i,k+1)`; the interaction edges `v_{i,s} v_{j,t}` between every left path endpoint
and every right path endpoint (all four for every left/right source pair `ij`, interaction graph
`K_{n₀,n₀}`); the edges of each padding copy of `T`; and the marker edges `(m,0) — (m,1)`. -/
def hostRel (n₀ t ℓ c niso : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    HostV n₀ t ℓ c niso → HostV n₀ t ℓ c niso → Bool
  | .inl (s, i, k), .inl (s', i', k') =>
      decide ((s = s' ∧ i = i' ∧ k.val + 1 = k'.val) ∨
        (s = 0 ∧ s' = 1 ∧ (k = 0 ∨ k = 3) ∧ (k' = 0 ∨ k' = 3)))
  | .inr (.inl (p, u)), .inr (.inl (p', u')) => decide (p = p' ∧ T.Adj u u')
  | .inr (.inr (.inl (m, b))), .inr (.inr (.inl (m', b'))) => decide (m = m' ∧ b = 0 ∧ b' = 1)
  | _, _ => false

/-- The **host graph** `Q` of Section 4.3 (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, p.19): two groups of `n₀` source variables, a private
path `v_{i,0} — a_i — b_i — v_{i,1}` for each of the `2 n₀` variables, all four interaction edges
`v_{i,s} v_{j,t}` (`s, t ∈ {0,1}`) for every left/right source pair, `ℓ` disjoint copies of the
padding graph `T`, `c` disjoint marker edges and `n_iso` isolated vertices. -/
def hostGraph (n₀ t ℓ c niso : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    SimpleGraph (HostV n₀ t ℓ c niso) :=
  SimpleGraph.fromRel fun x y => hostRel n₀ t ℓ c niso T x y = true

instance hostGraph.decidableRel (n₀ t ℓ c niso : ℕ) (T : SimpleGraph (Fin t))
    [DecidableRel T.Adj] : DecidableRel (hostGraph n₀ t ℓ c niso T).Adj :=
  fun x y => inferInstanceAs
    (Decidable (x ≠ y ∧ (hostRel n₀ t ℓ c niso T x y = true ∨ hostRel n₀ t ℓ c niso T y x = true)))

end MeanBudgetXC


