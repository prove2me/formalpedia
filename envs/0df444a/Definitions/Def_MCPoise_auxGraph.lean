-- Prove2me | Definitions.Def_MCPoise_auxGraph
-- name    : MCPoise_auxGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:19.151187+00:00
-- url     : https://prove2.me/theorems/a339ba4a-c30e-4be3-aed8-a172cdd2185c
-- title:
--   The auxiliary bipartite graph of a Junction-LP solution
-- statement:
--   Let $D'$ be the set of demands with $\sum_j \lambda_{i,j} \ge 1/4$. First round $\lambda_{i,j}$ down to $0$ whenever $\lambda_{i,j} \le 1/(8M)$. The pair $(i, j)$ is in the bucket $B_\ell$ if $\lambda_{i,j} \in (1/2^{\ell+1}, 1/2^\ell]$.
--
--   The **auxiliary graph** $\mathcal A$ has a pair vertex $z_i$ for each pair of $D'$, a vertex $r_{j,\ell}$ for each root and bucket, and an edge $(z_i, r_{j,\ell})$ of weight $1/2^{\ell+1}$ for each $(i, j) \in B_\ell$.
--
--   Each edge stands for a fractional flow in $G$ of the same value, and the assignment step routes along it.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.1, p.11; p.10

import Mathlib
import Definitions.Def_MCPoise_AVert

namespace MCPoise

/-- `λ_{i,j}` after the round-down of p.11: "We first round λ_{i,j} down to 0 for all λ_{i,j} ≤ 1/(8M)", with `M = k`. -/
noncomputable def roundDown {k : ℕ} (lam : Fin k → Fin k → ℝ) (i j : Fin k) : ℝ :=
  open scoped Classical in if lam i j ≤ 1 / (8 * (k : ℝ)) then 0 else lam i j

/-- `D′`: the demand indices with `Σ_{j∈[M]} λ_{i,j} ≥ 1/4` (p.10). -/
noncomputable def Dprime {k : ℕ} (lam : Fin k → Fin k → ℝ) : Finset (Fin k) :=
  open scoped Classical in Finset.univ.filter fun i => 1 / 4 ≤ ∑ j, lam i j

/-- The edge relation of the auxiliary graph: `i ∈ D′` and `(i, j)` is in the bucket `B_ℓ`, that is,
`λ_{i,j} ∈ (1/2^{ℓ+1}, 1/2^ℓ]` after the round-down (p.11). -/
def auxRel {k : ℕ} (lam : Fin k → Fin k → ℝ) : AVert k → AVert k → Prop
  | Sum.inl i, Sum.inr c =>
      i ∈ Dprime lam ∧ 1 / 2 ^ (c.2.val + 1) < roundDown lam i c.1 ∧
        roundDown lam i c.1 ≤ 1 / 2 ^ c.2.val
  | _, _ => False

/-- **The auxiliary bipartite graph `A`.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.1, p.11: "We first round λ_{i,j} down to 0 for all λ_{i,j} ≤ 1/(8M)." "(i, j) is in bucket B_ℓ if
λ_{i,j} ∈ (1/2^{ℓ+1}, 1/2^ℓ], for ℓ = 0, . . . , log M + 2." "For each bucket B_ℓ and each (i, j) ∈ B_ℓ, we add an
edge e = (z_i, r_{j,ℓ}) of weight w(e) = 1/2^{ℓ+1}."

**Formalization Note.** This is the construction from `λ`, not an arbitrary bipartite graph. `M = k`, with `r_j = s_j`. -/
def auxGraph {k : ℕ} (lam : Fin k → Fin k → ℝ) : SimpleGraph (AVert k) :=
  SimpleGraph.fromRel (auxRel lam)

/-- The vertex set of `A`: the pair vertices of `D′` and every root copy (p.11). -/
def auxVerts {k : ℕ} (lam : Fin k → Fin k → ℝ) : Set (AVert k) :=
  {v | ∀ i, v = Sum.inl i → i ∈ Dprime lam}

/-- The auxiliary graph `A` with its vertex set, as the starting piece of Algorithm 1. -/
def auxInit {k : ℕ} (lam : Fin k → Fin k → ℝ) : (auxGraph lam).Subgraph :=
  (⊤ : (auxGraph lam).Subgraph).induce (auxVerts lam)

end MCPoise


