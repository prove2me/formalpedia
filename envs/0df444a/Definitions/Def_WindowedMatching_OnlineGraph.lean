-- Prove2me | Definitions.Def_WindowedMatching_OnlineGraph
-- name    : WindowedMatching_OnlineGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:16.220767+00:00
-- url     : https://prove2.me/theorems/c1d5b0a5-143e-4d73-8ebe-6d73fc2ab414
-- title:
--   §2 — the online graph with deadline $d$, its weights and the benchmark $\mathrm{OFF}$
-- statement:
--   This module fixes the model of §2 (p.4) in the Adversarial Order setting $\sigma(i)=i$.
--
--   1. **The online graph.** For a deadline $d$, the graph $G_{d,\sigma}$ on $n$ vertices has an edge between distinct vertices $i$ and $j$ if and only if
--   $$|i-j|\le d.$$
--   2. **Online weights.** The weight of a pair $(i,j)$ as the algorithm sees it is $v_{ij}$ if $(i,j)$ is an edge of $G_{d,\sigma}$, and $0$ otherwise.
--   3. **The benchmark.** $\mathrm{OFF}$ is the maximum weight of a matching of $G_{d,\sigma}$.
--
--   These are the input and the benchmark of Theorem 3.3.
--
--   **Formalization Note** Vertices are `Fin n`, 0-based: vertex $k$ is the paper's vertex $k+1$. Weights are a function on `Sym2 (Fin n)`, so they are symmetric by construction, and the diagonal entries are never read because the graph has no loops. The inequality is compared in $\mathbb Z$. In the Adversarial Order setting $\sigma$ is fixed, so the expectation in the paper's "expected maximum-weight of a matching" is trivial. The maximum is the published finite maximum `ProphetMatchingEFGT.optWeight`.
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, §2, p.4; "seller s_k does not have any edges", p.6; OFF, p.7

import Definitions.Def_ProphetMatchingEFGT_MatchingModel

namespace WindowedMatching

/-! # The online graph with deadline `d` (Ashlagi et al., arXiv:1808.03526v1, §2, p.4)

The Adversarial Order setting `σ(i) = i` on `n` vertices, the graph `G_{d,σ}`, its edge weights as
the algorithm sees them, and the offline benchmark `OFF`.

**Formalization Note.** Vertices are `Fin n`, 0-based: vertex `k` is the paper's vertex `k + 1`,
arrives in period `k` and becomes critical in period `k + d`. Weights are `v : Sym2 (Fin n) → ℝ`,
so `v_ij = v_ji` holds by construction; non-negativity is a hypothesis of each theorem. `Sym2`
also has diagonal entries `s(i, i)`, which no definition below reads, because `windowGraph` has no
loops. -/

/-- The online graph with deadline `d`, `G_{d,σ}` with `σ(i) = i` (arXiv:1808.03526v1, §2, p.4):
the edge between `i` and `j` exists if and only if `|σ(i) − σ(j)| ≤ d`.

**Formalization Note.** A Mathlib `SimpleGraph`, so `i ≠ j` is part of adjacency: edges are between
two vertices. The inequality is `≤ d`, compared in `ℤ`, so no truncated subtraction occurs. -/
def windowGraph (n d : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ |(i : ℤ) - (j : ℤ)| ≤ (d : ℤ)
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [abs_sub_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n d : ℕ) : DecidableRel (windowGraph n d).Adj := fun i j => by
  unfold windowGraph
  exact inferInstanceAs (Decidable (i ≠ j ∧ |(i : ℤ) - (j : ℤ)| ≤ (d : ℤ)))

/-- The weight of the pair `(i, j)` in the online graph: `v_ij` if it is an edge of `G_{d,σ}`, and
`0` otherwise (arXiv:1808.03526v1, §2, p.4; p.6, "seller s_k does not have any edges").

**Formalization Note.** Every margin of the algorithm reads this function and never `v` directly.
Hence the seller `s_k` has margin `0` for its own buyer `b_k`, and a seller past its deadline has no
edge to a later buyer. -/
noncomputable def onlineWeight {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (i j : Fin n) : ℝ :=
  if (windowGraph n d).Adj i j then v s(i, j) else 0

/-- `OFF`: the maximum weight of a matching over `G_{d,σ}` (arXiv:1808.03526v1, §2, p.4; p.7).

**Formalization Note.** In the Adversarial Order setting `σ` is fixed, so the expectation in the
paper's "expected maximum-weight of a matching over `G_{d,σ}`" is over a point mass. The maximum is
the published `ProphetMatchingEFGT.optWeight`, a finite maximum over all matchings of the graph. -/
noncomputable def offlineOpt {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) : ℝ :=
  ProphetMatchingEFGT.optWeight (windowGraph n d) (fun e => v e.1)

end WindowedMatching


