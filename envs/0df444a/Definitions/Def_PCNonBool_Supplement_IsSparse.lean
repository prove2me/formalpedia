-- Prove2me | Definitions.Def_PCNonBool_Supplement_IsSparse
-- name    : PCNonBool_Supplement_IsSparse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:21.899698+00:00
-- url     : https://prove2.me/theorems/a724afd7-7c7b-4e05-898b-69e6d11fbc6e
-- title:
--   $(s,\varepsilon)$-sparse graph
-- statement:
--   A graph $G=(V,E)$ is **$(s,\varepsilon)$-sparse** if every set $U\subseteq V$ with $|U|\le s$ spans few edges:
--   $$|E(U)|\le(1+\varepsilon)\,|U|,$$
--   where $E(U)$ is the set of edges with both endpoints in $U$. (This is $(s,\varepsilon,\lambda)$-sparsity with $\lambda=0$.)
--
--   Local sparsity is the expansion-type hypothesis of the colouring lower bound: random regular and Erdős–Rényi graphs of bounded average degree are sparse with linear $s$.
--
--   **Formalization Note** $s$ is a natural number and $\varepsilon$ a real; edges are unordered pairs (`Sym2`).
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2 (Local sparsity), p.10 (PDF p.13)

import Mathlib

namespace PCNonBool.Supplement

/-- Local sparsity (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2, "Local sparsity", p.10 (PDF p.13)): a graph `G = (V, E)` is
`(s, ε)`-sparse if every set `U ⊆ V` with `|U| ≤ s` satisfies `|E(U)| ≤ (1 + ε)|U|`, where
`E(U)` is the set of edges with both endpoints in `U`. (This is `(s, ε, λ)`-sparsity with
`λ = 0`.)

**Formalization Note** `E(U)` is the set of edges of `G` (unordered pairs, `Sym2 V`) lying in
`U.sym2`, i.e. with both endpoints in `U`. `s` is a natural number and `ε` a real. -/
def IsSparse {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (ε : ℝ) : Prop :=
  ∀ U : Finset V, U.card ≤ s →
    (((G.edgeFinset.filter (fun e => e ∈ U.sym2)).card : ℕ) : ℝ) ≤ (1 + ε) * (U.card : ℝ)

end PCNonBool.Supplement


