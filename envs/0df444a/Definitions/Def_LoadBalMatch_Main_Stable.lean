-- Prove2me | Definitions.Def_LoadBalMatch_Main_Stable
-- name    : LoadBalMatch_Main_Stable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:20.889303+00:00
-- url     : https://prove2.me/theorems/4347dc0e-7e86-4c4c-a9a7-220dae41f5da
-- title:
--   Stable subgraphs (Definition 2.1) and the stabilizing pass (Algorithm 1 line (2b), Algorithm 4 line (2e))
-- statement:
--   Let $G$ be a graph on $V$ and $H\subseteq G$ a subgraph. Following Definition 2.1, $H$ is **stable** (in $G$) if
--   $$\mu(H)=\mu(H\cup\{e\})\qquad\text{for all edges } e \text{ of } G,$$
--   that is, no single edge of $G$ increases the matching number of $H$.
--
--   The **stabilizing pass** started from a graph $H_0$ over a list $\sigma=(e_1,\dots,e_m)$ of pairs scans the list in order: $H_j=H_{j-1}\cup\{e_j\}$ if $\mu(H_{j-1}\cup\{e_j\})>\mu(H_{j-1})$, and $H_j=H_{j-1}$ otherwise; its result is $H_m$. This is line (2b) of Algorithm 1 and line (2e) of Algorithm 4 ("Scan the edges $e\in E$ in the stream order and immediately add $e$ to $H$ whenever $\mu(H\cup\{e\})>\mu(H)$").
--
--   Stable subgraphs are the graphs the algorithms keep between iterations; Lemma 4.5 shows the pass produces one.
--
--   **Formalization Note.** `IsStable G H` includes `H ≤ G`. `stabilize H₀ σ` is a left fold over the list `σ`.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 3, Definition 2.1; p. 16, Algorithm 1 line (2b); p. 46, Algorithm 4 line (2e)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching

/-!
# Stable subgraphs (Definition 2.1) and the stabilizing pass

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…), p. 3, Definition 2.1:
"Given a graph G and a subgraph H ⊆ G, we say that H is stable if it has the property that
µ(H) = µ(H ∪ {e}) for all e ∈ G."
Algorithm 1 line (2b), p. 16, and Algorithm 4 line (2e), p. 46: "Scan the edges e ∈ E in the stream
order and immediately add e to H whenever µ(H ∪ {e}) > µ(H)."

`stabilize H₀ σ` is that scan, started from `H₀`, over the list `σ`.
-/

namespace LoadBalMatch.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 2.1: `H` is a stable subgraph of `G`. -/
def IsStable (G H : SimpleGraph V) : Prop :=
  H ≤ G ∧ ∀ e ∈ G.edgeSet, matchingNumber (addEdges H {e}) = matchingNumber H

/-- The stabilizing pass: scan `σ` in order and add `e` to the current graph `H` whenever
`µ(H ∪ {e}) > µ(H)`. -/
noncomputable def stabilize (H₀ : SimpleGraph V) (σ : List (Sym2 V)) : SimpleGraph V :=
  σ.foldl (fun H e =>
    if matchingNumber H < matchingNumber (addEdges H {e}) then addEdges H {e} else H) H₀

end LoadBalMatch.Main


