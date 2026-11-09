-- Prove2me | Definitions.Def_TermCycDich_OutcomeCorrect
-- name    : TermCycDich_OutcomeCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:58.12352+00:00
-- url     : https://prove2.me/theorems/a32d33ca-18db-49fd-ba6e-8fe8e62733d7
-- title:
--   Correct outcome of Theorem 1.2
-- statement:
--   For an annotated graph $(G,R)$, an integer $b$ and a function $\tau:\mathbb N^2\to\mathbb N$, an outcome is **correct** if
--
--   1. it is "$\mathrm{bidim}(G,R)>b$" and indeed $\mathrm{bidim}(G,R)>b$; or
--   2. it is a vertex set $S$ with $R\subseteq S$, $S\ne V(G)$, the set $V(G)\setminus S$ irrelevant for $(G,R)$, and $G[S]$ not containing the complete graph $K_{6(b+1)^2+1}$ as a minor; or
--   3. it is a tree-decomposition of $G$ of width at most $\tau(b,|G|)$, i.e. every bag has at most $\tau(b,|G|)+1$ vertices.
--
--   **Formalization Note** Minors and tree-decompositions are the public `RobertsonSeymour1986.GM5.IsMinor` and `RobertsonSeymour1986.GM5.IsTreeDecomposition`.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.2, p.4 (PDF 6)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_TermCycDich_AnnotatedGraph
import Definitions.Def_TermCycDich_bidim
import Definitions.Def_TermCycDich_IsIrrelevant
import Definitions.Def_TermCycDich_Outcome

namespace TermCycDich

/-- The outcome `o` is a **correct answer of Theorem 1.2** for the annotated graph `x = (G, R)`,
the integer `b` and the width function `τ`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.2, p.4 (PDF 6) (restated p.56 (PDF 58)): "i) bidim(G, R) > b, ii) an induced
subgraph G_0 with R ⊆ V(G_0) such that V(G) \ V(G_0) ≠ ∅ is irrelevant and G_0 does not contain
K_{6(b+1)²+1} as a minor, or iii) a tree-decomposition for G of width at most τ(b, |G|)".

**Formalization Note**
1. `bidimGt`: `b < bidim(G, R)`.
2. `keep S`: `R ⊆ S`, `S ≠ V(G)`, the complement `V(G) \ S` is irrelevant (`IsIrrelevant`), and
   `G[S]` has no `K_{6(b+1)²+1}` minor (`⊤` on `Fin (6(b+1)²+1)`, public
   `RobertsonSeymour1986.GM5.IsMinor`).
3. `treeDec m T bag`: a tree-decomposition (public
   `RobertsonSeymour1986.GM5.IsTreeDecomposition`) with every bag of size at most `τ(b, |G|) + 1`
   (width `≤ τ(b, |G|)`). -/
def OutcomeCorrect (x : AnnotatedGraph) (b : ℕ) (τ : ℕ → ℕ → ℕ) : Outcome x.n → Prop
  | .bidimGt => b < bidim x.G (↑x.R : Set (Fin x.n))
  | .keep S => x.R ⊆ S ∧ S ≠ Finset.univ ∧
      IsIrrelevant x.G (↑x.R : Set (Fin x.n)) (↑(Sᶜ) : Set (Fin x.n)) ∧
      ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : SimpleGraph (Fin (6 * (b + 1) ^ 2 + 1)))
        (x.G.induce (↑S : Set (Fin x.n)))
  | .treeDec _ T bag => RobertsonSeymour1986.GM5.IsTreeDecomposition x.G T bag ∧
      ∀ t, (bag t).card ≤ τ b x.n + 1

end TermCycDich


