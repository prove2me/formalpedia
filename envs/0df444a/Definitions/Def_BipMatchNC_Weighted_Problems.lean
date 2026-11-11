-- Prove2me | Definitions.Def_BipMatchNC_Weighted_Problems
-- name    : BipMatchNC_Weighted_Problems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:13:43.636334+00:00
-- url     : https://prove2.me/theorems/278046e4-0ed5-4710-89aa-d439dcf638c7
-- title:
--   Encodings of bipartite graphs and weighted instances, the language PM, and the output relations of the weight and search problems
-- statement:
--   A balanced bipartite graph on $[n]+[n]$ is encoded by the self-delimiting binary code of $n$ followed by the $n^2$ bits of its bi-adjacency matrix in row-major order; the language **PM** consists of the codes of graphs having a perfect matching (every other word is outside). A **weighted instance** is a graph $G$ with edge weights $w:E\to\mathbb N$ (stored as an $n\times n$ table that is $0$ off the edges), encoded as the graph code followed by the codes of the $n^2$ table entries in row-major order. Its weights are **bounded by $n^c+c$** if every edge weight is at most $n^c+c$.
--
--   A correct output of the **maximum weight perfect matching search problem** is the bit $1$ followed by the $n^2$ row-major bits of the edge set of a perfect matching of maximum total weight, if $G$ has a perfect matching, and the bit $0$ (the flag "no perfect matching") followed by $n^2$ zeros otherwise. A correct output of the **maximum weight problem** is $1$ followed by the code of $w^*$ if $G$ has a perfect matching, and the single bit $0$ otherwise.
--
--   **Formalization Note.** `encGraph`, `PMLanguage`, `WInstance` (with `w_nonedge`), `WInstance.enc`, `WInstance.Bounded c`, `pmBits`, `MaxWeightPMOutput`, `MaxPMWeightOutput`. Numbers are coded with the published `TreeEdgeRankPC.encNat` (each bit of the binary expansion preceded by `1`, then a final `0`), which makes both codes injective.
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 2 (PDF 3), Theorem 1.1; p. 4 (PDF 5), §2.1; p. 13 (PDF 14), Theorem 3.5

import Mathlib
import Definitions.Def_TreeEdgeRankPC_Circuit
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph

namespace BipMatchNC.Weighted

open TreeEdgeRankPC

/-- The binary code of a balanced bipartite graph on `[n] + [n]`: the self-delimiting code
`encNat n` (published with `TreeEdgeRankPC_Circuit`), then the `n²` bits of the bi-adjacency matrix
in row-major order. It is injective. -/
def encGraph {n : ℕ} (G : BipGraph n) : List Bool :=
  encNat n ++ (List.finRange n).flatMap fun i => (List.finRange n).map fun j => G.adj i j

/-- The language `PM` (§2.1, p. 4), as words: the codes of balanced bipartite graphs that have a
perfect matching. Every other word, including every word that is not a code, is outside. -/
def PMLanguage : Set (List Bool) :=
  {x | ∃ (n : ℕ) (G : BipGraph n), x = encGraph G ∧ G.HasPM}

/-- An instance of the weighted problems: a balanced bipartite graph `G` on `[n] + [n]` and edge
weights `w : E → ℕ` (§2.1, p. 4), stored as an `n × n` table that is `0` off the edges. -/
structure WInstance where
  /-- The number of vertices on each side. -/
  n : ℕ
  /-- The graph. -/
  G : BipGraph n
  /-- The weights `w(u_i, v_j) = w i j`. -/
  w : Fin n → Fin n → ℕ
  /-- Non-edges carry weight `0`. -/
  w_nonedge : ∀ i j, G.adj i j = false → w i j = 0

namespace WInstance

/-- The binary code of an instance: `encGraph G`, then `encNat (w i j)` for every pair `(i, j)` in
row-major order. It is injective. -/
def enc (x : WInstance) : List Bool :=
  encGraph x.G ++
    (List.finRange x.n).flatMap fun i => (List.finRange x.n).flatMap fun j => encNat (x.w i j)

/-- The weights are **bounded by the polynomial `n^c + c`**: every edge weight is at most
`n^c + c`. "Polynomially bounded weights" means this bound for some constant `c` fixed in advance. -/
def Bounded (c : ℕ) (x : WInstance) : Prop :=
  ∀ i j, x.G.adj i j = true → x.w i j ≤ x.n ^ c + c

end WInstance

/-- The edge set of the perfect matching `π` as `n²` bits in row-major order: bit `(i, j)` is `1`
iff `π i = j`. -/
def pmBits {n : ℕ} (π : Equiv.Perm (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => decide (π i = j)

/-- The correct outputs of the **maximum weight perfect matching search problem** on the instance
`x`: if `G` has a perfect matching, the bit `1` followed by the edge set of a perfect matching of
maximum total weight; otherwise the bit `0` (the flag "no perfect matching") followed by `n²`
zeros. -/
def MaxWeightPMOutput (x : WInstance) (y : List Bool) : Prop :=
  (x.G.HasPM ∧ ∃ π, x.G.IsMaxWeightPM x.w π ∧ y = true :: pmBits π) ∨
    (¬ x.G.HasPM ∧ y = false :: List.replicate (x.n * x.n) false)

/-- The correct outputs of the **maximum weight problem** (Theorem 3.5) on the instance `x`: if `G`
has a perfect matching, the bit `1` followed by `encNat w*`, the code of the maximum weight of a
perfect matching; otherwise the single bit `0`. -/
def MaxPMWeightOutput (x : WInstance) (y : List Bool) : Prop :=
  (x.G.HasPM ∧ y = true :: encNat (x.G.maxPMWeight x.w)) ∨ (¬ x.G.HasPM ∧ y = [false])

end BipMatchNC.Weighted


