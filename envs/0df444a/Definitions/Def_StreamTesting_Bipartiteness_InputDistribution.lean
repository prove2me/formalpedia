-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_InputDistribution
-- name    : StreamTesting_Bipartiteness_InputDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:34.810631+00:00
-- url     : https://prove2.me/theorems/6de32972-2207-4e78-a55e-ff3005d71863
-- title:
--   Random labelings and independent random-order hard inputs
-- statement:
--   For $H$ on $m$ vertices, let $n=2m$. A labeling $\Lambda:[n]\to V(H)\times\{0,1\}$ is a bijection undoing the observed labeling. The graph on observed labels is obtained by transporting the actual adjacency of $G_s$ along $\Lambda$.
--
--   The input distribution $D_s$ samples $\Lambda$ and the label arrival permutation $\sigma$ independently and uniformly, then uses that transported graph and order. Counting actual bijections preserves multiplicities when graph automorphisms yield the same labeled graph.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §4.1, printed p.21 / PDF p.21.

import Definitions.Def_StreamTesting_Bipartiteness_Lift
import Definitions.Def_StreamTesting_Bipartiteness_Policy
import Definitions.Def_PunctSketch_coinProb

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Λ undoes the labeling. Both types have exactly 2m elements. -/
abbrev Labeling (m : ℕ) := Fin (2 * m) ≃ (Fin m × Bool)

/-- Transport the actual lift to the observed labels. -/
def labeledGraph {m : ℕ} (H : SimpleGraph (Fin m)) (s : Bool) (Λ : Labeling m) :
    SimpleGraph (Fin (2 * m)) where
  Adj x y := (liftGraph H s).Adj (Λ x) (Λ y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => (liftGraph H s).loopless.irrefl _ h⟩

/-- Actual D_s experiment: independent uniform Λ and σ, mapped to graph/order.
Multiplicities of labelings producing the same graph are retained. -/
def inputProb {m : ℕ} (H : SimpleGraph (Fin m)) (s : Bool)
    (P : SimpleGraph (Fin (2 * m)) → Order (2 * m) → Prop) : ℝ :=
  PunctSketch.coinProb (fun ω : Labeling m × Order (2 * m) => P (labeledGraph H s ω.1) ω.2)

end StreamTesting.Bipartiteness


