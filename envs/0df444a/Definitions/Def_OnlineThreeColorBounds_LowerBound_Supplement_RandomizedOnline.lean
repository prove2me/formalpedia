-- Prove2me | Definitions.Def_OnlineThreeColorBounds_LowerBound_Supplement_RandomizedOnline
-- name    : OnlineThreeColorBounds_LowerBound_Supplement_RandomizedOnline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:35.573297+00:00
-- url     : https://prove2.me/theorems/95f924c0-ae48-439f-afe3-c1e4c04cf6c8
-- title:
--   Randomized online coloring on the log-cost RAM with fair coins
-- statement:
--   An ordered graph on $m$ vertices is a graph on the arrival indices $0,1,\dots,m-1$. Arrival $i$ reveals its **earlier-neighbor set** $N^-(i)=\{j<i: j\sim i\}$. At arrival $i$ the **revealed prefix** is the list $N^-(0),\dots,N^-(i)$.
--
--   A **randomized online coloring algorithm** is one program $P$ of the published logarithmic-cost RAM with fair coins (`TimeSpaceMA_RAM`, run through `SoftmaxAttnFD_Machine`). It runs on a single infinite tape $\tau$ of independent fair bits. At arrival $i$ the program is started on the encoded revealed prefix, and the color of $i$ is the content of cell $0$ when it halts. Every arrival uses the same tape $\tau$, so the algorithm keeps its random choices from one arrival to the next. The program never sees later arrivals, the number of vertices, or a three-coloring of the graph.
--
--   For an input graph $G$ and a tape $\tau$:
--
--   1. the run **halts** if it halts at every arrival;
--   2. the **total cost** is the sum, over all arrivals, of the bit cost of the run at that arrival. Each executed instruction costs $1$ plus the bit lengths of the addresses and values it touches, and a run that does not halt costs $+\infty$;
--   3. the **history** of the run records, for each arrival, its earlier-neighbor set and its one color;
--   4. $C_A(G,\pi)$ is the number of distinct colors in that history.
--
--   These objects state Theorem 1.2: properness on every halting tape, the expected number of colors, and the expected total running time.
--
--   **Formalization Note** A prefix is encoded as its number of arrivals followed by, for each arrival, the size of its earlier-neighbor set and its elements in increasing order. The encoding is stored with the published `memOf`: loading is free and a cell is paid for when it is read. Each arrival restarts the program on its prefix with the shared tape. A stateful implementation is recovered by replaying earlier arrivals, at most a factor $m$ more cost, so the class of expected-polynomial-time algorithms is unchanged. On a tape where some arrival does not halt, the color read is a placeholder. The theorem uses it only on halting tapes, and the finite expected cost makes the non-halting tapes a null set.
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a; online model §1, printed p. 1 / PDF p. 2; randomized algorithm and its running time §3.3 and proof of Theorem 1.2, printed pp. 12–13, 17 / PDF pp. 13–14, 18

import Definitions.Def_OnlineThreeColorBounds_LowerBound_OnlineAlgorithm
import Definitions.Def_SoftmaxAttnFD_Machine
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace OnlineThreeColorBounds.LowerBound.Supplement

open OnlineThreeColorBounds.LowerBound

/-- The input revealed at arrival `i` of the ordered graph `G`: the earlier-neighbor sets of
arrivals `0, …, i`, in arrival order. -/
noncomputable def prefixInput {m : ℕ} (G : SimpleGraph (Fin m)) (i : Fin m) :
    List (Finset ℕ) :=
  (List.ofFn (earlierNeighbors G)).take (i.val + 1)

/-- Encoding of a revealed prefix as a list of naturals: the number of arrivals, then for each
arrival the size of its earlier-neighbor set followed by its elements in increasing order. -/
def encodePrefix (ns : List (Finset ℕ)) : List ℕ :=
  ns.length :: ns.flatMap (fun s => s.card :: s.sort (· ≤ ·))

/-- The initial memory of the run for arrival `i` (published `memOf`: cell `j` holds the `j`-th
entry of the encoding; loading is free, a cell is paid for when read). -/
noncomputable def arrivalMem {m : ℕ} (G : SimpleGraph (Fin m)) (i : Fin m) : ℕ → ℕ :=
  TimeSpaceMA.memOf (encodePrefix (prefixInput G i))

/-- The color that the randomized online algorithm given by program `P` assigns to arrival `i`
on coin tape `τ`: cell `0` of the memory at the first halted state of `P` run on the revealed
prefix. The same tape `τ` is used for every arrival, so the algorithm keeps its random choices
across arrivals; it sees neither later arrivals nor the number of vertices. -/
noncomputable def arrivalColor (P : TimeSpaceMA.Program) {m : ℕ} (G : SimpleGraph (Fin m))
    (τ : ℕ → Bool) (i : Fin m) : ℕ :=
  SoftmaxAttnFD.final P (arrivalMem G i) τ 0

/-- On tape `τ` the run halts at every arrival. -/
def AllHalt (P : TimeSpaceMA.Program) {m : ℕ} (G : SimpleGraph (Fin m)) (τ : ℕ → Bool) : Prop :=
  ∀ i : Fin m, SoftmaxAttnFD.cost P (arrivalMem G i) τ < ⊤

/-- Total bit cost of the online run on tape `τ`: the sum over all arrivals of the published
`cost` (which is `⊤` at an arrival where the run does not halt). -/
noncomputable def onlineCost (P : TimeSpaceMA.Program) {m : ℕ} (G : SimpleGraph (Fin m))
    (τ : ℕ → Bool) : ℝ≥0∞ :=
  ∑ i : Fin m, SoftmaxAttnFD.cost P (arrivalMem G i) τ

/-- The history of the online run on tape `τ`: arrival `i` records its earlier neighbors and the
single color assigned to it. -/
noncomputable def onlineHistory (P : TimeSpaceMA.Program) {m : ℕ} (G : SimpleGraph (Fin m))
    (τ : ℕ → Bool) : History :=
  List.ofFn (fun i : Fin m => (earlierNeighbors G i, ({arrivalColor P G τ i} : Finset ℕ)))

/-- `C_A(G, π)` on tape `τ`: the number of distinct colors used by the online run. -/
noncomputable def colorsUsed (P : TimeSpaceMA.Program) {m : ℕ} (G : SimpleGraph (Fin m))
    (τ : ℕ → Bool) : ℕ :=
  colorCount (onlineHistory P G τ)

end OnlineThreeColorBounds.LowerBound.Supplement


