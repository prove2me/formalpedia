-- Prove2me | Definitions.Def_LEDPCount_TwoRoundLocal
-- name    : LEDPCount_TwoRoundLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:20.609053+00:00
-- url     : https://prove2.me/theorems/8e88f5b6-47e9-4b1a-961b-2e42b2389213
-- title:
--   Two-round local algorithms on graphs, their transcript law, and $\varepsilon$-LEDP (Definitions 2.12–2.13)
-- statement:
--   In the local model for graph data each vertex $i\in[n]$ is a party holding its adjacency vector $A_i\in\{0,1\}^n$, and the algorithm interacts with the parties only through local randomizers applied to a single party's input. A **two-round local algorithm** consists of
--   1. for each party $i$, a round-1 randomizer $R^{(1)}_i:\{0,1\}^n\to\mathcal M_1$;
--   2. for each party $i$ and each vector $y=(y_1,\dots,y_n)$ of round-1 messages, a round-2 randomizer $R^{(2)}_{i,y}:\{0,1\}^n\to\mathbb R$;
--   3. an output map from transcripts $(y,m)$ to $\mathbb R$.
--
--   On the graph $G$ the round-1 messages are independent with $y_i\sim R^{(1)}_i(A_i)$; given $y$, the round-2 messages are independent with $m_i\sim R^{(2)}_{i,y}(A_i)$. The **transcript** $\Pi(G)=(y,m)$ has the resulting law. The algorithm is **$\varepsilon$-LEDP** (Definition 2.13 with $\delta=0$) if the map $G\mapsto\Pi(G)$ is $\varepsilon$-differentially private for edge-neighboring graphs:
--   $$
--   \Pr[\Pi(G)\in S]\le e^{\varepsilon}\Pr[\Pi(G')\in S]\qquad\text{for all }G\sim G'\text{ and measurable }S.
--   $$
--
--   **Formalization Note** This is the paper's interactive local model with a fixed two-round schedule in which every party is selected in both rounds and the round-2 randomizers are a function of the round-1 messages. Round-1 messages take finitely many values, so the transcript law is the finite mixture $\sum_y\Pr[y]\,(\delta_y\otimes\bigotimes_i R^{(2)}_{i,y}(A_i))$. The selected parties and the randomizers are determined by $y$, so recording them in the transcript would change nothing. Differential privacy is the published `ContinualCounting.IsApproxDP` with $\delta=0$.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §2.4, Definitions 2.12–2.13 and the local model, p.16–17 (PDF p.18–19)

import Mathlib
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_LEDPCount_EdgeNeighbors

namespace LEDPCount

open MeasureTheory

/-- The adjacency vector `A_i ∈ {0,1}^n` of vertex `i`, the private input of party `i` in the
local model for graph data (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, §2.1, p.13–14 and §2.4, p.17, PDF p.15–16, 19). -/
noncomputable def adjRow {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) : Fin n → Bool := by
  classical
  exact fun j => decide (G.Adj i j)

/-- A two-round local algorithm on `n`-vertex graphs (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, §2.4, p.16–17,
PDF p.18–19): every vertex `i` is a party holding its adjacency vector `A_i`.
In round 1 party `i` sends a message in `M₁` drawn from its local randomizer
`round1 i : {0,1}^n → Measure M₁` applied to its own row. In round 2 party `i` sends a real number
drawn from the randomizer `round2 i y : {0,1}^n → Measure ℝ`, which is chosen from the vector
`y` of round-1 messages and applied to its own row. The server outputs `output (y, m)`, a
function of the transcript.

**Formalization Note** This is the paper's interactive local model with a fixed two-round
schedule in which every party is selected in both rounds; the randomizers of round 2 are a
function of the round-1 transcript. -/
structure TwoRoundLocal (n : ℕ) (M₁ : Type) [MeasurableSpace M₁] where
  /-- Party `i`'s round-1 local randomizer. -/
  round1 : Fin n → (Fin n → Bool) → Measure M₁
  /-- Party `i`'s round-2 local randomizer, chosen from the round-1 messages. -/
  round2 : Fin n → (Fin n → M₁) → (Fin n → Bool) → Measure ℝ
  /-- The server's estimate, a function of the complete transcript. -/
  output : (Fin n → M₁) × (Fin n → ℝ) → ℝ

/-- The law of the complete transcript `Π(G) = (y, m)` of a two-round local algorithm on the
graph `G` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, §2.4, p.16–17, PDF p.18–19): the round-1 messages
`y = (y_1, …, y_n)` are independent with `y_i ∼ round1 i (A_i)`, and given `y` the round-2
messages are independent with `m_i ∼ round2 i y (A_i)`, using fresh coins.

**Formalization Note** Round-1 messages take finitely many values, so the law is the finite
mixture `∑_y Pr[y] · (δ_y ⊗ ⊗_i round2 i y (A_i))`. The selected parties and the assigned
randomizers are fixed or determined by `y`, so recording them in the transcript changes
nothing. -/
noncomputable def TwoRoundLocal.transcript {n : ℕ} {M₁ : Type} [MeasurableSpace M₁] [Fintype M₁]
    [MeasurableSingletonClass M₁] (P : TwoRoundLocal n M₁) (G : SimpleGraph (Fin n)) :
    Measure ((Fin n → M₁) × (Fin n → ℝ)) :=
  ∑ y : Fin n → M₁, (Measure.pi fun i => P.round1 i (adjRow G i)) {y} •
    (Measure.dirac y).prod (Measure.pi fun i => P.round2 i y (adjRow G i))

/-- Definition 2.13 (Local Edge Differential Privacy) with `δ = 0` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.17,
PDF p.19): a local algorithm is ε-LEDP if the randomized algorithm that outputs its complete
transcript `Π(G)` is ε-DP with respect to the edge-neighboring relation (Definition 2.11).

**Formalization Note** ε-DP is the published `ContinualCounting.IsApproxDP` (Definition 2.6 for an
arbitrary relation) with `δ = 0`. -/
def TwoRoundLocal.IsLEDP {n : ℕ} {M₁ : Type} [MeasurableSpace M₁] [Fintype M₁]
    [MeasurableSingletonClass M₁] (P : TwoRoundLocal n M₁) (ε : ℝ) : Prop :=
  ContinualCounting.IsApproxDP EdgeNeighbors P.transcript ε 0

end LEDPCount


