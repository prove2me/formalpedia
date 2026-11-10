-- Prove2me | Definitions.Def_LEDPCount_IsLocalRandomizer
-- name    : LEDPCount_IsLocalRandomizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:39.99984+00:00
-- url     : https://prove2.me/theorems/0d85d853-f466-4a06-9fb9-48bd3416fc2a
-- title:
--   $\varepsilon$-local randomizer (Definition 2.14)
-- statement:
--   Recall that a randomized algorithm $M$ is **$\varepsilon$-differentially private** for a neighbouring relation $\sim$ (Definition 2.6 with $\delta=0$) if $\Pr[M(x)\in S]\le e^{\varepsilon}\Pr[M(x')\in S]$ for every neighbouring pair $x\sim x'$ and every measurable event $S$. An **$\varepsilon$-local randomizer** (Definition 2.14 with $\delta=0$) is a randomized map $R:\{0,1\}^m\to\mathcal Y$ such that, for every pair $a,a'\in\{0,1\}^m$ differing in exactly one coordinate and every measurable $S\subseteq\mathcal Y$,
--   $$
--   \Pr[R(a)\in S]\le e^{\varepsilon}\,\Pr[R(a')\in S].
--   $$
--   In the local model for graphs, each party's private input is its adjacency vector and every message it sends is drawn from a local randomizer applied to that vector.
--
--   **Formalization Note** The inequality is the published `ContinualCounting.IsApproxDP` (Definition 2.6 for an arbitrary relation) with $\delta=0$. Bits are Booleans, and "differ in exactly one coordinate" is the published relation `PrivLearn.Generic.Neighbors` on $\mathrm{Fin}\,m\to\mathrm{Bool}$.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Definition 2.14, p.17 (PDF p.19); Definition 2.6, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_ContinualCounting_IsApproxDP

namespace LEDPCount

open MeasureTheory

/-- Definition 2.14 (Local Randomizer) with `δ = 0` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.17, PDF p.19): a
randomized mapping `R : {0,1}^m → Y` is an ε-local randomizer if
`Pr[R(a) ∈ S] ≤ e^ε Pr[R(a') ∈ S]` for every pair `a, a' ∈ {0,1}^m` differing in exactly one
coordinate and every measurable `S ⊆ Y`.

**Formalization Note** The inequality is the published `ContinualCounting.IsApproxDP` (Definition
2.6 for an arbitrary neighbour relation) with `δ = 0`. Bits are `Bool`; "differing in exactly
one coordinate" is the published `PrivLearn.Generic.Neighbors` on `Fin m → Bool` (`a i ≠ a' i`
for exactly one `i`). The paper's row length is `m = n`; Lemma 2.16 uses `m = t`. -/
def IsLocalRandomizer {m : ℕ} {Y : Type*} [MeasurableSpace Y] (R : (Fin m → Bool) → Measure Y)
    (ε : ℝ) : Prop :=
  ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors R ε 0

end LEDPCount


