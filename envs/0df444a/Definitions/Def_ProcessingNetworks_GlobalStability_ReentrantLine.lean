-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine
-- name    : ProcessingNetworks_GlobalStability_ReentrantLine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:11:10.170668+00:00
-- url     : https://prove2.me/theorems/dce8cb3d-3775-4ce4-8d81-a1fc3e6dc23b
-- title:
--   The two-station, five-class re-entrant network (Figure 8.3) and its Lyapunov ingredients
-- statement:
--   Figure 8.3 depicts a re-entrant line with a single input stream (rate $\lambda_1$, into class
--   $1$) and a single deterministic route $1\to2\to3\to4\to5\to$ exit; station 1 serves classes
--   $\{1,3,5\}$, station 2 serves classes $\{2,4\}$ (recoverable from the book's own computations
--   in Lemma 8.26's proof, which group $G_1$/$H_1$ around classes $1,3,5$ and $G_2$/$H_2$ around
--   $2,4$). `reentrantLineData` instantiates this as a `QueueingNetworkData 5 2` (`0`-indexed
--   classes `0,…,4` for the book's `1,…,5`).
--
--   $G_1, G_2$ (Eqs. 8.50-8.51) are the two components of the piecewise-linear Lyapunov function
--   $h = \max(G_1,G_2)$ (Eq. 8.53) Theorem 8.25's sufficiency proof builds, in terms of the
--   cumulative sums $Z_j^+ := Z_1+\cdots+Z_j$ along the route; $H_1, H_2$ (used in Lemma 8.26) are
--   the raw total fluid content at each station.
--
--   **Formalization note.** The class-to-station assignment and route structure were determined
--   from the surrounding prose's explicit computations (Lemma 8.26's proof spells out
--   $G_1 = x_1Z_1+x_3(Z_1{+}Z_3)+x_5(Z_1{+}Z_3{+}Z_5)$ and $G_2=x_2Z_1+x_4(Z_1{+}Z_3)$ under
--   $H_2=0$), not read off the figure directly, but the two are consistent and the figure was
--   consulted to confirm the two-station, single-route topology as pictured.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 155, Figure 8.3 and Eqs. (8.50)-(8.53)

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

/-- The two-station, five-class re-entrant queueing network of Figure 8.3, Dai & Harrison p. 155
(PDF p. 171): classes `0,…,4` (standing for the book's classes `1,…,5`) form a single
deterministic route `0 → 1 → 2 → 3 → 4 → exit`, with external arrivals (rate `lam1`) only into
class `0`. Station 1 serves classes `{0,2,4}` (the book's `{1,3,5}`), station 2 serves classes
`{1,3}` (the book's `{2,4}`); both are single-server (`b ≡ 1`). -/
def reentrantLineData (lam1 m1 m2 m3 m4 m5 : ℝ) : QueueingNetworkData 5 2 where
  p := ![0, 1, 0, 1, 0]
  P := fun i j => if (i : ℕ) + 1 = (j : ℕ) then 1 else 0
  m := ![m1, m2, m3, m4, m5]
  lam := ![lam1, 0, 0, 0, 0]
  b := ![1, 1]

/-- `G₁(t) := x₁Z₁⁺(t) + x₃Z₃⁺(t) + x₅Z₅⁺(t)`, Eq. (8.50), where `Zⱼ⁺ := Z₁+⋯+Zⱼ`: the
piecewise-linear Lyapunov function's station-1 component, for the re-entrant line with classes
`0,2,4` (`1,3,5`) at station 1. -/
def reentrantG1 (x1 x3 x5 : ℝ) (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  x1 * Zh t 0 + x3 * (Zh t 0 + Zh t 1 + Zh t 2) + x5 * (Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3 + Zh t 4)

/-- `G₂(t) := x₂Z₂⁺(t) + x₄Z₄⁺(t)`, Eq. (8.51): the station-2 component. -/
def reentrantG2 (x2 x4 : ℝ) (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  x2 * (Zh t 0 + Zh t 1) + x4 * (Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3)

/-- `H₁(t) := Z₁(t)+Z₃(t)+Z₅(t)`: the total fluid at station 1. -/
def reentrantH1 (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  Zh t 0 + Zh t 2 + Zh t 4

/-- `H₂(t) := Z₂(t)+Z₄(t)`: the total fluid at station 2. -/
def reentrantH2 (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  Zh t 1 + Zh t 3

end ProcessingNetworks.GlobalStability


