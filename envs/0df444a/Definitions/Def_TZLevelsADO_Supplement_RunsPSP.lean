-- Prove2me | Definitions.Def_TZLevelsADO_Supplement_RunsPSP
-- name    : TZLevelsADO_Supplement_RunsPSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:19:12.680202+00:00
-- url     : https://prove2.me/theorems/0bbcc825-88e7-4679-bf34-2986bc2a8e80
-- title:
--   Prescribed-pairs shortest paths on the comparison–addition machine: $(\alpha,\beta)$-approximations, unweighted graphs, and the run predicate
-- statement:
--   In the **prescribed-pairs shortest paths problem** ($t$-PSP) the input is a weighted undirected graph $G$ with $n$ vertices and $m$ edges, an integer parameter $k$, and a list $I = (\langle u_0, v_0\rangle, \dots, \langle u_{t-1}, v_{t-1}\rangle)$ of $t$ vertex pairs; the goal is an estimate $\hat d(u_j, v_j)$ of the distance $d(u_j, v_j)$ for every pair. The case $t = n$ is **n-PSP** and $t = m$ is **m-PSP**.
--
--   An estimate $\hat d$ is an **$(\alpha, \beta)$-approximation** of $d(u, v)$ if
--   $$d(u, v) \le \hat d \le \alpha\, d(u, v) + \beta,$$
--   and an $\alpha$-approximation if moreover $\beta = 0$. A graph is **unweighted** if every edge has weight $1$.
--
--   An algorithm is a single program for the comparison–addition machine (the word RAM with real addition, negation and comparison, run on a tape of fair coins). The instance is written in its input cells: the integers $n, m, k$, the endpoints of every edge, the number $t$ of pairs, and the endpoints $u_0, \dots, u_{t-1}$ and $v_0, \dots, v_{t-1}$; the edge weights are in the real input cells. Words have $O(\log(n + m + k + t))$ bits. The estimate for the $j$-th pair is the $j$-th real output cell when the program halts.
--
--   The program **solves** the instance with per-pair guarantee $\mathrm{Good}$, within $T$ steps with probability at least $1 - \varepsilon$, if there is a measurable set $E$ of coin tapes of probability at least $1 - \varepsilon$ such that on **every** coin tape the program halts and every output satisfies $\mathrm{Good}$, and on every tape of $E$ it halts within $T$ steps. This is the paper's convention that stretch bounds hold for every outcome of the sampling and running-time bounds hold with high probability.
--
--   These are the objects in which Theorems 3, 4, 6, 7 and 18 of the paper are stated.
--
--   **Formalization Note** The pairs form a list, so repetitions are allowed. The input layout extends the preprocessing input of `IsADO` (cells $0,1,2$: $n,m,k$; $3+e$ and $3+m+e$: the edge endpoints; $3+2m$: $t$; $4+2m+j$ and $4+2m+t+j$: $u_j$, $v_j$).
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §1, p.2 (PDF p.3) (t-PSP, n-PSP, m-PSP); p.1 (PDF p.2) ((α, β)-approximation); Definition 5, pp.3–4 (PDF pp.4–5); §2, pp.6–7 (PDF pp.7–8) (unweighted graphs, randomness convention)

import Mathlib
import Definitions.Def_RealAPSP_Machine
import Definitions.Def_TZLevelsADO_Graph
import Definitions.Def_TZLevelsADO_IsADO

open MeasureTheory

namespace TZLevelsADO.Supplement

/-!
# Prescribed-pairs shortest paths (t-PSP) on the comparison–addition machine

S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §1, p.2 (PDF p.3): "given a set I ⊆ V × V of t pairs, the goal is to
compute an estimate d̂(u, v) for every ⟨u, v⟩ ∈ I. … t = n, which we denote by n-PSP. We write m-PSP
for the case t = m."; Definition 5, pp.3–4 (PDF pp.4–5), the (t, s)-PSP; §2, p.6 (PDF p.7):
"ℓ(x, y) = 1 in unweighted graphs"; §2, p.7 (PDF p.8): "our running-time and space bounds hold with
high probability, and our stretch bounds hold for every outcome of the sampling"; p.1 (PDF p.2): an
estimate is an (α, β)-approximation if d(u, v) ≤ d̂(u, v) ≤ αd(u, v) + β.

**Formalization Note.**
* **Machine.** The algorithm is one program for the published comparison–addition RAM
  `RealAPSP.Machine` (the machine of the mission's Theorem 1), run on a fair coin tape.
* **Pairs.** The prescribed pairs are a list `I` of `t = I.length` pairs of vertices (repetitions
  allowed, which is more general than a set).
* **Input layout.** It extends the preprocessing input of `TZLevelsADO.IsADO`: integer cells `0, 1, 2`
  hold `n, m, k`; cells `3 + e` and `3 + m + e` hold the endpoints `src e`, `dst e`; cell `3 + 2m`
  holds `t`; cells `4 + 2m + j` and `4 + 2m + t + j` hold the endpoints `u_j`, `v_j` of the `j`-th
  pair; real cell `e` holds `ℓ(e)`.
* **Word size.** `pspWidth = n + m + k + t + 2`, so every input integer fits in a word.
* **Output.** The estimate `d̂(u_j, v_j)` is real cell `routCell j` of the halted state.
* **Randomness.** `RunsPSP` asks for one measurable set `E` of coin tapes of probability at least
  `1 − fail`. On **every** tape the program halts and every output satisfies the per-pair guarantee
  `Good`; on every tape in `E` it halts within `T` steps.
-/

/-- §2, p.6: an unweighted graph, `ℓ(x, y) = 1` for every edge. -/
def Unweighted (G : Graph) : Prop := ∀ e, G.wt e = 1

/-- p.1: `d̂` is an `(α, β)`-approximation of `d(u, v)`: `d(u, v) ≤ d̂ ≤ α·d(u, v) + β`. -/
def IsApprox (G : Graph) (α β : ℝ) (u v : Fin G.n) (dhat : ℝ) : Prop :=
  dist G u v ≤ dhat ∧ dhat ≤ α * dist G u v + β

/-- The word-size parameter of a PSP instance: words have `O(log (n + m + k + t + 2))` bits. -/
def pspWidth (G : Graph) (k : ℕ) (I : List (Fin G.n × Fin G.n)) : ℕ :=
  G.n + G.m + k + I.length + 2

/-- The integer input cells: `n, m, k`, the edge endpoints, `t`, then `u₀, …, u_{t−1}`, `v₀, …, v_{t−1}`. -/
def pspInts (G : Graph) (k : ℕ) (I : List (Fin G.n × Fin G.n)) : List ℤ :=
  prepInts G k ++ [(I.length : ℤ)] ++ I.map (fun p => ((p.1 : ℕ) : ℤ)) ++
    I.map (fun p => ((p.2 : ℕ) : ℤ))

/-- The state of the program `Alg` after `t` steps on the PSP instance `(G, k, I)` and coin tape `tape`. -/
noncomputable def pspState (Alg : RealAPSP.Program) (G : Graph) (k : ℕ)
    (I : List (Fin G.n × Fin G.n)) (tape : ℕ → Bool) (t : ℕ) : RealAPSP.State :=
  RealAPSP.stateAt Alg (pspWidth G k I) tape (pspInts G k I) (prepReals G) t

/-- `Alg` solves the PSP instance `(G, k, I)` with per-pair guarantee `Good u v d̂` on every coin tape,
and within `T` steps with probability at least `1 − fail`. The estimate for the `j`-th pair is real cell
`routCell j` of the halted state. -/
def RunsPSP (Alg : RealAPSP.Program) (G : Graph) (k : ℕ) (I : List (Fin G.n × Fin G.n))
    (Good : Fin G.n → Fin G.n → ℝ → Prop) (T fail : ℝ) : Prop :=
  ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - fail) ≤ RealAPSP.coinTape E ∧
    ∀ tape : ℕ → Bool, ∃ t : ℕ, (pspState Alg G k I tape t).halted = true ∧
      (∀ j : Fin I.length, Good (I.get j).1 (I.get j).2
        ((pspState Alg G k I tape t).rmem (RealAPSP.routCell j))) ∧
      (tape ∈ E → (t : ℝ) ≤ T)

end TZLevelsADO.Supplement


