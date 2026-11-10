-- Prove2me | Definitions.Def_VecKnapsackMitM_Main_Machine
-- name    : VecKnapsackMitM_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:33:33.766214+00:00
-- url     : https://prove2.me/theorems/0da2dbb3-1382-4702-9d99-0dc9b7424f40
-- title:
--   Deterministic real-RAM runs, the d-Knapsack input/output layout and the time bound of Theorem 1.1
-- statement:
--   The computation model for "runs in time $T$". Programs are those of the published unit-cost real RAM `MatMulTimeLP` (real cells $R$, index cells $N$; exact $+,-,\times,\div$ on reals, $+$ and truncated $-$ on indices, indirect loads and stores, `<`-jumps, `halt`), restricted by the published `VecBalPoly.Admissible` (rational real literals, no $\sqrt{\ }$, no random draws). The machine has no floor, no real-to-index conversion and no index multiplication.
--
--   * `run P s₀ t`: the state after $t$ steps of $P$ from the state $s_0$ (the random tape is the zero tape, never read by an admissible program).
--   * `initState2 reals nats`: program counter $0$, $R[i]$ the $i$-th real, $N[i]$ the $i$-th natural, every other cell $0$.
--   * `RunsWithin P s₀ T Out`: some step $t$ with $t+1\le T$ (executed instructions plus the final halt) reaches a halted state, and that state satisfies `Out`.
--   * `itemsReals I`: $p(0),\bar w_0(0),\dots,\bar w_{d-1}(0),p(1),\dots$ (item $i$ occupies $d+1$ consecutive cells).
--   * `knapsackInput inst ε ρ`: $N[0]=d$, $N[1]=n$; $R[0]=\varepsilon$, $R[1]=\rho$, $R[2+t]=\bar W_{t+1}$, then the items.
--   * Output of a d-Knapsack program: the cells $N[2+i]$, $i<n$; `OutputBinary` says each is $0$ or $1$, and `outputSet` is $\{i: N[2+i]=1\}$.
--   * `NN n` $=N=\max(n,2)$, the reading of $n$ in bounds with a $\log n$ factor (INSIGHTS I1).
--   * `mainBound d n ε ρ C` $=\bigl(N^{\lceil (d-1)/(2\varepsilon)-1/2+\rho\rceil}+N^d\bigr)\cdot\bigl(d\log_2N/(\rho\varepsilon)\bigr)^{C\cdot d}$.
--
--   The helpers `zeroTape`, `run`, and `initState2` alias the published `ShadowBootstrap_stateFrom` definitions; `finVec` aliases `MatMulTimeLP.vecToList`. `RunsWithin` adds an output predicate to the published halting convention. No quantum-information condition from the transitive imports is used.
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; §2, printed p. 8 (PDF 9); Theorem 1.1, printed p. 2 (PDF 3)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_ShadowBootstrap_stateFrom
import Definitions.Def_VecKnapsackMitM_Main_Instance

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-! The computation model for "runs in time `T`" (Bringmann, Kulik, Węgrzycki 2026, §2, printed
p. 8, PDF 9: "We focus our presentation on the RealRAM"). Programs are those of the published
unit-cost real RAM `MatMulTimeLP` (real cells `R`, index cells `N`, exact `+ − × ÷` on reals,
`+` and truncated `−` on indices, indirect loads and stores, `<`-jumps, `halt`; one step per
executed instruction), restricted by the published `VecBalPoly.Admissible` (rational real
literals only, no `√`, no random draws), so a run is deterministic and the random tape is never
read. A run starts from a two-bank state: integer data in the index cells, real data in the
real cells, every other cell `0`. -/

/-- The all-zero random tape (never read by an admissible program). -/
abbrev zeroTape : Tape := ShadowBootstrap.zeroTape

/-- The state after `t` steps of `P` started in the state `s₀`. -/
noncomputable abbrev run := ShadowBootstrap.stateFrom

/-- The two-bank initial state: program counter `0`, `R[i] = reals[i]`, `N[i] = nats[i]`, every
other cell `0`. -/
noncomputable abbrev initState2 := ShadowBootstrap.initState2

/-- The run of `P` from `s₀` halts within time `T` with an output satisfying `Out`: some step
`t` with `t + 1 ≤ T` (the `t` executed instructions and the final `halt`, the published
`haltTime` convention) reaches a halted state, and that state satisfies `Out`. A halted state
never changes, so `Out` is a property of the final state. -/
def RunsWithin (P : Program) (s₀ : State) (T : ℝ) (Out : State → Prop) : Prop :=
  ∃ t : ℕ, IsHalted P (run P s₀ t) ∧ (t : ℝ) + 1 ≤ T ∧ Out (run P s₀ t)

/-- A real vector as a list, in coordinate order. -/
abbrev finVec := @MatMulTimeLP.vecToList

/-- The items as reals: for `i = 0, …, n − 1` in turn, `p(i), w_0(i), …, w_{d−1}(i)` (item `i`
occupies `d + 1` consecutive cells). -/
def itemsReals {d n : ℕ} (I : Items d n) : List ℝ :=
  (List.finRange n).flatMap fun i => I.p i :: finVec (I.w i)

/-- Input of the d-Knapsack algorithm: index cells `N[0] = d`, `N[1] = n`; real cells
`R[0] = ε`, `R[1] = ρ`, `R[2 + t] = W_t` (`t < d`), then the items (`itemsReals`) from
`R[2 + d]` on. -/
noncomputable def knapsackInput {d n : ℕ} (inst : Instance d n) (ε ρ : ℝ) : State :=
  initState2 ([ε, ρ] ++ finVec inst.W ++ itemsReals inst.toItems) [d, n]

/-- Every output cell `N[2 + i]`, `i < n`, of the state holds `0` or `1`. -/
def OutputBinary (s : State) (n : ℕ) : Prop := ∀ i < n, s.N (2 + i) = 0 ∨ s.N (2 + i) = 1

/-- The output set: the items `i` with `N[2 + i] = 1`. -/
def outputSet (s : State) (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => s.N (2 + i.val) = 1

/-- `N = max(n, 2)`, the reading of `n` in every bound with a `log n` factor (INSIGHTS I1:
`log 1 = 0` would make the bounds `0`). -/
noncomputable def NN (n : ℕ) : ℝ := max (n : ℝ) 2

/-- The running time of Theorem 1.1 and Lemma 4.7 with exponent constant `C`:
`(N^{⌈(d−1)/(2ε) − 1/2 + ρ⌉} + N^d) · (d · log₂ N / (ρ · ε))^{C · d}`, `N = max(n, 2)`. -/
noncomputable def mainBound (d n : ℕ) (ε ρ C : ℝ) : ℝ :=
  (NN n ^ (⌈((d : ℝ) - 1) / (2 * ε) - 1 / 2 + ρ⌉) + NN n ^ d) *
    ((d : ℝ) * Real.logb 2 (NN n) / (ρ * ε)) ^ (C * (d : ℝ))

end VecKnapsackMitM.Main


