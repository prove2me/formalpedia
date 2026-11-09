-- Prove2me | Definitions.Def_ProportionalGroupDivision_Main_Machine
-- name    : ProportionalGroupDivision_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:57.790806+00:00
-- url     : https://prove2.me/theorems/1e40a303-f1eb-4f03-9ef7-e793e5b1c3e7
-- title:
--   Randomized real-arithmetic programs (Theorem 2, footnote 1; Corollary 20)
-- statement:
--   The paper says that the allocation of its upper bound "can be computed in randomized polynomial time", the randomness being used for the random walk of Lovett–Meka, and that the algorithm of Corollary 20 "runs in time $\mathrm{poly}(n,m,\delta^{-1})$"; the inputs are real numbers and no machine is specified. These running times are read on the published randomized real RAM `PolySampIso` (exact real registers and memory, integer pointer registers, unit cost per instruction), restricted to the following fragment:
--
--   1. exact $+,-,\times,\div$ on reals, rational literals, indirect load and store, pointer set, copy, increment and decrement, comparison jumps, a pointer-to-real cast;
--   2. $\sqrt{\cdot}$;
--   3. draws of independent standard Gaussians $\mathcal N(0,1)$;
--   4. halt.
--
--   The instructions $\exp$, $\log$ and the exponential draw of `PolySampIso` are excluded. No instruction selects an allocation, rounds a vector or solves a search problem.
--
--   An input is placed in the initial state: integers in the pointer registers and reals in the memory cells $0,1,\dots$; the output is read from memory cells $-1,-2,\dots$ of the first halted state. Two input layouts are fixed: for Corollary 20, pointers $(N,m)$ and memory $A$ (row by row), $c_1,\dots,c_N$, $x$, $\delta$; for Theorem 2, pointers $(k,m,n_1,\dots,n_k)$ and memory the valuations $\mu_{(i,j)}(g)$, agents in lexicographic order and each agent's $m$ values in order of the goods.
--
--   **Formalization Note** A program is one finite instruction list chosen before every input. `HaltsWithin P s₀ ω T` says that the run on the random streams $\omega$ halts after at most $T$ executed instructions; the probability law of $\omega$ is the published `PolySampIso.tape`.
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 2 and footnote 1, PDF p. 2; Theorem 5 and Corollary 20, PDF pp. 5 and 20; Appendix A, PDF p. 24 (printed pages equal)

import Mathlib
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_ProportionalGroupDivision_Main_Model

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-!
# Randomized real-arithmetic algorithms (Theorem 2 with footnote 1, p. 2; Corollary 20, p. 20)

The paper states running times ("randomized polynomial time", "runs in time poly(n, m, δ⁻¹)")
for algorithms on real inputs without fixing a machine. They are read on the published randomized
real RAM `PolySampIso` (exact real registers and memory indexed by `ℤ`, integer pointer
registers; the published `SmaleNinth` core of exact `+ − × ÷`, rational literals, indirect
load/store, pointer set/copy/increment/decrement and comparison jumps; a pointer-to-real cast;
`√`; draws of i.i.d. standard Gaussians; `halt`; unit cost per executed instruction), restricted to
the fragment below: the instructions `exp`, `log` and the exponential draw `expo` are excluded, so
the only primitives are exact arithmetic, comparisons, square roots, integer indexing and loops,
and standard Gaussian draws (the random walk primitive of [LM12]). No instruction selects an
allocation, rounds a vector or solves a search problem.

A program is one finite list of instructions, chosen before every input. An input is placed in
the initial state (`initState`): a list of integers in the pointer registers `p[0], p[1], …` and a
list of reals in the memory cells `0, 1, …`. The output is read from the memory cells
`−1, −2, …` of the first halted state.
-/

/-- The program uses only the fragment: rational literals, no core `accept`/`reject`
(`PolySampIso.Admissible`), and no `exp`, `log` or `expo` instruction. -/
def InFragment (P : PolySampIso.Program) : Prop :=
  PolySampIso.Admissible P ∧
    ∀ op ∈ P, match op with
      | .exp _ _ => False
      | .log _ _ => False
      | .expo _ => False
      | _ => True

/-- The initial state for integer data `ptrs` (pointer register `q` holds `ptrs[q]`, `0` beyond)
and real data `reals` (memory cell `a ≥ 0` holds `reals[a]`, every other cell `0`); program
counter, registers, stream cursors and work are `0`. -/
noncomputable def initState (ptrs : List ℤ) (reals : List ℝ) : PolySampIso.State :=
  ⟨⟨0, fun _ => 0, fun q => ptrs.getD q 0,
      fun a => if 0 ≤ a then reals.getD a.toNat 0 else 0⟩, 0, 0, false, 0⟩

/-- The run of `P` from `s₀` on the random streams `ω` halts within `T` steps (each step is one
executed instruction of unit cost). -/
def HaltsWithin (P : PolySampIso.Program) (s₀ : PolySampIso.State) (ω : PolySampIso.Streams)
    (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ (PolySampIso.run P s₀ ω t).halted = true

/-- The first halted state of the run (read at `PolySampIso.haltTime`). -/
noncomputable def finalState (P : PolySampIso.Program) (s₀ : PolySampIso.State)
    (ω : PolySampIso.Streams) : PolySampIso.State :=
  PolySampIso.run P s₀ ω (PolySampIso.haltTime P s₀ ω)

/-- Output cell `g` of a state: memory cell `−1 − g`. -/
def outCell (s : PolySampIso.State) (g : ℕ) : ℝ := s.core.mem (-1 - (g : ℤ))

/-- A matrix as a list of reals, row by row. -/
def matrixList {N m : ℕ} (A : Matrix (Fin N) (Fin m) ℝ) : List ℝ :=
  (List.ofFn fun i => List.ofFn (A i)).flatten

/-- Corollary 20's input: pointers `[N, m]`; memory holds `A ∈ ℝ^{N×m}` row by row, then
`c_1, …, c_N`, then `x ∈ ℝ^m`, then `δ`. -/
noncomputable def lmInput {N m : ℕ} (A : Matrix (Fin N) (Fin m) ℝ) (c : Fin N → ℝ)
    (x : Fin m → ℝ) (δ : ℝ) : PolySampIso.State :=
  initState [(N : ℤ), (m : ℤ)] (matrixList A ++ List.ofFn c ++ List.ofFn x ++ [δ])

/-- Theorem 2's input: pointers `[k, m, n_1, …, n_k]`; memory holds the valuations
`μ_{(i,j)}(g)`, agents in lexicographic order `(i, j)`, each agent's `m` values in good order. -/
noncomputable def fdInput {k : ℕ} (n : Fin k → ℕ) {m : ℕ} (μ : Valuation n m) :
    PolySampIso.State :=
  initState ([(k : ℤ), (m : ℤ)] ++ List.ofFn (fun i => (n i : ℤ)))
    (List.ofFn fun i => (List.ofFn fun j => List.ofFn (μ i j)).flatten).flatten

end ProportionalGroupDivision.Main


