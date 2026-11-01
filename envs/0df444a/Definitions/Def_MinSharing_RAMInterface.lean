-- Prove2me | Definitions.Def_MinSharing_RAMInterface
-- name    : MinSharing_RAMInterface
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:57.781864+00:00
-- url     : https://prove2.me/theorems/9aa9e154-b51f-4962-8bc0-8150eb09c52f
-- title:
--   Real-RAM input/output conventions: instance memory, output allocation, deciding, enumerating graphs
-- statement:
--   The algorithmic statements of the mission are about programs of the published real RAM (`SmaleNinth.RAMProgram`): exact real arithmetic, integer pointers, a memory indexed by $\mathbb Z$, and unit cost per executed instruction. An algorithm "using $O(f)$ operations" is a single program $R$ and a constant $K>0$ such that $R$ halts within $K\cdot f$ steps with a correct output. This module fixes how inputs are laid out and outputs are read:
--
--   1. **Instance memory**: cell $0$ holds $n$, cell $1$ holds $m$, cell $2+i m+o$ holds $v_{i,o}$, all other cells hold $0$. For a pair $(v,z)$ the share $z_{i,o}$ is also placed in cell $2+nm+im+o$.
--   2. **List of graphs** (input of Lemma 3.9(b)): additionally $k$ in cell $2+nm$, the length $N$ of the list in cell $3+nm$, and the $g$-th graph (on agents $0,\dots,k-1$) as $0/1$ entries in cells $4+nm+g\,nm+im+o$.
--   3. **Output allocation**: the share $z_{i,o}$ is read from cell $-(1+im+o)$ when $R$ halts.
--   4. **Graph region**: the current graph of an enumeration has edge $(i,o)$ iff cell $-(1+nm+im+o)$ holds $1$.
--   5. **Halting with an output** within $T$ steps: some $t\le T$ reaches the accept instruction and the output allocation then satisfies the required property. **Deciding** within $T$ steps: halting by accept or reject within $T$ steps, accepting exactly when the property holds.
--   6. **Enumerating** a set $S$ of graphs within $T$ steps with report position $p$: $R$ halts by accepting at some $t_0\le T$; at every step $t<t_0$ at which the program counter equals $p$ the graph region holds a graph of $S$; and every graph of $S$ is held there at some such step (repetitions allowed).
--
--   The enumeration convention lets an algorithm update the current graph in place, so its running time can be proportional to the number of graphs rather than to the total size of their descriptions, as in the paper's Lemma 3.8(b).
--
--   **Formalization Note** Because the machine is a deep embedding, "there exists a program" cannot hide uncharged computation; correctness of the output is part of every algorithmic statement. All addresses are integers; the regions above are pairwise disjoint.
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 2.2 p.9, Lemma 2.5 p.11, Theorem 3.6(a) p.14, Proposition 3.7 p.15, Lemmas 3.8–3.9 pp.16–17 ("operations", "enumerated", "if G_v^k is given as the input")

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false

namespace MinSharing

open SmaleNinth

/-! Input and output conventions for the algorithmic claims of arXiv:1908.01669v3 (Lemmas 2.2, 2.5,
3.8, 3.9, Proposition 3.7, Theorem 3.6(a)), on the published real RAM `SmaleNinth.RAMProgram`:
unit cost per executed instruction, real registers, integer pointers, memory `ℤ → ℝ`.
"`O(f)` operations" is a bound `K · f` on the number of executed instructions. -/

/-- Memory cell of the value `vᵢ,ₒ`: `2 + i·m + o`. -/
def vCell (m : ℕ) (i o : ℕ) : ℤ := 2 + (i : ℤ) * m + o

/-- Memory cell of the share `zᵢ,ₒ` of an input allocation: `2 + n·m + i·m + o`. -/
def zCell (n m : ℕ) (i o : ℕ) : ℤ := 2 + (n : ℤ) * m + (i : ℤ) * m + o

/-- Memory cell of the output share `zᵢ,ₒ`: `−(1 + i·m + o)`. -/
def outCell (m : ℕ) (i o : ℕ) : ℤ := -(1 + (i : ℤ) * m + o)

/-- Memory cell of the edge `(i, o)` of the current graph of an enumeration:
`−(1 + n·m + i·m + o)`. -/
def graphCell (n m : ℕ) (i o : ℕ) : ℤ := -(1 + (n : ℤ) * m + (i : ℤ) * m + o)

/-- The input memory of an instance `v` with `n` agents and `m` objects: cell `0` holds `n`,
cell `1` holds `m`, cell `2 + i·m + o` holds `vᵢ,ₒ`, every other cell holds `0`. -/
noncomputable def instanceMem {n m : ℕ} (v : Fin n → Fin m → ℝ) (a : ℤ) : ℝ :=
  (if a = 0 then (n : ℝ) else 0) + (if a = 1 then (m : ℝ) else 0) +
    ∑ i : Fin n, ∑ o : Fin m, if a = vCell m i o then v i o else 0

/-- The input memory of a pair (instance `v`, allocation `z`): `instanceMem v` together with
`zᵢ,ₒ` in cell `2 + n·m + i·m + o`. -/
noncomputable def pairMem {n m : ℕ} (v z : Fin n → Fin m → ℝ) (a : ℤ) : ℝ :=
  instanceMem v a + ∑ i : Fin n, ∑ o : Fin m, if a = zCell n m i o then z i o else 0

/-- The input memory of Lemma 3.9(b): the instance `v` (`n` agents), the number `k` in cell
`2 + n·m`, the length `N` of the list `Gs` in cell `3 + n·m`, and the `g`-th graph of `Gs`
(a graph on agents `0, …, k−1` and the `m` objects) as `0/1` entries: cell
`4 + n·m + g·(n·m) + i·m + o` holds `1` iff `(i, o)` is an edge of `Gs[g]`. -/
noncomputable def graphListMem {n m : ℕ} (v : Fin n → Fin m → ℝ) (k : ℕ)
    (Gs : List (Finset (Fin k × Fin m))) (a : ℤ) : ℝ :=
  instanceMem v a + (if a = 2 + (n : ℤ) * m then (k : ℝ) else 0) +
    (if a = 3 + (n : ℤ) * m then (Gs.length : ℝ) else 0) +
    ∑ g : Fin Gs.length, ∑ i : Fin k, ∑ o : Fin m,
      if a = 4 + (n : ℤ) * m + (g : ℤ) * ((n : ℤ) * m) + (i : ℤ) * m + o ∧ (i, o) ∈ Gs.get g
      then 1 else 0

/-- The allocation written in the output region of a memory: `zᵢ,ₒ` is read from
`outCell m i o`. -/
def outputAlloc (n m : ℕ) (mem : ℤ → ℝ) : Fin n → Fin m → ℝ :=
  fun i o => mem (outCell m i o)

/-- The graph (on `k` agent rows and `m` objects) held in the graph region of a memory: `(i, o)` is
an edge iff `graphCell n m i o` holds `1`. -/
noncomputable def decodeGraph (n m k : ℕ) (mem : ℤ → ℝ) : Finset (Fin k × Fin m) :=
  Finset.univ.filter fun p => mem (graphCell n m p.1 p.2) = 1

/-- `R`, started on input memory `x`, **halts (accepting) within `T` steps with an output
allocation satisfying `P`**: some step count `t ≤ T` reaches the `accept` instruction, and the
allocation read from the output region at that moment satisfies `P`. -/
def HaltsWithOutputWithin (n m : ℕ) (R : RAMProgram) (x : ℤ → ℝ) (T : ℝ)
    (P : (Fin n → Fin m → ℝ) → Prop) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ RAMHaltedWith R (RAMRun R x t) true ∧
    P (outputAlloc n m (RAMRun R x t).mem)

/-- `R` **decides** the property `Q` on input `x` within `T` steps: it halts within `T` steps,
accepting if `Q` holds and rejecting otherwise. -/
def DecidesWithin (R : RAMProgram) (x : ℤ → ℝ) (T : ℝ) (Q : Prop) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ ∃ b : Bool, RAMHaltedWith R (RAMRun R x t) b ∧ (b = true ↔ Q)

/-- `R` **enumerates** the set `S` of graphs (on `k` agent rows) within `T` steps, with report
position `p` (the reading of "enumerate" used for Lemmas 3.8(b), 3.9(b) and Proposition 3.7):
`R` halts (accepting) at some step `t₀ ≤ T`; at every step `t < t₀` at which the program counter
is `p`, the graph region holds a graph of `S` (soundness); and every graph of `S` is held by the
graph region at some step `t < t₀` at which the program counter is `p` (completeness).
Repetitions are allowed. -/
noncomputable def EnumeratesWithin (n m k : ℕ) (R : RAMProgram) (p : ℕ) (x : ℤ → ℝ)
    (S : Set (Finset (Fin k × Fin m))) (T : ℝ) : Prop :=
  ∃ t₀ : ℕ, (t₀ : ℝ) ≤ T ∧ RAMHaltedWith R (RAMRun R x t₀) true ∧
    (∀ t < t₀, (RAMRun R x t).pc = p → decodeGraph n m k (RAMRun R x t).mem ∈ S) ∧
    ∀ G ∈ S, ∃ t < t₀, (RAMRun R x t).pc = p ∧ decodeGraph n m k (RAMRun R x t).mem = G

end MinSharing


