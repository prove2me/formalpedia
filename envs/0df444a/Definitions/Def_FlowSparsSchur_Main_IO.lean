-- Prove2me | Definitions.Def_FlowSparsSchur_Main_IO
-- name    : FlowSparsSchur_Main_IO
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:23:45.855407+00:00
-- url     : https://prove2.me/theorems/5b0dbc5a-ce6f-4a18-8e0a-e122629c722a
-- title:
--   Input layout and output decoding of graphs on the randomized real RAM, and rpow-free programs
-- statement:
--   The paper's "randomized algorithm" is read as a program of the randomized exact real RAM `PNormReg_Machine` (unit cost per instruction, rational literals, fair coin tape, no floor). This definition fixes how a graph is handed to a program and read back.
--
--   **Input.** For a graph $G$ on $\{0,\dots,n-1\}$ with edges $e=0,\dots,m-1$ and a list $s_0,\dots,s_{k-1}$ of terminals, integer memory holds, from cell $0$, the numbers $n,m,k$, then $\mathrm{src}(e),\mathrm{dst}(e)$ for every edge in order, then $s_0,\dots,s_{k-1}$. Real memory holds one real per edge in order (capacities in Theorem 1.1, conductances in Lemma 4.1), followed by the call's real parameters ($\xi,\delta$ in Lemma 4.1). The terminal set is $S=\{s_0,\dots,s_{k-1}\}$.
--
--   **Output.** After halting, integer cell $-1$ holds the number $r$ of output edges; edge $t<r$ has endpoints in integer cells $-2-2t$ and $-3-2t$ (vertex numbers of $G$) and its weight in real cell $-1-t$. The output is a graph on $S$ if $r\ge0$ and every endpoint is a terminal; the decoded graph has vertex set $S$ and these $r$ edges, the weight read as the capacity (Theorem 1.1) or as the conductance (Lemma 4.1). A program is **rpow-free** if it contains no `rpow` instruction.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 1, Theorem 1.1; p. 15, Lemma 4.1 (the paper names no machine; reading of the mission)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_FlowSparsSchur_Main_Graph

/-!
# Input layout and output decoding on the randomized real RAM

Goranci, Henzinger, Momeni, Räcke, Sricharan, *Breaking the Quadratic Time Barrier for Flow
Sparsifiers via Schur Complement Localization*, STOC 2027 submission, Theorem 1.1 (p. 1) and
Lemma 4.1 (p. 15). The paper names no machine; the mission reads "algorithm" as a program of the
published randomized exact real RAM `PNormReg` (`Definitions.Def_PNormReg_Machine`).

**Input.** Integer memory, from cell `0`: `n, m, k`, then the endpoints `src e, dst e` of the edges
`e = 0, …, m − 1` in order, then the terminals `s 0, …, s (k − 1)`. Real memory, from cell `0`: one
real per edge in the same order (capacities for Theorem 1.1, conductances for Lemma 4.1), followed by
the extra real parameters of the call (`ξ, δ` for Lemma 4.1).

**Output.** After `halt`: integer cell `−1` holds the number `r` of output edges; output edge
`t < r` has endpoints in integer cells `−2 − 2t` and `−3 − 2t` (vertex numbers of `G`) and weight in
real cell `−1 − t`. The output graph has vertex set exactly the terminal set `S`.

`NoRpow P`: the program never executes the machine's `rpow` instruction (none occurs in it).
-/

namespace FlowSparsSchur.Main

open PNormReg

/-- The program contains no `rpow` instruction. -/
def NoRpow (P : Program) : Prop := ∀ op ∈ P, ∀ d a b : ℕ, op ≠ Instr.rpow d a b

/-- The terminal set `S = {s 0, …, s (k − 1)}`. -/
def termSet {n k : ℕ} (s : Fin k → Fin n) : Finset (Fin n) := Finset.univ.image s

/-- Integer input: `n, m, k`, the edge endpoints in edge order, the terminals in order. -/
def inputInts (n m k : ℕ) (G : CGraph (Fin n) (Fin m)) (s : Fin k → Fin n) : List ℤ :=
  [(n : ℤ), (m : ℤ), (k : ℤ)] ++
    (List.finRange m).flatMap (fun e => [((G.src e : ℕ) : ℤ), ((G.dst e : ℕ) : ℤ)]) ++
    (List.finRange k).map (fun i => ((s i : ℕ) : ℤ))

/-- The edge capacities in edge order. -/
noncomputable def capList {n m : ℕ} (G : CGraph (Fin n) (Fin m)) : List ℝ :=
  (List.finRange m).map G.cap

/-- The edge conductances in edge order. -/
noncomputable def condList {n m : ℕ} (G : CGraph (Fin n) (Fin m)) : List ℝ :=
  (List.finRange m).map G.cond

/-- Number of output edges: integer cell `−1`. -/
def outCount (st : State) : ℤ := st.integerMemory (-1)

/-- First endpoint of output edge `t`: integer cell `−2 − 2t`. -/
def outEnd1 (st : State) (t : ℕ) : ℤ := st.integerMemory (-2 - 2 * (t : ℤ))

/-- Second endpoint of output edge `t`: integer cell `−3 − 2t`. -/
def outEnd2 (st : State) (t : ℕ) : ℤ := st.integerMemory (-3 - 2 * (t : ℤ))

/-- Weight of output edge `t`: real cell `−1 − t`. -/
noncomputable def outWeight (st : State) (t : ℕ) : ℝ := st.core.mem (-1 - (t : ℤ))

/-- The output lists a graph on the terminal set `S`: `r ≥ 0` and both endpoints of every output
edge are (numbers of) terminals. -/
def OutOnTerminals {n : ℕ} (S : Finset (Fin n)) (st : State) : Prop :=
  0 ≤ outCount st ∧ ∀ t : ℕ, (t : ℤ) < outCount st →
    (∃ v ∈ S, ((v : ℕ) : ℤ) = outEnd1 st t) ∧ (∃ v ∈ S, ((v : ℕ) : ℤ) = outEnd2 st t)

/-- No output edge is a self-loop. -/
def OutNoLoops (st : State) : Prop :=
  ∀ t : ℕ, (t : ℤ) < outCount st → outEnd1 st t ≠ outEnd2 st t

/-- The terminal named by the integer `z`, given that `z` names one. -/
noncomputable def decodeTerm {n : ℕ} (S : Finset (Fin n)) (z : ℤ)
    (h : ∃ v ∈ S, ((v : ℕ) : ℤ) = z) : S :=
  ⟨h.choose, h.choose_spec.1⟩

/-- The output graph on `S` whose edge weights are capacities (conductances `1`, unused):
output edge `t` joins `outEnd1 t` and `outEnd2 t` with capacity `outWeight t`. -/
noncomputable def outCapGraph {n : ℕ} (S : Finset (Fin n)) (st : State)
    (h : OutOnTerminals S st) : CGraph S (Fin (outCount st).toNat) where
  src t := decodeTerm S (outEnd1 st t) ((h.2 t (by have := t.isLt; omega)).1)
  dst t := decodeTerm S (outEnd2 st t) ((h.2 t (by have := t.isLt; omega)).2)
  cap t := outWeight st t
  cond _ := 1

/-- The output graph on `S` whose edge weights are conductances (capacities `1`, unused). -/
noncomputable def outCondGraph {n : ℕ} (S : Finset (Fin n)) (st : State)
    (h : OutOnTerminals S st) : CGraph S (Fin (outCount st).toNat) where
  src t := decodeTerm S (outEnd1 st t) ((h.2 t (by have := t.isLt; omega)).1)
  dst t := decodeTerm S (outEnd2 st t) ((h.2 t (by have := t.isLt; omega)).2)
  cap _ := 1
  cond t := outWeight st t

end FlowSparsSchur.Main


