-- Prove2me | Definitions.Def_MinColorPath_MinorFree_Machine
-- name    : MinColorPath_MinorFree_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:10:31.314775+00:00
-- url     : https://prove2.me/theorems/23c96549-6829-40bf-bc0e-1e09549accb4
-- title:
--   Input code and output cells of Min-Color Path on the published word RAM
-- statement:
--   The machine is the published deterministic word RAM (`TrulySubcubicAPSP_WordRAM`): instructions one, add, sub, mul (modulo $2^W$), indirect load and store, branch on negative, accept, reject; every executed instruction, the halting one included, costs one step. An instance $(G,\mathrm{cl},s,t)$ with $G$ on $\{0,\dots,n-1\}$ and palette $\{0,\dots,p-1\}$ is written in the memory as the words
--   $$n,\ p,\ s,\ t,\ \big(\deg(v),\ \text{neighbours of } v\big)_{v=0}^{n-1},\ \big(|\mathrm{cl}(v)|,\ \text{colors of } v\big)_{v=0}^{n-1},$$
--   each list without repetition and in an arbitrary order. The answer is read from the cells directly after the input: the number $\ell$ of vertices followed by the vertices of a path, or the single word $-1$. Word widths $W\ge b(\lfloor\log_2N\rfloor+1)$ are admissible for the program's constant $b$.
--
--   **Formalization Note.** `InputCode G cl` carries the adjacency and color lists with their specification; `I.words s t` is the word list; `CellsHold`, `OutputsList` and `OutputsNoPath` read the memory as signed integers (`BitVec.toInt`); `WideEnough b N W` is $b(\lfloor\log_2 N\rfloor+1)\le W$. Statements quantify over every code, i.e. every order of every list.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 1, problem Min-Color Path (the paper fixes no machine or format; this is the mission's reading)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

/-!
# Input code and output cells for Min-Color Path on the published word RAM

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), p. 1 (the problem Min-Color Path; the paper fixes no
machine and no input format).

The machine is the published deterministic word RAM `TrulySubcubicAPSP.exec` / `loadWords`
(unit cost per executed instruction, the halting one included). This file fixes the reading of
the instance and of the answer.

* **Input.** An instance is a graph `G` on `Fin n`, a coloring `cl : Fin n → Finset (Fin p)` and
  `s, t : Fin n`. Its code is the word list `n, p, s, t`, then for every vertex `v` (in the order
  `0, …, n − 1`) the degree of `v` followed by its neighbours, then for every vertex the number of
  its colors followed by its colors. Each adjacency list and each color list is duplicate-free and
  may be in **any** order; statements quantify over every such code (`InputCode`).
* **Output.** The answer is read from the cells right after the input (address `L`): either `ℓ`
  followed by the `ℓ` vertices of a path, or the single word `−1` (no path). Cells are read as
  signed integers (`BitVec.toInt`).
-/

namespace MinColorPath.MinorFree

open TrulySubcubicAPSP

/-- A code of the instance `(G, cl)`: an adjacency list and a color list for every vertex,
duplicate-free, in any order. -/
structure InputCode {n p : ℕ} (G : SimpleGraph (Fin n)) (cl : Fin n → Finset (Fin p)) where
  /-- The neighbours of `v`, in some order. -/
  adj : Fin n → List (Fin n)
  /-- The colors of `v`, in some order. -/
  col : Fin n → List (Fin p)
  adj_spec : ∀ v, (adj v).Nodup ∧ ∀ u, u ∈ adj v ↔ G.Adj v u
  col_spec : ∀ v, (col v).Nodup ∧ ∀ τ, τ ∈ col v ↔ τ ∈ cl v

/-- The input words of the code `I` with terminals `s, t`. -/
def InputCode.words {n p : ℕ} {G : SimpleGraph (Fin n)} {cl : Fin n → Finset (Fin p)}
    (I : InputCode G cl) (s t : Fin n) : List Int :=
  [(n : Int), (p : Int), (s.val : Int), (t.val : Int)] ++
    (List.finRange n).flatMap (fun v => ((I.adj v).length : Int) :: (I.adj v).map fun u => (u.val : Int)) ++
    (List.finRange n).flatMap (fun v => ((I.col v).length : Int) :: (I.col v).map fun τ => (τ.val : Int))

/-- The cells from address `L` on hold the words `ws` (read as signed integers). -/
def CellsHold {W : ℕ} (m : Int → BitVec W) (L : ℕ) (ws : List Int) : Prop :=
  ∀ k (hk : k < ws.length), (m ((L + k : ℕ) : Int)).toInt = ws[k]

/-- The output cells from address `L` hold the vertex list `l` of a path: `|l|` followed by the
vertices of `l` in order. -/
def OutputsList {W n : ℕ} (m : Int → BitVec W) (L : ℕ) (l : List (Fin n)) : Prop :=
  CellsHold m L ((l.length : Int) :: l.map fun v => (v.val : Int))

/-- The output cell at address `L` holds the no-path marker `−1`. -/
def OutputsNoPath {W : ℕ} (m : Int → BitVec W) (L : ℕ) : Prop :=
  (m (L : Int)).toInt = -1

/-- The admissible word widths for size parameter `N` and constant `b`: `W ≥ b (⌊log₂ N⌋ + 1)`. -/
def WideEnough (b N W : ℕ) : Prop := b * (Nat.log2 N + 1) ≤ W

end MinColorPath.MinorFree


