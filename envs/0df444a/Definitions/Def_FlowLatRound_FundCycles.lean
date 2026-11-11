-- Prove2me | Definitions.Def_FlowLatRound_FundCycles
-- name    : FlowLatRound_FundCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:28.142357+00:00
-- url     : https://prove2.me/theorems/fcabef7c-32dd-419e-a451-76b5e656be2f
-- title:
--   §3.1 and App. C — the fundamental-cycle matrix $C_T$, computed by a charged program
-- statement:
--   For a multigraph $G$ and spanning tree $T$, the fundamental-cycle matrix $C_T\in\{0,\pm1\}^{m\times d}$ has one column per non-tree edge $e$ (in increasing order): the signed indicator vector of the cycle $C(T,e)$ with entry $+1$ at $e$, i.e. one unit of flow along $e$ returned to its tail along the tree path. The program finds the path by breadth-first search in $T$ and is the last step of the basis sampler of Theorem 1.1.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), §3.1, p.6 (PDF 8); Appendix C opening, p.22 (PDF 24)

import Mathlib
import Definitions.Def_FlowLatRound_FlowGraph
import Definitions.Def_FlowLatRound_CostModel

namespace FlowLatRound

/-! # The fundamental-cycle matrix `C_T`

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), §3.1, p.6 (PDF 8: "The signed indicator vectors of the d
fundamental cycles C(T, e), e ∉ T, form a basis of Λ_G"); Appendix C opening, p.22 (PDF 24:
"C_T ∈ {0, ±1}^{m×d} … whose column for a non-tree edge e is the signed indicator vector of
C(T, e) with entry +1 at e").

**Formalization Note.** The matrix is computed by a charged program (it is also the last step
of the sampler). The non-tree edges are taken in increasing index order; column `j` belongs to
the `j`-th of them, `e`. A breadth-first search in `T` from `src e` gives parent pointers; walking
from `dst e` up to `src e`, every tree edge `f` traversed from `x` to `y` gets `+1` if it is
oriented `x → y` and `−1` otherwise, and `e` gets `+1`. This is the signed indicator vector of
`C(T, e)` oriented along `e` (a unit of flow along `e` returned along the tree path); a loop gives
the indicator of `e`. A table `Fin k → α` held by the program (including the graph's `src`,
`dst`) is an array: reading or writing an entry costs one step. -/

namespace MGraph

variable {n m : ℕ} (G : MGraph n m)

/-- One breadth-first round in `T`: scan every frontier vertex against every tree edge and
record unvisited neighbours with their parent edge. -/
def bfsRoundC (Tl : List (Fin m)) (frontier : List (Fin n))
    (st : List (Fin n) × (Fin n → Bool) × (Fin n → Option (Fin m × Fin n))) :
    Counted (List (Fin n) × (Fin n → Bool) × (Fin n → Option (Fin m × Fin n))) := do
  -- per (frontier vertex, tree edge): two array reads, four index comparisons, two writes
  charge (frontier.length * Tl.length * (4 * opCost (max n m) (max n m) + 6))
  pure <| frontier.foldl (fun acc x => Tl.foldl (fun (acc : List (Fin n) × (Fin n → Bool) ×
      (Fin n → Option (Fin m × Fin n))) f =>
      let y? : Option (Fin n) :=
        if G.src f = x then some (G.dst f) else if G.dst f = x then some (G.src f) else none
      match y? with
      | some y =>
          if acc.2.1 y then acc
          else (acc.1 ++ [y], Function.update acc.2.1 y true,
            Function.update acc.2.2 y (some (f, x)))
      | none => acc) acc) st

/-- Breadth-first search in `T` (at most `fuel` rounds). -/
def bfsLoopC (Tl : List (Fin m)) : ℕ → List (Fin n) → (Fin n → Bool) →
    (Fin n → Option (Fin m × Fin n)) → Counted (Fin n → Option (Fin m × Fin n))
  | 0, _, _, par => pure par
  | fuel + 1, frontier, vis, par => do
      charge 1
      if frontier.isEmpty then pure par
      else do
        let st ← G.bfsRoundC Tl frontier ([], vis, par)
        bfsLoopC Tl fuel st.1 st.2.1 st.2.2

/-- Parent pointers of the breadth-first search tree of `T` rooted at `r`: `par v = (f, u)`
means `v` was reached from `u` along the tree edge `f`. -/
def treeParentsC (T : Finset (Fin m)) (r : Fin n) : Counted (Fin n → Option (Fin m × Fin n)) := do
  charge (m * opCost m m + n + 1)
  let Tl := (List.finRange m).filter (· ∈ T)
  G.bfsLoopC Tl (n + 1) [r] (fun v => decide (v = r)) (fun _ => none)

/-- Walk up the parent pointers from `x` (at most `fuel` steps), recording `(f, from, to)`. -/
def walkUpC (par : Fin n → Option (Fin m × Fin n)) :
    ℕ → Fin n → Counted (List (Fin m × Fin n × Fin n))
  | 0, _ => pure []
  | fuel + 1, x => do
      charge 1
      match par x with
      | none => pure []
      | some (f, y) => do
          let rest ← walkUpC par fuel y
          pure ((f, x, y) :: rest)

/-- The signed indicator vector of the fundamental cycle `C(T, e)`, with `+1` at `e`. -/
def fundColC (T : Finset (Fin m)) (e : Fin m) : Counted (Fin m → ℤ) := do
  let par ← G.treeParentsC T (G.src e)
  let path ← walkUpC par (n + 1) (G.dst e)
  charge ((path.length + 1) * (2 * opCost (max n m) (max n m) + 4))
  pure <| path.foldl
    (fun z (p : Fin m × Fin n × Fin n) =>
      Function.update z p.1 (if G.src p.1 = p.2.1 ∧ G.dst p.1 = p.2.2 then 1 else -1))
    (Function.update (fun _ => 0) e 1)

/-- The fundamental-cycle matrix `C_T ∈ ℤ^{m × (m − n + 1)}`: column `j` is the signed
fundamental cycle of the `j`-th non-tree edge (in increasing index order). -/
def fundMatrixC (T : Finset (Fin m)) : Counted (Fin m → Fin (m + 1 - n) → ℤ) := do
  charge (m * opCost m m + 1)
  let nt := (List.finRange m).filter (· ∉ T)
  let cols ← nt.mapM (G.fundColC T)
  charge (m * (cols.length + 1))
  pure (fun e j => (cols.getD j.1 (fun _ => 0)) e)

/-- The fundamental-cycle matrix `C_T` (the output of `fundMatrixC`). -/
def fundMatrix (T : Finset (Fin m)) : Fin m → Fin (m + 1 - n) → ℤ :=
  (G.fundMatrixC T).run' 0

end MGraph

end FlowLatRound


