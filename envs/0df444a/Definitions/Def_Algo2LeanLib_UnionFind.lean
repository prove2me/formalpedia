-- Prove2me | Definitions.Def_Algo2LeanLib_UnionFind
-- name    : Algo2LeanLib_UnionFind
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:00.964987+00:00
-- url     : https://prove2.me/theorems/bf2fc655-b8c5-47b6-86a6-04e91854981f
-- title:
--   Union-find model: forests, ranks, representatives and validity
-- statement:
--   `Algo2Lean.UnionFind.State n` contains four maps on `Fin n`: a parent map, natural ranks, proof-only component representatives and proof-only masses. `Connected` is equality of representatives. `initial n` is the singleton forest. `Find state vertex root steps` records a parent path with its number of nonroot edges. `compress` rewrites one parent to its representative; `link` joins two roots by the designated winner, increasing its rank on a tie; `union` chooses the winner by rank.
--
--   `Valid` requires that representatives are roots, roots represent themselves, parent edges preserve representatives, and every nonroot edge strictly increases rank. Root mass is at least $2^{rank}$; nonroot mass is zero and total mass is at most $n$. These accounting invariants establish finite paths and the logarithmic rank bound without assuming a specific prior execution history. Ghost representatives and masses are proof data, not additional mutable program fields.
--
--   This bundle is independent of generated code and graph algorithms. Mutable calls relate their parent/rank arrays to this model through the separate `UnionFindAnalysis.Rep` definition.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFind.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind

/-- Replace one entry of a finite map. -/
def update {n : Nat} {α : Type} (f : Fin n → α) (index : Fin n) (value : α) : Fin n → α :=
  fun vertex => if vertex = index then value else f vertex

@[simp] theorem update_same {n : Nat} {α : Type} (f : Fin n → α) (index : Fin n) (value : α) :
    update f index value index = value := by simp [update]

@[simp] theorem update_other {n : Nat} {α : Type} (f : Fin n → α)
    (index vertex : Fin n) (value : α) (different : vertex ≠ index) :
    update f index value vertex = f vertex := by simp [update, different]

/-- Sum a natural-valued finite map without importing additional libraries. -/
def total : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => f 0 + total (fun vertex => f vertex.succ)







/-- A parent forest with proof-only representatives and component masses. -/
structure State (n : Nat) where
  parent : Fin n → Fin n
  rank : Fin n → Nat
  representative : Fin n → Fin n
  mass : Fin n → Nat

/-- The structural and accounting facts needed by find and union proofs. -/
structure Valid {n : Nat} (state : State n) : Prop where
  representative_root : ∀ vertex, state.parent (state.representative vertex) = state.representative vertex
  root_representative : ∀ vertex, state.parent vertex = vertex → state.representative vertex = vertex
  parent_representative : ∀ vertex, state.representative (state.parent vertex) = state.representative vertex
  parent_rank : ∀ vertex, state.parent vertex ≠ vertex → state.rank vertex < state.rank (state.parent vertex)
  root_mass : ∀ vertex, state.parent vertex = vertex → 2 ^ state.rank vertex ≤ state.mass vertex
  nonroot_mass : ∀ vertex, state.parent vertex ≠ vertex → state.mass vertex = 0
  mass_budget : total state.mass ≤ n

/-- Two vertices belong to the same represented component. -/
def Connected {n : Nat} (state : State n) (first second : Fin n) : Prop :=
  state.representative first = state.representative second

/-- Initially every vertex is its own component, with rank zero and mass one. -/
def initial (n : Nat) : State n where
  parent := id
  rank := fun _ => 0
  representative := id
  mass := fun _ => 1



@[simp] theorem initial_connected (n : Nat) (first second : Fin n) :
    Connected (initial n) first second ↔ first = second := Iff.rfl

/-- A find traverses one parent link at a time and stops at a root.
    The final index counts traversed links, excluding the final root test. -/
inductive Find {n : Nat} (state : State n) : Fin n → Fin n → Nat → Prop where
  | root (vertex : Fin n) : state.parent vertex = vertex → Find state vertex vertex 0
  | step (vertex root : Fin n) (steps : Nat) :
      state.parent vertex ≠ vertex → Find state (state.parent vertex) root steps →
      Find state vertex root (steps + 1)













/-- Compress one visited vertex directly to its component root. -/
def compress {n : Nat} (state : State n) (vertex : Fin n) : State n :=
  { state with parent := update state.parent vertex (state.representative vertex) }

@[simp] theorem compress_representative {n : Nat} (state : State n) (vertex other : Fin n) :
    (compress state vertex).representative other = state.representative other := rfl

@[simp] theorem compress_connected {n : Nat} (state : State n) (vertex first second : Fin n) :
    Connected (compress state vertex) first second ↔ Connected state first second := Iff.rfl





/-- Redirect every name of the losing component to the winning root. -/
def mergeRepresentative {n : Nat} (representative : Fin n → Fin n)
    (loser winner : Fin n) : Fin n → Fin n :=
  fun vertex => if representative vertex = loser then winner else representative vertex

/-- Link two distinct roots whose ranks are in nondecreasing order. -/
def link {n : Nat} (state : State n) (loser winner : Fin n) : State n where
  parent := update state.parent loser winner
  rank := update state.rank winner
    (if state.rank loser = state.rank winner then state.rank winner + 1 else state.rank winner)
  representative := mergeRepresentative state.representative loser winner
  mass := update (update state.mass loser 0) winner (state.mass loser + state.mass winner)













/-- Link representatives by rank; an already connected pair leaves the state alone.
    The first argument wins rank ties, matching the usual union-by-rank code. -/
def union {n : Nat} (state : State n) (first second : Fin n) : State n :=
  let left := state.representative first
  let right := state.representative second
  if left = right then state
  else if state.rank left < state.rank right then link state left right
  else link state right left









end Algo2Lean.UnionFind


