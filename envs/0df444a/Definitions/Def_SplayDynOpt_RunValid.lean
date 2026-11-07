-- Prove2me | Definitions.Def_SplayDynOpt_RunValid
-- name    : SplayDynOpt_RunValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:44.891206+00:00
-- url     : https://prove2.me/theorems/ee6c1eca-ae6f-480f-a5c0-ec14b3509664
-- title:
--   The pairing-heap interface: blocks, operations and valid runs
-- statement:
--   Fix a finite set $V$ of elements, integers $C_{\mathrm{growing}},C_{\mathrm{exempt}}$ and $G\ge2$, and a real $\gamma$. The **state** consists of a collection of blocks and a value function $f:V\to\{1,\dots,G\}$. Each block has an ordered sequence of elements, a creator $u\in V$ and a pass count $p\in\mathbb Z_{\ge0}$, and is either growing or shrinking. Initially there are no blocks and the values $f(v)\in\{1,\dots,G\}$ are arbitrary. The **operations** and their preconditions are:
--
--   1. $\mathrm{Convert}(B)$: turn the growing block $B$ into a shrinking block.
--   2. $\mathrm{Create}(v)$: create a new empty growing block with creator $v$ and pass count $0$; afterwards at most $C_{\mathrm{growing}}$ growing blocks have creator $v$.
--   3. $\mathrm{Insert}(B,v)$: given $v$ in no block and a growing block $B$ with creator $u$ and $f(v)\ge f(u)+1$, add $v$ as the leftmost element of $B$.
--   4. $\mathrm{Delete}(v)$: remove $v$ from the shrinking block containing it.
--   5. $\mathrm{Pass}(B,M)$: $B$ is shrinking and $M$ is a set of tuples $(v,w,B_v)$, where $v,w$ are adjacent in $B$ in either order and $B_v$ is a growing block with creator $v$, such that $f(w)\ge f(v)+1$ for each tuple, each element of $B$ appears in at most one tuple, and either $|M|\ge\gamma|B|$ or the pass count of $B$ is less than $C_{\mathrm{exempt}}$. The pass count of $B$ increases by $1$, and for each tuple $w$ is removed from $B$ and added as the leftmost element of $B_v$.
--   6. $\mathrm{Split}(B,k)$: split the shrinking block $B$ into two new shrinking blocks, the prefix of length $k$ and the suffix of length $|B|-k$, each inheriting the creator and the current pass count of $B$; $B$ becomes empty.
--   7. $\mathrm{ValueChange}(v,\Delta)$: with $\Delta\in\{-1,1\}$, set $f(v)\leftarrow f(v)+\Delta$, keeping $1\le f(v)\le G$.
--
--   A **valid run** is a list of operations from an initial state, each satisfying its preconditions in the state its predecessors produce. The **total activity** $A$ is $\sum|M|$ over all Pass operations, $A_{\mathrm{insig}}(\tau)$ is the same sum over Pass operations on blocks with pass count at least $\tau$ before the pass, and $\#\mathrm{Insert}$, $\#\mathrm{ValueChange}$ count those operations.
--
--   The interface abstracts the core of the pairing-heap analyses of Sinnamon–Tarjan and Tarjan–Xu, and it can be studied independently of trees.
--
--   **Formalization Note** A block is identified by its index in the list of all blocks ever created: `create` appends one and `split` appends two, prefix first, so the identifiers are fresh. A block emptied by `split` stays in the list as an empty shrinking block. The invariants "each element is in at most one block" and "at most $C_{\mathrm{growing}}$ growing blocks per creator" follow from the preconditions. $M$ is a list without repeated elements; its losers enter distinct blocks because the winners are distinct, so the order of the list does not matter. The integer constants are natural numbers, since a negative constant would behave like $0$.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §5.5.1, pp.38–39 (State, Operations); Lemmas 26, 27, p.39 (A, A_insig)

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

/-- The fixed parameters of the interface (§5.5.1, p.38): integers `C_growing`, `C_exempt`, the
value bound `G`, and the real `γ`. -/
structure IParams where
  Cgrowing : ℕ
  Cexempt : ℕ
  G : ℕ
  γ : ℝ

/-- A **block** of the interface: an ordered sequence of elements (`elems`, leftmost first), its
creator element, its pass count, and whether it is growing (`true`) or shrinking (`false`). -/
structure Block (V : Type) where
  elems : List V
  creator : V
  passCount : ℕ
  growing : Bool

/-- The **state** of the interface: the blocks, indexed by their position in `blocks` (a block's
identifier is its index; created blocks are appended, so identifiers are never reused), and the
value function `f`. -/
structure IState (V : Type) where
  blocks : List (Block V)
  f : V → ℕ

/-- The **operations** of the interface (§5.5.1, pp.38–39). `create v` creates the block with the
next free identifier `blocks.length`; `split B k` creates the two blocks with the next two free
identifiers (prefix first). In `pass B M`, each pairing is a triple `(v, w, B_v)`: winner `v`,
loser `w`, and the identifier of the growing block `B_v` of `v` that `w` joins. In
`valueChange v up`, `up = true` is `Δ = +1` and `up = false` is `Δ = −1`. -/
inductive IOp (V : Type)
  | convert (B : ℕ)
  | create (v : V)
  | insert (B : ℕ) (v : V)
  | delete (v : V)
  | pass (B : ℕ) (M : List (V × V × ℕ))
  | split (B : ℕ) (k : ℕ)
  | valueChange (v : V) (up : Bool)

variable {V : Type} [DecidableEq V]

/-- The number of growing blocks with creator `v`. -/
def numGrowing (s : IState V) (v : V) : ℕ :=
  (s.blocks.filter (fun b => b.growing && decide (b.creator = v))).length

/-- The **preconditions** of each operation, verbatim from §5.5.1 (pp.38–39):
* `Convert(B)`: `B` is a growing block.
* `Create(v)`: afterwards there are at most `C_growing` growing blocks with creator `v`.
* `Insert(B, v)`: `v` is in no block, `B` is a growing block with creator `u`, and
  `f(v) ≥ f(u) + 1`.
* `Delete(v)`: `v` is in a shrinking block.
* `Pass(B, M)`: `B` is shrinking; for every pairing `(v, w, B_v)`, `v` and `w` are adjacent
  elements of `B` in either order, `B_v` is a growing block with creator `v`, and
  `f(w) ≥ f(v) + 1`; each element of `B` appears in at most one pairing; and either
  `|M| ≥ γ|B|` or the pass count of `B` is `< C_exempt` (both measured before the pass).
* `Split(B, k)`: `B` is shrinking and `0 ≤ k ≤ |B|`.
* `ValueChange(v, Δ)`: `1 ≤ f(v) + Δ ≤ G`. -/
def IOp.Valid (P : IParams) (s : IState V) : IOp V → Prop
  | .convert B => ∃ b, s.blocks[B]? = some b ∧ b.growing = true
  | .create v => numGrowing s v + 1 ≤ P.Cgrowing
  | .insert B v =>
      (∀ b ∈ s.blocks, v ∉ b.elems) ∧
      ∃ b, s.blocks[B]? = some b ∧ b.growing = true ∧ s.f b.creator + 1 ≤ s.f v
  | .delete v => ∃ b ∈ s.blocks, b.growing = false ∧ v ∈ b.elems
  | .pass B M =>
      ∃ b, s.blocks[B]? = some b ∧ b.growing = false ∧
        (∀ p ∈ M, ([p.1, p.2.1] <:+: b.elems ∨ [p.2.1, p.1] <:+: b.elems) ∧
          (∃ bv, s.blocks[p.2.2]? = some bv ∧ bv.growing = true ∧ bv.creator = p.1) ∧
          s.f p.1 + 1 ≤ s.f p.2.1) ∧
        (M.flatMap (fun p => [p.1, p.2.1])).Nodup ∧
        ((M.length : ℝ) ≥ P.γ * b.elems.length ∨ b.passCount < P.Cexempt)
  | .split B k => ∃ b, s.blocks[B]? = some b ∧ b.growing = false ∧ k ≤ b.elems.length
  | .valueChange v up => if up then s.f v + 1 ≤ P.G else 2 ≤ s.f v

/-- The **effect** of each operation (§5.5.1, pp.38–39):
* `Convert(B)`: `B` becomes shrinking.
* `Create(v)`: a new empty growing block with creator `v` and pass count `0`.
* `Insert(B, v)`: `v` becomes the leftmost element of `B`.
* `Delete(v)`: `v` is removed from its shrinking block.
* `Pass(B, M)`: the pass count of `B` is incremented; for every pairing `(v, w, B_v)` the loser
  `w` is removed from `B` and added as the leftmost element of `B_v`.
* `Split(B, k)`: two new shrinking blocks, the prefix of length `k` and the suffix of `B`, both
  with the creator and the current pass count of `B`; `B` becomes empty.
* `ValueChange(v, Δ)`: `f(v) ← f(v) + Δ`. -/
def IOp.apply (s : IState V) : IOp V → IState V
  | .convert B => ⟨s.blocks.mapIdx (fun i b => if i = B then { b with growing := false } else b), s.f⟩
  | .create v => ⟨s.blocks ++ [⟨[], v, 0, true⟩], s.f⟩
  | .insert B v =>
      ⟨s.blocks.mapIdx (fun i b => if i = B then { b with elems := v :: b.elems } else b), s.f⟩
  | .delete v =>
      ⟨s.blocks.map (fun b => if b.growing = false then { b with elems := b.elems.erase v } else b),
        s.f⟩
  | .pass B M =>
      let losers := M.map (fun p => p.2.1)
      let bs := s.blocks.mapIdx (fun i b =>
        if i = B then { b with elems := b.elems.filter (fun x => x ∉ losers),
                               passCount := b.passCount + 1 } else b)
      ⟨M.foldl (fun bs p => bs.mapIdx (fun i b =>
          if i = p.2.2 then { b with elems := p.2.1 :: b.elems } else b)) bs, s.f⟩
  | .split B k =>
      match s.blocks[B]? with
      | none => s
      | some b =>
          ⟨s.blocks.set B { b with elems := [] } ++
            [⟨b.elems.take k, b.creator, b.passCount, false⟩,
             ⟨b.elems.drop k, b.creator, b.passCount, false⟩], s.f⟩
  | .valueChange v up =>
      ⟨s.blocks, Function.update s.f v (if up then s.f v + 1 else s.f v - 1)⟩

/-- An **initial state**: no blocks, and arbitrary values `f(v) ∈ {1, …, G}` (p.38: "Initially,
there are no blocks, and the values f(v) are arbitrary"). -/
def IState.IsInitial (P : IParams) (s : IState V) : Prop :=
  s.blocks = [] ∧ ∀ v, 1 ≤ s.f v ∧ s.f v ≤ P.G

/-- A **valid sequence of interface operations** from the state `s`: every operation satisfies its
preconditions in the state produced by the operations before it.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §5.5.1, pp.38–39 (State and Operations of the interface).

**Formalization Note.** Blocks are identified by their index in the list of all blocks ever
created; a block emptied by `Split` stays in the list as an empty shrinking block. The invariants
"each element belongs to at most one block" and "at most `C_growing` growing blocks per creator"
are maintained by the preconditions (`Insert` needs `v` in no block; only `Create` makes growing
blocks). A pass is a list of pairings; the losers enter distinct blocks (their winners are
distinct), so the order of the list does not matter. -/
def RunValid (P : IParams) : IState V → List (IOp V) → Prop
  | _, [] => True
  | s, op :: ops => op.Valid P s ∧ RunValid P (op.apply s) ops

/-- The **total activity** `A`: the sum of the matching sizes `|M|` over all `Pass` operations
(Lemma 26, p.39). -/
def activity : List (IOp V) → ℕ
  | [] => 0
  | .pass _ M :: ops => M.length + activity ops
  | _ :: ops => activity ops

/-- `A_insig`: the sum of `|M|` over the **insignificant** passes, those on a block whose pass
count before the pass is at least the threshold `τ` (Lemma 27, p.39). -/
def insigActivity (τ : ℕ) : IState V → List (IOp V) → ℕ
  | _, [] => 0
  | s, op :: ops =>
      (match op with
       | .pass B M => if τ ≤ ((s.blocks[B]?).map Block.passCount).getD 0 then M.length else 0
       | _ => 0) + insigActivity τ (op.apply s) ops

/-- `#Insert`: the number of `Insert` operations. -/
def numInsert : List (IOp V) → ℕ
  | [] => 0
  | .insert _ _ :: ops => 1 + numInsert ops
  | _ :: ops => numInsert ops

/-- `#ValueChange`: the number of `ValueChange` operations. -/
def numValueChange : List (IOp V) → ℕ
  | [] => 0
  | .valueChange _ _ :: ops => 1 + numValueChange ops
  | _ :: ops => numValueChange ops

end SplayDynOpt


