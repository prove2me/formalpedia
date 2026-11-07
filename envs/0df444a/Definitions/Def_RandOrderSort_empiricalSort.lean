-- Prove2me | Definitions.Def_RandOrderSort_empiricalSort
-- name    : RandOrderSort_empiricalSort
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:21.123504+00:00
-- url     : https://prove2.me/theorems/87c9b1c4-9612-45ae-9b17-77b46bb985d8
-- title:
--   EmpiricalSort (Algorithm 1) and its run record
-- statement:
--   EmpiricalSort is defined literally as Algorithm 1. For $n<16T$ it places arrivals consecutively. Otherwise it places the first $T$ arrivals in the first $T$ cells, then runs the $L$ growing phases and the $k$ shrinking phases of the schedule. Each phase has a tree, prescribed capacities and a fresh block:
--
--   1. **Reallocate.** The old empty cells are processed in increasing physical order. Each is assigned, through its stored label's canonical leaf in the new tree, to a nearest bucket with unused capacity (ties by bucket index), and takes that bucket's left endpoint as its new label. The fresh block is then assigned in physical order, completing the lowest-indexed bucket first.
--   2. **Place.** Each arrival goes to the first free cell, in physical order, of a bucket with a free cell at minimum tree distance from its canonical leaf (ties by bucket index).
--
--   `runState` is the state of the run after a given number of arrivals; `empiricalSort` is the resulting `OnlineCmpAlg`. The record `St` stores the cell of each arrival, the labels and buckets of empty cells, the length of the allocated prefix, a `fault` flag, and a log of all requests. Each logged request carries its phase, its type (arrival or old cell), the key or label before and after replacement, and its canonical and destination leaves.
--
--   **Formalization Note** The run never stops: a step that finds no admissible bucket, a reallocation that leaves a capacity unfilled, or a fresh block that passes cell $n$ sets `fault`, and Lemma 3.1 asserts that this never happens. Arrival $t$ is processed with the key order restricted to the arrivals $0,\dots,t$, so the rule is online by construction. Fresh-cell assignments are not requests, as on p.20. A shrinking tree is (7) on the first $m$ keys with $b_i$ leaves, which is the truncation of the fixed tree (p.14).
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §3, pp.12–18; Algorithm 1, p.16; §4.1.1, p.20

import Mathlib
import Definitions.Def_RandOrderSort_OnlineCmpAlg
import Definitions.Def_RandOrderSort_phaseStart
import Definitions.Def_RandOrderSort_mkTree

namespace RandOrderSort

/-! # EmpiricalSort and its run (§3, pp.12–18; Algorithm 1, p.16)

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), §3.1, p.12: "The allocated cells always form a
physical prefix of the original array. Its empty cells are available; cells in the unallocated
suffix are reserved for later phases. At the start of a phase, every available cell belongs to a
bucket and carries that bucket's left endpoint as a temporary label. For an arriving key, choose a
bucket with a free cell at minimum tree distance from its canonical leaf. Break distance ties by
increasing bucket index, and use the first free cell of the chosen bucket in physical order. Store
the associated real value irrevocably in that cell." pp.12–13 (Reallocate): "At a phase change,
prescribe the new bucket capacities before assigning cells. Process the old available empty cells
in increasing physical order. For each cell, use its stored label to find its canonical leaf in
the new tree. Assign the cell to a nearest bucket with unused assignment capacity, breaking ties by
bucket index, and replace its label by that bucket's left endpoint. … After all old cells have been
assigned, append the prescribed fresh block from the unallocated suffix of the original n-cell
array. Assign its cells in physical order to the remaining capacities, completing the
lowest-indexed bucket first, and give each cell its new bucket's left endpoint as label."
Algorithm 1 (p.16) and §§3.2–3.3 fix the phases, trees, capacities and fresh blocks.

**Formalization Note.**
* The run processes arrivals `t = 0, 1, …, n − 1` in order; the processing of arrival `t` sees the
  key order only through `lt` restricted to the arrivals `0, …, t` (`restrictLt`). This makes
  EmpiricalSort an `OnlineCmpAlg` by construction (`empiricalSort`).
* `n < 8192`: arrival `t` goes to cell `t`. `n ≥ 8192`: arrivals `0, …, T − 1` go to cells
  `0, …, T − 1` (the initial block); every later arrival `t` belongs to phase `p = phaseOf n t`;
  at the first arrival of a phase, Reallocate runs first with the phase's tree (built by (7) from
  the first `phasePrefix n p` keys with `phaseLeaves n p` leaves), its capacities and its fresh
  block; then the arrival is placed.
* Tree distance ties are broken by bucket index; "nearest bucket with unused capacity" and
  "bucket with a free cell at minimum tree distance" both use `bestBucket`.
* The run never stops: if a step finds no admissible bucket, if a reallocation leaves a capacity
  unfilled, or if a fresh block passes cell `n`, the flag `fault` is set (an arrival without a cell
  is sent to cell `n + t`). Lemma 3.1 asserts that no fault occurs.
* The run's `log` records every request in order: arrivals and old-cell reassignments (§4.1.1), each
  with its phase, its type, the key or label of the cell before (`y`) and after (`z`) replacement,
  its canonical leaf and its destination leaf in the phase's tree. Fresh-cell assignments are not
  requests ("Initial labels on fresh cells are counted separately", p.20).
-/

/-- A request (§4.1.1, p.20): one arrival (`arr = true`) or one old empty cell reassigned at a
reallocation (`arr = false`) in phase `phase`; `y`, `z` are the cell's key or label before and
after replacement; `canon`, `dest` are its canonical and destination leaves. -/
structure Req where
  phase : ℕ
  arr : Bool
  y : Ext
  z : Ext
  canon : ℕ
  dest : ℕ

/-- The state of the run: `cell t` is the cell of arrival `t`; `filled c` says that cell `c`
holds an arrival; `bkt c` and `lbl c` are the bucket and the label of an allocated empty cell;
`alloc` is the length of the allocated physical prefix. -/
structure St where
  cell : ℕ → ℕ
  filled : ℕ → Bool
  bkt : ℕ → ℕ
  lbl : ℕ → Ext
  alloc : ℕ
  fault : Bool
  log : List Req

/-- The initial state: nothing placed, nothing allocated. -/
def St.init : St := ⟨fun _ => 0, fun _ => false, fun _ => 0, fun _ => .ninf, 0, false, []⟩

/-- `lt` restricted to the arrivals `0, …, t`. -/
def restrictLt (lt : ℕ → ℕ → Bool) (t : ℕ) (a b : ℕ) : Bool :=
  decide (a ≤ t) && decide (b ≤ t) && lt a b

/-- The tree of phase `p`: (7) on the first `phasePrefix n p` keys with `phaseLeaves n p` leaves
(Algorithm 1, lines 7, 12 and 14: a shrinking phase truncates the fixed tree, whose surviving
boundaries are `y_{⌊m j/b_i⌋}`, p.14). -/
def phaseTree (n : ℕ) (lt : ℕ → ℕ → Bool) (p : ℕ) : Tree :=
  mkTree lt (Finset.range (phasePrefix n p)) (phaseLeaves n p)

/-- The available (allocated, empty) cells in increasing physical order. -/
def St.emptyCells (s : St) : List ℕ := (List.range s.alloc).filter (fun c => !(s.filled c))

/-- The admissible bucket nearest to leaf `a` (least `lcaH a ℓ`, ties by least index `ℓ`). -/
def bestBucket (nb : ℕ) (avail : ℕ → Bool) (a : ℕ) : Option ℕ :=
  (List.range nb).foldl (fun acc ℓ =>
    if avail ℓ then
      match acc with
      | none => some ℓ
      | some ℓ' => if lcaH a ℓ < lcaH a ℓ' then some ℓ else acc
    else acc) none

/-- Reassign one old empty cell `c` at the reallocation of phase `p` (tree `tr`, capacities
`cap`, assignment counts `used`). -/
def reassignOld (p : ℕ) (lt : ℕ → ℕ → Bool) (tr : Tree) (cap : ℕ → ℕ) (acc : St × (ℕ → ℕ))
    (c : ℕ) : St × (ℕ → ℕ) :=
  let s := acc.1
  let used := acc.2
  let a := canonLeaf lt tr (s.lbl c)
  match bestBucket tr.leaves (fun ℓ => decide (used ℓ < cap ℓ)) a with
  | none => ({ s with fault := true }, used)
  | some ℓ =>
      ({ s with bkt := Function.update s.bkt c ℓ, lbl := Function.update s.lbl c (leftEnd tr ℓ),
                log := s.log ++ [⟨p, false, s.lbl c, leftEnd tr ℓ, a, ℓ⟩] },
       Function.update used ℓ (used ℓ + 1))

/-- Assign one fresh cell `c` to the lowest-indexed bucket with remaining capacity. -/
def assignFresh (tr : Tree) (cap : ℕ → ℕ) (acc : St × (ℕ → ℕ)) (c : ℕ) : St × (ℕ → ℕ) :=
  let s := acc.1
  let used := acc.2
  match (List.range tr.leaves).find? (fun ℓ => decide (used ℓ < cap ℓ)) with
  | none => ({ s with fault := true }, used)
  | some ℓ =>
      ({ s with bkt := Function.update s.bkt c ℓ, lbl := Function.update s.lbl c (leftEnd tr ℓ) },
       Function.update used ℓ (used ℓ + 1))

/-- **Reallocate** at the start of phase `p` (pp.12–13). -/
def realloc (n : ℕ) (lt : ℕ → ℕ → Bool) (p : ℕ) (s : St) : St :=
  let tr := phaseTree n lt p
  let cap := phaseCap n p
  let f := phaseFresh n p
  let r1 := s.emptyCells.foldl (reassignOld p lt tr cap) (s, fun _ => 0)
  let r2 := (List.range' s.alloc f).foldl (assignFresh tr cap) r1
  { r2.1 with
    alloc := s.alloc + f,
    fault := r2.1.fault || !((List.range tr.leaves).all (fun ℓ => decide (r2.2 ℓ = cap ℓ))) ||
      decide (n < s.alloc + f) }

/-- **Place** arrival `t` in phase `p` (p.12). -/
def placeArr (n : ℕ) (lt : ℕ → ℕ → Bool) (p t : ℕ) (s : St) : St :=
  let tr := phaseTree n lt p
  let a := canonLeaf lt tr (.key t)
  let free := fun ℓ => s.emptyCells.filter (fun c => decide (s.bkt c = ℓ))
  match bestBucket tr.leaves (fun ℓ => !(free ℓ).isEmpty) a with
  | none => { s with fault := true, cell := Function.update s.cell t (n + t) }
  | some ℓ =>
      match (free ℓ).head? with
      | none => { s with fault := true, cell := Function.update s.cell t (n + t) }
      | some c =>
          { s with cell := Function.update s.cell t c, filled := Function.update s.filled c true,
                   log := s.log ++ [⟨p, true, s.lbl c, .key t, a, ℓ⟩] }

/-- Process arrival `t` (Algorithm 1). `lt` is the key order on the arrivals `0, …, t`. -/
def stepArr (n : ℕ) (lt : ℕ → ℕ → Bool) (t : ℕ) (s : St) : St :=
  if n < 16 * T ∨ t < T then
    { s with cell := Function.update s.cell t t, filled := Function.update s.filled t true,
             alloc := t + 1 }
  else
    let p := phaseOf n t
    let s' := if phaseStart n p = t then realloc n lt p s else s
    placeArr n lt p t s'

/-- The state after the arrivals `0, …, t − 1` have been processed; arrival `τ` is processed with
the key order restricted to the arrivals `0, …, τ`. -/
def runState (n : ℕ) (lt : ℕ → ℕ → Bool) (t : ℕ) : St :=
  (List.range t).foldl (fun s τ => stepArr n (restrictLt lt τ) τ s) St.init

/-- A comparison table on the arrivals `0, …, t`, read as a relation on `ℕ`. -/
def tblLt {t : ℕ} (tbl : Fin (t + 1) → Fin (t + 1) → Bool) (a b : ℕ) : Bool :=
  if h : a < t + 1 ∧ b < t + 1 then tbl ⟨a, h.1⟩ ⟨b, h.2⟩ else false

/-- **EmpiricalSort** (Algorithm 1) as a comparison-only online algorithm: the cell of arrival `t`
is the one chosen when the run, fed the comparison table of the arrivals `0, …, t`, processes
arrival `t`. -/
def empiricalSort : OnlineCmpAlg :=
  ⟨fun n t tbl => (runState n (tblLt tbl) (t + 1)).cell t⟩

/-- The complete run of EmpiricalSort on the execution `(x, π, σ)`. -/
noncomputable def runOf {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) : St :=
  runState n (ltOf x π σ) n

/-- The requests of the operation of type `arr` (arrivals if `true`, reallocation if `false`) of
phase `p`, in order. -/
def opReqs (s : St) (p : ℕ) (arr : Bool) : List Req :=
  s.log.filter (fun r => decide (r.phase = p) && (r.arr == arr))

/-- The rank (0-based) of arrival `a` among the `n` arrivals in the order `lt`. -/
def rankLt (n : ℕ) (lt : ℕ → ℕ → Bool) (a : ℕ) : ℕ :=
  ((Finset.range n).filter (fun a' => lt a' a)).card

/-- The cut in the strict key order between ranks `c − 1` and `c` (0-based): arrival `a` is above
it when its rank is at least `c`. `c = 0` and `c = n` are the outer cuts. -/
def rankCut (n : ℕ) (lt : ℕ → ℕ → Bool) (c : ℕ) (a : ℕ) : Bool := decide (c ≤ rankLt n lt a)

end RandOrderSort


