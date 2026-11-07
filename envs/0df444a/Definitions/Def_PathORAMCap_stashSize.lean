-- Prove2me | Definitions.Def_PathORAMCap_stashSize
-- name    : PathORAMCap_stashSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:06.835886+00:00
-- url     : https://prove2.me/theorems/98473344-b030-49bd-991d-97d7239ba84a
-- title:
--   The Path ORAM process $P_{Z,N}$ and the stash size $S(\pi;t)$
-- statement:
--   The process $P_{Z,N}$ has bucket capacity $Z$ and blocks with addresses $1,\dots,N$ on the tree of depth $L=\lceil\log_2N\rceil$. Its state is a **position map** (each address's leaf label), the contents of every bucket (at most $Z$ blocks) and the **stash**. Initially the tree and the stash hold no real block and the position map holds independent uniform initial labels. An access to address $a$ with a fresh uniform label $U$:
--
--   1. reads the old label $x$ of $a$ and moves every block stored on $\mathrm{path}(x)$ into the stash;
--   2. creates block $a$ in the stash if this is its first access;
--   3. sets the label of $a$ to $U$;
--   4. refills $\mathrm{path}(x)$ from the leaf up to the root: a stash block is eligible for a bucket when its assigned path passes through it (for $a$, the new path); if at least $Z$ are eligible the $Z$ with the smallest block numbers move into the bucket, otherwise all eligible blocks do.
--
--   An instance is $(s,\alpha)$ with $s\ge1$ and $\alpha=(a_1,\dots,a_s)\in[N]^s$, fixed in advance. For the random execution $\pi=P_{Z,N}(s,\alpha)$, $S(\pi;t)$ is the number of real blocks in the stash after the refill of the $t$-th access, with $S(\pi;0)=0$.
--
--   All the theorems of the mission are about this process; the module defines it exactly, step by step.
--
--   **Formalization Note** Address $i$ is block `i − 1 : Fin N`, which keeps the identifier order. Block values, reads and writes, encryption and dummy blocks do not affect placement and are not modelled. The random inputs are the pair (initial labels, new labels) in `Labels N s`; the process itself is defined for any depth `L` and any labels (`stateAt`), and `stashSize` uses `L = ⌈log₂ N⌉`.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), §2.1–§2.2, pp.6–7 (PDF pp.9–10)

import Mathlib
import Definitions.Def_PathORAMCap_Leaf

set_option autoImplicit false

namespace PathORAMCap

/-- The storage state of Path ORAM with blocks `Fin N` on the depth-`L` tree (Chang, Au, *The Minimum
Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), §2.1,
pp.6–7 (PDF pp.9–10)):
`pos` is the position map (each block's assigned leaf label), `created b` records whether block `b`
has been created (first accessed), and `loc b = some v` means that block `b` is stored in the bucket
of node `v`; a created block with `loc b = none` is in the stash.

**Formalization Note.** The logical address `i ∈ [N]` is `Fin N` value `i − 1`, which preserves the
order used by the smallest-identifier tie-break. Block values, reads and writes, encryption and
dummy padding do not affect which real blocks sit where and are not modelled. -/
structure ORAMState (N L : ℕ) where
  /-- The position map. -/
  pos : Fin N → Leaf L
  /-- Whether the block has been created. -/
  created : Fin N → Bool
  /-- The bucket holding the block, or `none` (in the stash, or not created). -/
  loc : Fin N → Option (List Bool)

/-- The initial state (§2.1, "Initialization", p.6): the tree and the stash hold no real blocks, and
the position map holds the initial labels `U₀`. -/
def ORAMState.init {N L : ℕ} (U₀ : Fin N → Leaf L) : ORAMState N L :=
  ⟨U₀, fun _ => false, fun _ => none⟩

/-- Step 4 at one bucket (§2.1, p.7 (PDF p.10)): refill the node of depth `ℓ` on the path of the old
label `x`. A stash block is eligible when its assigned path passes through that node; if at least
`Z` blocks are eligible, the `Z` with the smallest identifiers move into the bucket, otherwise all
eligible blocks do. A block is selected exactly when fewer than `Z` eligible blocks have a smaller
identifier. -/
def refillLevel {N L : ℕ} (Z : ℕ) (st : ORAMState N L) (x : Leaf L) (ℓ : ℕ) : ORAMState N L :=
  let v := x.toList.take ℓ
  let elig : Fin N → Bool := fun b =>
    st.created b && (st.loc b).isNone && decide (v <+: (st.pos b).toList)
  let sel : Fin N → Bool := fun b =>
    elig b && decide ((Finset.univ.filter (fun b' => elig b' = true ∧ b' < b)).card < Z)
  { st with loc := fun b => if sel b then some v else st.loc b }

/-- One access to address `a` with new label `U` (§2.1, the four steps, pp.6–7 (PDF pp.9–10)):
1. read the old label `x = pos a` and move every block stored on `path(x)` into the stash;
2. create block `a` (in the stash) if this is its first access;
3. assign the new label: `pos a := U`;
4. refill `path(x)` from the leaf (depth `L`) up to the root (depth `0`) by `refillLevel`, with
   eligibility for the accessed block tested on its new label. -/
def access {N L : ℕ} (Z : ℕ) (st : ORAMState N L) (a : Fin N) (U : Leaf L) : ORAMState N L :=
  let x := st.pos a
  let st₁ : ORAMState N L :=
    { st with loc := fun b =>
        match st.loc b with
        | some w => if w <+: x.toList then none else some w
        | none => none }
  let st₂ : ORAMState N L := { st₁ with created := Function.update st₁.created a true }
  let st₃ : ORAMState N L := { st₂ with pos := Function.update st₂.pos a U }
  ((List.range (L + 1)).reverse).foldl (fun st' ℓ => refillLevel Z st' x ℓ) st₃

/-- The number of real blocks in the stash. -/
def stashCount {N L : ℕ} (st : ORAMState N L) : ℕ :=
  (Finset.univ.filter (fun b => st.created b = true ∧ st.loc b = none)).card

/-- The execution of `P_{Z,N}` on the instance `α = (a₁, …, a_s)` (encoded `Fin s → Fin N`) on a
depth-`L` tree with initial labels `U₀` and new labels `U`: the state after `t` accesses
(§2.2, p.7 (PDF p.10)). Access `t + 1` uses `α ⟨t, _⟩` and `U ⟨t, _⟩`; after `s` accesses the state
is unchanged. -/
def stateAt {N s : ℕ} (Z L : ℕ) (α : Fin s → Fin N) (U₀ : Fin N → Leaf L) (U : Fin s → Leaf L) :
    ℕ → ORAMState N L
  | 0 => ORAMState.init U₀
  | t + 1 => if h : t < s then access Z (stateAt Z L α U₀ U t) (α ⟨t, h⟩) (U ⟨t, h⟩)
      else stateAt Z L α U₀ U t

/-- The random inputs of an execution of `P_{Z,N}` on an instance of length `s`
(§2.1–§2.2, pp.6–7): the `N` initial labels and the `s` new labels, leaves of the depth-`⌈log₂ N⌉`
tree. All labels independent and uniform is the uniform law on this finite type. -/
abbrev Labels (N s : ℕ) : Type :=
  (Fin N → Leaf (treeDepth N)) × (Fin s → Leaf (treeDepth N))

/-- `S(π; t)` for `π = P_{Z,N}(s, α)` at the realization `ω` of the labels: the number of real
blocks in the stash after the refill of access `t` (§2.2, p.7 (PDF p.10)); `S(π; 0) = 0`. -/
def stashSize {N s : ℕ} (Z : ℕ) (α : Fin s → Fin N) (ω : Labels N s) (t : ℕ) : ℕ :=
  stashCount (stateAt Z (treeDepth N) α ω.1 ω.2 t)

end PathORAMCap


