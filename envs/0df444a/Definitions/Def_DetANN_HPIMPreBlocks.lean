-- Prove2me | Definitions.Def_DetANN_HPIMPreBlocks
-- name    : DetANN_HPIMPreBlocks
-- status  : Definition
-- author  : @milia
-- created : 2026-11-17T07:49:00.732211+00:00
-- url     : https://prove2.me/theorems/5f5de37d-43e7-438e-805d-bf7af1299cc1
-- title:
--   Program blocks for the HPIM preprocessing program
-- statement:
--   Vocabulary for building the preprocessing program of `hpim_preprocessing` out of **blocks**, on the PNormReg machine (definition `PNormReg_Machine`). In a state, $I$ is the integer memory and $R$ the real memory.
--
--   1. **Blocks.** A block is a family $\mathrm{blk}:\mathbb N\to\mathrm{Program}$.
--      - The code $\mathrm{blk}(o)$ is placed at position $o$ of a host program, so its jump targets are absolute ($o+k$).
--      - `IsBlock blk L` says that every $\mathrm{blk}(o)$ has length $L$ and is a deterministic program (`DetProgram`).
--      - A block specification is stated for *every* host $Q$ that embeds $\mathrm{blk}(o)$ at $o$.
--   2. **Frames.**
--      - `KeepsLow s s' outP outR`: the pointer and real registers with index $<40$ agree between $s$ and $s'$, except the listed output registers.
--      - `WritesOnly Q s t W`: every cell stored to in the first $t$ steps of $Q$ from $s$ satisfies $W$. Here $(\mathrm{true},z)$ is real cell $z$ and $(\mathrm{false},z)$ is integer cell $z$.
--   3. **Local points.** `LocalPts s P` says that $P_0,\dots,P_{n-1}\in\mathbb R^m$ are stored in $s$:
--      - pointer $1$ is $m$ and pointer $11$ is $n$;
--      - the list at pointer $10$ holds global indices $g_i=I[p_{10}+i]$;
--      - point $g$ starts at real address $I[p_{12}+g]$, so $R[I[p_{12}+g_i]+j]=P_i(j)$;
--      - all addresses are $\ge0$.
--   4. **Components.** `compMin P d i` is the least index in the component of $i$ in the threshold graph at $d$, whose edges are $\{a,b\}$ with $\|P_a-P_b\|\le d$.
--   5. **Stored BSPs.** `BSPAt m s ilo ihi rlo rhi u T` says that the BSP $T$ (definition `DetANN_HPIMBSP`) is stored from integer address $u$, with all its integer cells in $[i_{lo},i_{hi})$ and all its real cells in $[r_{lo},r_{hi})$.
--      - At node $u$: $I[u]$ is $0$ for a leaf and $1$ for a cut, and $I[u+1]$ is the real address of the node's box ($lo$, then $hi$, $m$ cells each).
--      - A leaf has $I[u+2]$ equal to $0$ (OUT) or $i+1$ (IN $i$).
--      - A cut has its children at $I[u+2]$ and $I[u+3]$.
--   6. **Size of the HPIM tree.** For the tree of definition `DetANN_HPIMTree`, $\mathrm{treePts}(Y,f,S)$ is the total number of points over the tree on $S$ with fuel $f$:
--      $$\mathrm{treePts}(f,S)=\begin{cases}|S|&f=0\text{ or }|S|\le1,\\ |S|+\sum_{C}\mathrm{treePts}(f-1,C)+\mathrm{treePts}(f-1,R)&\text{otherwise,}\end{cases}$$
--      where $C$ runs over the *distinct* components at $r_{\mathrm{med}}$ and $R$ is the set of representatives at $2r_{\mathrm{med}}$. Children with equal sets are counted once, because they are stored once.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7): the preprocessing program of DetANN.HPIM.hpim_preprocessing is assembled from these blocks. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_DetANN_HPIMTree

/-!
# Program blocks for the HPIM preprocessing program

The preprocessing program of `DetANN.HPIM.hpim_preprocessing` is assembled from **blocks**. A block is
a family `blk : ℕ → Program` of fixed length `L`. Here `blk off` is the code placed at position `off`
of a host program, so its jump targets are absolute (`off + k`). A block specification holds in
*every* host `Q` that embeds `blk off` at `off` (`PNormRegLib.Embeds`). It starts at `pc = off` and
ends at `pc = off + L` without halting.

**Register convention.** Pointer and real registers `< 40` belong to the host. A block changes only
its listed output registers among them (`KeepsLow`). Registers `≥ 40` are free scratch for blocks.
The interface registers are:
* pointers:
  * `1` = `m`;
  * `10` = address of the local index list `S`;
  * `11` = `n`;
  * `12` = base of the point-address table;
  * `13`, `14` = tops of the integer and real scratch stacks (free cells lie *below* them);
  * `15`, `16` = integer and real heap pointers (free cells lie *at and above* them);
  * `17` = an address passed in or out;
* reals: `10` = a threshold or the median threshold, `11` = a radius `r`, `12` = a factor `c`.

**Memory convention.** Inputs and the heap live at addresses `≥ 0`. Scratch lives at addresses `< 0`.

* `IsBlock blk L`: every `blk off` has length `L` and is a `DetProgram`.
* `KeepsLow`, `WritesOnly`: register frame and write frame of a run segment.
* `LocalPts s pts`: the local points `pts` are stored in `s`. Their global indices are `I[S + i]`,
  and point `g` starts at real address `I[PA + g]`.
* `compMin P d i`: the least index of the component of `i` in the threshold graph at `d`.
* `BSPAt m s ilo ihi rlo rhi u T`: the BSP `T` is stored from integer address `u`, with all its
  integer cells in `[ilo, ihi)` and all its real cells in `[rlo, rhi)`.
* `treePts Y S f`: the total number of points over the HPIM tree on `S`. Children with equal sets
  under one node are counted once, because they are stored once.
-/

namespace DetANN.HPIM

open PNormReg

/-- `blk off` has length `L` and is a deterministic program, for every offset. -/
def IsBlock (blk : ℕ → Program) (L : ℕ) : Prop :=
  ∀ off, (blk off).length = L ∧ DetProgram (blk off)

/-- Host registers (`< 40`) are kept, except the listed output pointers `outP` and reals `outR`. -/
def KeepsLow (s s' : State) (outP outR : List ℕ) : Prop :=
  (∀ x < 40, x ∉ outP → s'.core.ptrs x = s.core.ptrs x) ∧
    (∀ x < 40, x ∉ outR → s'.core.regs x = s.core.regs x)

/-- Every cell stored to in the first `t` steps of `Q` from `s` satisfies `W`
(`(true, z)`: real cell `z`; `(false, z)`: integer cell `z`). -/
def WritesOnly (Q : Program) (s : State) (t : ℕ) (W : Bool × ℤ → Prop) : Prop :=
  ∀ c ∈ cellsWritten Q s t, W c

/-- The local points `pts` are stored in `s` (all addresses `≥ 0`). -/
def LocalPts {m n : ℕ} (s : State) (pts : Fin n → Fin m → ℝ) : Prop :=
  s.core.ptrs 1 = m ∧ s.core.ptrs 11 = n ∧ 0 ≤ s.core.ptrs 10 ∧ 0 ≤ s.core.ptrs 12 ∧
    ∀ i : Fin n, 0 ≤ s.integerMemory (s.core.ptrs 10 + i) ∧
      0 ≤ s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i)) ∧
      ∀ j : Fin m,
        s.core.mem (s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i)) + j) =
          pts i j

/-- The least index of the component of `i` in the threshold graph at `d`. -/
noncomputable def compMin {m n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (i : Fin n) : ℕ := by
  classical
  exact ((Finset.univ.filter (thrReach P d i)).min'
    ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩⟩ : ℕ)

/-- The BSP `T` is stored from integer address `u`, inside the integer window `[ilo, ihi)` and the
real window `[rlo, rhi)`. A node at `u`: `I[u] = 0` (leaf) or `1` (cut); `I[u+1]` is the real address
of its box (`lo`: `m` cells, then `hi`: `m` cells). For a leaf, `I[u+2]` is `0` (OUT) or `i + 1`
(IN `i`). For a cut, `I[u+2]` and `I[u+3]` are the addresses of the left and right children. -/
inductive BSPAt (m : ℕ) (s : State) (ilo ihi rlo rhi : ℤ) : ℤ → BSP m → Prop
  | leaf (u : ℤ) (lo hi : Fin m → ℝ) (a : Option ℕ) :
      ilo ≤ u → u + 3 ≤ ihi → s.integerMemory u = 0 →
      rlo ≤ s.integerMemory (u + 1) → s.integerMemory (u + 1) + 2 * m ≤ rhi →
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + j) = lo j) →
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + m + j) = hi j) →
      s.integerMemory (u + 2) = (match a with | none => 0 | some i => (i : ℤ) + 1) →
      BSPAt m s ilo ihi rlo rhi u (.leaf lo hi a)
  | cut (u : ℤ) (lo hi : Fin m → ℝ) (l r : BSP m) :
      ilo ≤ u → u + 4 ≤ ihi → s.integerMemory u = 1 →
      rlo ≤ s.integerMemory (u + 1) → s.integerMemory (u + 1) + 2 * m ≤ rhi →
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + j) = lo j) →
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + m + j) = hi j) →
      BSPAt m s ilo ihi rlo rhi (s.integerMemory (u + 2)) l →
      BSPAt m s ilo ihi rlo rhi (s.integerMemory (u + 3)) r →
      BSPAt m s ilo ihi rlo rhi u (.cut lo hi l r)

/-- The total number of points over the HPIM tree on `S` with fuel `f` (the recursion of
`hpimNode`). The children of one node with the same set are counted once. -/
noncomputable def treePts {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) :
    ℕ → Finset (Fin N) → ℕ
  | 0, S => S.card
  | f + 1, S => by
    classical
    exact if S.card ≤ 1 then S.card else
      S.card + (∑ C ∈ Finset.univ.image (compBotOf Y S), treePts Y f C) + treePts Y f (repsOf Y S)

end DetANN.HPIM


