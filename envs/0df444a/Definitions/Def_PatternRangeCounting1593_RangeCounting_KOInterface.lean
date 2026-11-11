-- Prove2me | Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface
-- name    : PatternRangeCounting1593_RangeCounting_KOInterface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:32.659423+00:00
-- url     : https://prove2.me/theorems/149fc5da-5dcd-4359-83a1-d9448b5e4c83
-- title:
--   The retained Kozma–Opler interface (K1)–(K4) on a bit string
-- statement:
--   Let $\pi$ be a pattern, $\tau$ a permutation of length $m$ and $w$ a word size. A bit string $\beta$ is a **retained Kozma–Opler representation** of $\tau$ for a hierarchy, a handle encoding and fixed operation programs when:
--
--   1. (K1) the hierarchy is a pair of nested division chains with $\ell$ levels as defined by the scales, $m_i$ blocks per axis at level $i$, and every level-$i$ block of size at most $40m/m_i$;
--   2. (K2) every row or column block at every level meets at most $\Delta=\lceil 10c_\pi\rceil$ occupied cells;
--   3. a block **handle** is a pair of words (succinct-tree node identifier, local-counter address); node identifiers are injective on the blocks of an axis and smaller than twice the number of tree nodes plus two;
--   4. (K3), (K4): on the packed bits of every buffer of fewer than $2^w$ bits that begins with $\beta$, each of the following fixed programs answers correctly within $T$ steps without modifying memory: coordinate $\mapsto$ (handle of its finest block, the block's endpoints, the coordinate's offset); (parent handle, one-based child index) $\mapsto$ child handle; tree parent, child and leaf selection; $\mathrm{childRank}$ (number of preceding siblings) and $\mathrm{leafRank}$ (number of leaves before the subtree); $\mathrm{rank}_1$ and $\mathrm{select}_1$ on the bitvector marking the first coordinate of every finest block; the local queries $\mathrm{rectCount}$, $\mathrm{nonEmpty}$, $\mathrm{cellRank}$ (above the finest level) and $\mathrm{rectCount}$, $\mathrm{cellOffset}$ (at the finest level), on both axes;
--   5. the original exact rectangle counter answers $|P_\tau\cap([x_1,x_2]\times[y_1,y_2])|$ for all $0\le x_1,x_2,y_1,y_2\le m$ within $c_{KO}(\lfloor\log_2\lfloor\log_2 m\rfloor\rfloor+1)$ steps.
--
--   The register conventions are $r_0=m$, $r_1=$ axis ($0$ for column blocks, $1$ for row blocks), then the arguments in the order of the paper.
--
--   This is the precise content of "the retained Kozma–Opler representation" that Theorem 1.1 keeps and that Lemmas 4.2–5.2 build on.
--
--   **Formalization Note** Requiring correctness on every buffer that begins with $\beta$, read-only, lets later components be appended and the operations be used as subroutines.
--
--   The base buffer itself must have fewer than $2^w$ bits. Thus the universal operation contract applies to the actual base buffer and cannot hold solely because no admissible extension exists.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 3.4 and the conventions after it, printed pp. 11–13 (PDF pp. 12–14); Kozma–Opler, arXiv:2510.20382v1, Lemma 2.2 and Section 4

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy

set_option autoImplicit false

namespace PatternRangeCounting1593.RangeCounting

/-!
# The retained Kozma–Opler interface (K1)–(K4)

Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 3.4 and the
conventions after it, printed pp. 11–13 (PDF pp. 12–14), attributed to Kozma–Opler
[KO26, arXiv:2510.20382v1, Lemma 2.2 and Section 4].

A bit string `base` *is a retained Kozma–Opler representation* of `τ` for the hierarchy `Hd`,
the handle encoding `hdl` and the fixed operation programs `P` when `Hd` satisfies (K1) and
(K2) and every operation of (K3) and (K4), run on the packed bits of any buffer that begins with
`base`, returns the specified answer within `T` steps without modifying memory; the exact
rectangle counter runs within `cKO · (⌊log₂⌊log₂ m⌋⌋ + 1)` steps.

Register conventions of every operation: `r₀ = m`, `r₁ = ax` (`0` = column blocks, `1` = row
blocks; the count takes no axis), then the operation's arguments; answers in `r₀, r₁, …`.
A handle of a block is the pair (node identifier, local-counter address) of two words.
-/

/-- The fixed programs implementing the retained operations. -/
structure KOProgs where
  /-- coordinate ↦ handle of its finest block, block endpoints, offset -/
  finest : Program
  /-- (parent handle, one-based child index) ↦ child handle -/
  child : Program
  /-- tree parent on node identifiers -/
  parent : Program
  /-- tree child selection on node identifiers -/
  treeChild : Program
  /-- leaf selection -/
  leafSelect : Program
  /-- `childRank(v)`: the number of preceding siblings -/
  childRank : Program
  /-- `leafRank(v)`: the number of leaves strictly before the subtree of `v` -/
  leafRank : Program
  /-- `rank₁` on the coordinate bitvector marking the first coordinate of every finest block -/
  rankU : Program
  /-- `select₁` on the coordinate bitvector -/
  selectU : Program
  /-- local `rectCount_B` -/
  rectCount : Program
  /-- local `nonEmpty_B` -/
  nonEmpty : Program
  /-- local `cellRank_B` -/
  cellRank : Program
  /-- finest `cellOffset_B` -/
  cellOffset : Program
  /-- the original exact rectangle counter -/
  count : Program

/-- A handle encoding: `node ax i b` and `addr ax i b` are the node identifier and local-counter
address of block `b` at level `i` on axis `ax`. -/
structure Handles where
  node : ℕ → ℕ → ℕ → ℕ
  addr : ℕ → ℕ → ℕ → ℕ

/-- (K1): `ℓ` is the depth of the scale sequence, level `i` has `m_i` blocks per axis, and every
level-`i` block has size at most `40 m / m_i`. -/
def K1 (m : ℕ) (Hd : Hierarchy) : Prop :=
  Hd.ell = depth m ∧
  ∀ i ≤ Hd.ell, ∀ ax ≤ 1, numBlocks (axisChain Hd ax) m i = blocksAt m i ∧
    ∀ b, (blockSet (axisChain Hd ax) m i b).card * blocksAt m i ≤ 40 * m

/-- (K2): every row or column block at every level meets at most `Δ` occupied cells. -/
def K2 {k m : ℕ} (π : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) : Prop :=
  ∀ i ≤ Hd.ell, ∀ ax ≤ 1, ∀ b, deg (axisView τ Hd ax) i b ≤ Delta π

/-- Handles are words; node identifiers are succinct-tree identifiers: injective on the blocks of
each axis and smaller than `2·(number of tree nodes) + 2` (the range of a balanced-parenthesis or
LOUDS position). -/
def HandlesOK (w m : ℕ) (Hd : Hierarchy) (hdl : Handles) : Prop :=
  ∀ ax ≤ 1,
    (∀ i ≤ Hd.ell, ∀ b < numBlocks (axisChain Hd ax) m i,
      hdl.node ax i b < 2 ^ w ∧ hdl.addr ax i b < 2 ^ w ∧
      hdl.node ax i b <
        2 * (∑ j ∈ Finset.range (Hd.ell + 1), numBlocks (axisChain Hd ax) m j) + 2) ∧
    (∀ i i' b b', i ≤ Hd.ell → i' ≤ Hd.ell → b < numBlocks (axisChain Hd ax) m i →
      b' < numBlocks (axisChain Hd ax) m i' → hdl.node ax i b = hdl.node ax i' b' →
      i = i' ∧ b = b')

/-- The operations of (K3) and (K4) are answered correctly on memory `mem` within `T` steps
(the counter within `Tc` steps), read-only. -/
def KOOps {m : ℕ} (w : ℕ) (τ : Equiv.Perm (Fin m)) (P : KOProgs) (T Tc : ℕ) (Hd : Hierarchy)
    (hdl : Handles) (mem : ℕ → ℕ) : Prop :=
  let ℓ := Hd.ell
  -- (K3) coordinate ↦ finest block
  (∀ ax ≤ 1, ∀ x, 1 ≤ x → x ≤ m →
    let f := axisChain Hd ax; let b := f ℓ x
    RunsQueryRO w P.finest mem [m, ax, x]
      [hdl.node ax ℓ b, hdl.addr ax ℓ b, bmin f m ℓ b, bmax f m ℓ b, x + 1 - bmin f m ℓ b] T) ∧
  -- (K3) parent handle and one-based child index ↦ child handle
  (∀ ax ≤ 1, ∀ i < ℓ, ∀ b < numBlocks (axisChain Hd ax) m i, ∀ j, 1 ≤ j →
    j ≤ nChildren (axisChain Hd ax) m i b →
    let c := firstChild (axisChain Hd ax) m i b + j - 1
    RunsQueryRO w P.child mem [m, ax, hdl.node ax i b, hdl.addr ax i b, j]
      [hdl.node ax (i + 1) c, hdl.addr ax (i + 1) c] T) ∧
  -- tree parent
  (∀ ax ≤ 1, ∀ i, 1 ≤ i → i ≤ ℓ → ∀ b < numBlocks (axisChain Hd ax) m i,
    RunsQueryRO w P.parent mem [m, ax, hdl.node ax i b]
      [hdl.node ax (i - 1) (parentOf (axisChain Hd ax) m i b)] T) ∧
  -- tree child selection
  (∀ ax ≤ 1, ∀ i < ℓ, ∀ b < numBlocks (axisChain Hd ax) m i, ∀ j, 1 ≤ j →
    j ≤ nChildren (axisChain Hd ax) m i b →
    RunsQueryRO w P.treeChild mem [m, ax, hdl.node ax i b, j]
      [hdl.node ax (i + 1) (firstChild (axisChain Hd ax) m i b + j - 1)] T) ∧
  -- leaf selection (one-based)
  (∀ ax ≤ 1, ∀ j, 1 ≤ j → j ≤ numBlocks (axisChain Hd ax) m ℓ →
    RunsQueryRO w P.leafSelect mem [m, ax, j] [hdl.node ax ℓ (j - 1)] T) ∧
  -- childRank (zero-based number of preceding siblings)
  (∀ ax ≤ 1, ∀ i, 1 ≤ i → i ≤ ℓ → ∀ b < numBlocks (axisChain Hd ax) m i,
    RunsQueryRO w P.childRank mem [m, ax, hdl.node ax i b]
      [childIndex (axisChain Hd ax) m i b - 1] T) ∧
  -- leafRank (leaves strictly before the subtree)
  (∀ ax ≤ 1, ∀ i ≤ ℓ, ∀ b < numBlocks (axisChain Hd ax) m i,
    RunsQueryRO w P.leafRank mem [m, ax, hdl.node ax i b]
      [axisChain Hd ax ℓ (bmin (axisChain Hd ax) m i b)] T) ∧
  -- rank₁ on the coordinate bitvector
  (∀ ax ≤ 1, ∀ x ≤ m,
    RunsQueryRO w P.rankU mem [m, ax, x]
      [((Finset.range (numBlocks (axisChain Hd ax) m ℓ)).filter
          (fun j => bmin (axisChain Hd ax) m ℓ j ≤ x)).card] T) ∧
  -- select₁ on the coordinate bitvector
  (∀ ax ≤ 1, ∀ j, 1 ≤ j → j ≤ numBlocks (axisChain Hd ax) m ℓ →
    RunsQueryRO w P.selectU mem [m, ax, j] [bmin (axisChain Hd ax) m ℓ (j - 1)] T) ∧
  -- (K4) local rectangle counts, above the finest level
  (∀ ax ≤ 1, ∀ i < ℓ, ∀ b < numBlocks (axisChain Hd ax) m i, ∀ u₁ u₂ h₁ v₁ h₂ v₂,
    ValidAbove (axisView τ Hd ax) i b u₁ u₂ h₁ v₁ h₂ v₂ →
    RunsQueryRO w P.rectCount mem [m, ax, hdl.node ax i b, hdl.addr ax i b, u₁, u₂, h₁, v₁, h₂, v₂]
      [rectAboveSem (axisView τ Hd ax) i b u₁ u₂ h₁ v₁ h₂ v₂] T) ∧
  -- (K4) local rectangle counts, at the finest level
  (∀ ax ≤ 1, ∀ b < numBlocks (axisChain Hd ax) m ℓ, ∀ u₁ u₂ h₁ v₁ h₂ v₂,
    ValidFinest (axisView τ Hd ax) ℓ b u₁ u₂ h₁ v₁ h₂ v₂ →
    RunsQueryRO w P.rectCount mem [m, ax, hdl.node ax ℓ b, hdl.addr ax ℓ b, u₁, u₂, h₁, v₁, h₂, v₂]
      [rectFinestSem (axisView τ Hd ax) ℓ b u₁ u₂ h₁ v₁ h₂ v₂] T) ∧
  -- (K4) child-cell occupancy
  (∀ ax ≤ 1, ∀ i < ℓ, ∀ b < numBlocks (axisChain Hd ax) m i, ∀ u h v,
    ValidCell (axisView τ Hd ax) i b u h v →
    RunsQueryRO w P.nonEmpty mem [m, ax, hdl.node ax i b, hdl.addr ax i b, u, h, v]
      [nonEmptySem (axisView τ Hd ax) i b u h v] T) ∧
  -- (K4) occupied child cells preceding a child cell
  (∀ ax ≤ 1, ∀ i < ℓ, ∀ b < numBlocks (axisChain Hd ax) m i, ∀ u h v,
    ValidCell (axisView τ Hd ax) i b u h v →
    RunsQueryRO w P.cellRank mem [m, ax, hdl.node ax i b, hdl.addr ax i b, u, h, v]
      [cellRankSem (axisView τ Hd ax) i b u h v] T) ∧
  -- (K4) finest cellOffset
  (∀ ax ≤ 1, ∀ b < numBlocks (axisChain Hd ax) m ℓ, ∀ u h, 1 ≤ u →
    u ≤ (blockSet (axisChain Hd ax) m ℓ b).card → 1 ≤ h → h ≤ deg (axisView τ Hd ax) ℓ b →
    RunsQueryRO w P.cellOffset mem [m, ax, hdl.node ax ℓ b, hdl.addr ax ℓ b, u, h]
      [cellOffsetSem (axisView τ Hd ax) ℓ b u h] T) ∧
  -- the original exact rectangle counter
  (∀ x₁ x₂ y₁ y₂, x₁ ≤ m → x₂ ≤ m → y₁ ≤ m → y₂ ≤ m →
    RunsQueryRO w P.count mem [m, x₁, x₂, y₁, y₂] [rectCount τ x₁ x₂ y₁ y₂] Tc)

/-- `base` is a retained Kozma–Opler representation of `τ` (pattern `π`, word size `w`): the
hierarchy `Hd` is valid and satisfies (K1), (K2); handles are words with injective node
identifiers; `base` itself has fewer than `2^w` bits, so the operation contract applies to it;
and on every buffer of fewer than `2^w` bits that begins with `base`, all retained
operations are answered within `T` steps and the exact counter within
`cKO · (⌊log₂⌊log₂ m⌋⌋ + 1)` steps. -/
def KOInterface {k m : ℕ} (π : Equiv.Perm (Fin k)) (w : ℕ) (τ : Equiv.Perm (Fin m))
    (P : KOProgs) (T cKO : ℕ) (base : List Bool) (Hd : Hierarchy) (hdl : Handles) : Prop :=
  Hd.Valid m ∧ K1 m Hd ∧ K2 π τ Hd ∧ HandlesOK w m Hd hdl ∧ base.length < 2 ^ w ∧
  ∀ buf : List Bool, base <+: buf → buf.length < 2 ^ w →
    KOOps w τ P T (cKO * loglogBound m) Hd hdl (packBits w buf)

end PatternRangeCounting1593.RangeCounting


