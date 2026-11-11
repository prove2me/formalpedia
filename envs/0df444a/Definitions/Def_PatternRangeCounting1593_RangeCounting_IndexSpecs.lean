-- Prove2me | Definitions.Def_PatternRangeCounting1593_RangeCounting_IndexSpecs
-- name    : PatternRangeCounting1593_RangeCounting_IndexSpecs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:14.961273+00:00
-- url     : https://prove2.me/theorems/4f15f6a1-8d51-44d6-b5a2-7d0de3305de3
-- title:
--   Navigation structure, gateway index, boundary records, occupied-cell lists and the indexed representation
-- statement:
--   Each component of the additional index is a bit string placed anywhere in a buffer that begins with a retained Kozma–Opler representation $\beta$; its bit offset is passed in a register, the buffer has fewer than $2^w$ bits, and the program runs read-only.
--
--   1. A **navigation structure** $N$ (Lemma 4.2): with registers $(m, o_N, \mathrm{ax}, x, i)$, for the level-$i$ block $B$ of axis $\mathrm{ax}$ containing $x\in[1,m]$, the program returns its handle, its zero-based left-to-right index at level $i$, $\min B$, $\deg(B)$, its width if $i=\ell$ (else $0$), and its one-based index among its parent's children ($0$ at level $0$).
--   2. A **gateway index** $D$ (Theorem 4.4): with registers $(m,o_N,o_D,x,y)$, $x,y\in[1,m]$, the program returns the largest $i^*\le a$ for which $Z=C_{i^*}(x)\times R_{i^*}(y)$ is occupied, and $(p(Z),c(Z),d(Z))$.
--   3. **Boundary records** $J$ (Lemma 5.1): for a block $B$ of axis $\mathrm{ax}$ at level $i\le\ell$ given by its handle, a cut $0\le c\le\deg(B)$ and $\min B-1\le x\le\max B$, the program returns $G_B(x,c)$.
--   4. The **occupied-cell lists** are given to the constructors as words: for the column view and then the row view, for every level and block in order, the degree followed by the indices of the opposite blocks of its occupied cells in increasing order.
--   5. The **indexed representation** is $\beta\,N\,D\,J$ (concatenated, at bit offsets $0,o_N,o_D,o_J$) with each component meeting its specification for the same hierarchy and handles, all within $T$ steps.
--
--   These specifications fix *what* is computed; the space, time and construction bounds are stated by the theorems.
--
--   An indexed representation additionally requires the complete concatenated buffer to have fewer than $2^w$ bits, so all component contracts apply to this actual buffer.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §4.1 Lemma 4.2, §4.2 Theorem 4.4, §5.1 Lemma 5.1, §7.1 Theorem 7.1, printed pp. 15–18 and 23–25 (PDF pp. 16–19 and 24–26)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
import Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface

set_option autoImplicit false

namespace PatternRangeCounting1593.RangeCounting

/-!
# The additional index: navigation directories, gateway index, boundary records

Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §4.1 (Lemma 4.2), §4.2
(Theorem 4.4), §5.1 (Lemma 5.1), §7.1 (Theorem 7.1), printed pp. 15–18 and 23–25
(PDF pp. 16–19 and 24–26).

Each component is a bit string placed anywhere in a buffer that begins with the retained
Kozma–Opler representation `base`; its bit offset is passed in a register. The specifications
say what a fixed program computes from such a buffer, read-only, within a step bound. They state
no space or time bound themselves; those are conclusions of the theorems.
-/

/-- Lemma 4.2's navigation structure `N` (directories, degree arrays, ancestor records): on any
buffer of fewer than `2^w` bits beginning with `base` and holding `N` at bit offset `oN`, the
program `navP` with registers `[m, oN, ax, x, i]` (axis `ax`, coordinate `x ∈ [1, m]`, level
`i ≤ ℓ`) returns, for the level-`i` block `B` containing `x`: its handle (node identifier,
counter address), its zero-based left-to-right index at level `i`, its first coordinate, its degree, its width if `i = ℓ` (else `0`), and its
one-based index among its parent's children (`0` at level `0`), within `Tnav` steps. -/
def NavSpec {m : ℕ} (w : ℕ) (τ : Equiv.Perm (Fin m)) (navP : Program) (Tnav : ℕ)
    (base N : List Bool) (Hd : Hierarchy) (hdl : Handles) : Prop :=
  ∀ buf : List Bool, ∀ oN : ℕ, base <+: buf → SliceAt buf oN N → buf.length < 2 ^ w →
    ∀ ax ≤ 1, ∀ x, 1 ≤ x → x ≤ m → ∀ i ≤ Hd.ell,
      let f := axisChain Hd ax; let b := f i x
      RunsQueryRO w navP (packBits w buf) [m, oN, ax, x, i]
        [hdl.node ax i b, hdl.addr ax i b, b, bmin f m i b, deg (axisView τ Hd ax) i b,
         if i = Hd.ell then (blockSet f m i b).card else 0, childIndex f m i b] Tnav

/-- Theorem 4.4's gateway index `D`: on any buffer of fewer than `2^w` bits beginning with
`base`, holding `N` at `oN` and `D` at `oD`, the program `gwP` with registers `[m, oN, oD, x, y]`
(`x, y ∈ [1, m]`) returns the largest `i* ≤ a` (anchor level) for which
`Z = C_{i*}(x) × R_{i*}(y)` is occupied, and `(p(Z), c(Z), d(Z))`, within `Tg` steps. -/
def GatewaySpec {m : ℕ} (w : ℕ) (τ : Equiv.Perm (Fin m)) (gwP : Program) (Tg : ℕ)
    (base N D : List Bool) (Hd : Hierarchy) : Prop :=
  ∀ buf : List Bool, ∀ oN oD : ℕ, base <+: buf → SliceAt buf oN N → SliceAt buf oD D →
    buf.length < 2 ^ w →
    ∀ x y, 1 ≤ x → x ≤ m → 1 ≤ y → y ≤ m →
      let i := gatewayLevel τ Hd (anchorLevel m) x y
      let cx := Hd.cb i x; let ry := Hd.rb i y
      RunsQueryRO w gwP (packBits w buf) [m, oN, oD, x, y]
        [i, nwCount (colView τ Hd) i cx ry, cutAbove (colView τ Hd) i cx ry,
         cutAbove (rowView τ Hd) i ry cx] Tg

/-- Lemma 5.1's boundary records `J`: on any buffer of fewer than `2^w` bits beginning with
`base`, holding `N` at `oN` and `J` at `oJ`, the program `bdP` with registers
`[m, oN, oJ, ax, i, node, addr, c, x]` for a block `B` (axis `ax`, level `i ≤ ℓ`, given by its
handle), a cut `0 ≤ c ≤ deg(B)` and a cutoff `min B − 1 ≤ x ≤ max B` returns `G_B(x, c)` within
`Tb` steps. -/
def BoundarySpec {m : ℕ} (w : ℕ) (τ : Equiv.Perm (Fin m)) (bdP : Program) (Tb : ℕ)
    (base N J : List Bool) (Hd : Hierarchy) (hdl : Handles) : Prop :=
  ∀ buf : List Bool, ∀ oN oJ : ℕ, base <+: buf → SliceAt buf oN N → SliceAt buf oJ J →
    buf.length < 2 ^ w →
    ∀ ax ≤ 1, ∀ i ≤ Hd.ell, ∀ b < numBlocks (axisChain Hd ax) m i,
      ∀ c ≤ deg (axisView τ Hd ax) i b, ∀ x,
        bmin (axisChain Hd ax) m i b ≤ x + 1 → x ≤ bmax (axisChain Hd ax) m i b →
        RunsQueryRO w bdP (packBits w buf)
          [m, oN, oJ, ax, i, hdl.node ax i b, hdl.addr ax i b, c, x]
          [Gpref (axisView τ Hd ax) i b x c] Tb

/-- The occupied-cell lists as words: for the column view and then the row view, for every level
`i = 0, …, ℓ` and every block `b` in left-to-right order, the degree of `b` followed by the
indices of its occupied cells' opposite blocks in increasing order (top to bottom for a column
block, left to right for a row block). -/
noncomputable def occListWords {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) : List ℕ :=
  [0, 1].flatMap (fun ax =>
    (List.range (Hd.ell + 1)).flatMap (fun i =>
      (List.range (numBlocks (axisChain Hd ax) m i)).flatMap (fun b =>
        deg (axisView τ Hd ax) i b :: (occF (axisView τ Hd ax) i b).sort (· ≤ ·))))

/-- A construction input: the packed buffer `buf` in words `0, …, oL − 1` and the word list `L`
from address `oL` on. -/
def layoutMem (w : ℕ) (buf : List Bool) (oL : ℕ) (L : List ℕ) (j : ℕ) : ℕ :=
  if j < oL then packBits w buf j else L.getD (j - oL) 0

/-- The fixed programs of the indexed representation. -/
structure RepProgs where
  ko : KOProgs
  nav : Program
  gw : Program
  bd : Program

/-- The indexed representation of §§4–5 built by §7.1: `bits = base ++ N ++ D ++ J` with the
components at bit offsets `0, oN, oD, oJ`, where `base` is a retained Kozma–Opler
representation (operations within `T` steps, counter within `cKO · (⌊log₂⌊log₂ m⌋⌋ + 1)`), `N`
a navigation structure, `D` a gateway index and `J` boundary records, all answered within `T`
steps by the programs `Q`. The complete buffer has fewer than `2^w` bits, so each component's
operation contract applies to this actual buffer. -/
def IndexedRep {k m : ℕ} (π : Equiv.Perm (Fin k)) (w : ℕ) (τ : Equiv.Perm (Fin m))
    (Q : RepProgs) (T cKO : ℕ) (bits : List Bool) (oN oD oJ : ℕ) : Prop :=
  bits.length < 2 ^ w ∧ ∃ (base N D J : List Bool) (Hd : Hierarchy) (hdl : Handles),
    bits = base ++ N ++ D ++ J ∧ oN = base.length ∧ oD = oN + N.length ∧ oJ = oD + D.length ∧
    KOInterface π w τ Q.ko T cKO base Hd hdl ∧
    NavSpec w τ Q.nav T base N Hd hdl ∧
    GatewaySpec w τ Q.gw T base N D Hd ∧
    BoundarySpec w τ Q.bd T base N J Hd hdl

end PatternRangeCounting1593.RangeCounting


