-- Prove2me | Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
-- name    : PatternRangeCounting1593_RangeCounting_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:38.113469+00:00
-- url     : https://prove2.me/theorems/8d83e3e6-930c-4fd7-b6b8-cd0989612847
-- title:
--   Nested divisions, Kozma–Opler scales, cells, continuation states, boundary prefixes and local queries
-- statement:
--   **Scales.** For a length $m$ let $L=\lfloor m/\sqrt{\log_2 m}\rfloor$, $\omega_0=m$, $\omega_{i+1}=\lfloor\omega_i^{5/6}\rfloor$, and let $\ell$ be the least $i$ with $m/\omega_i\ge L$. The number of blocks per axis at level $i$ is $m_i=\lfloor m/\omega_i\rfloor$ for $i<\ell$ and $m_\ell=L$; $H=\sum_{i=0}^{\ell}m_i$; the **anchor level** is $a=\max\{i<\ell:\omega_i\ge(\log_2 m)^2\}$.
--
--   **Nested divisions.** A division chain of the axis $[1,m]$ assigns to each level $i\le\ell$ a partition into consecutive nonempty blocks numbered $0,1,\dots$ from left to right, one block at level $0$, each level-$(i+1)$ block inside a level-$i$ block. A hierarchy is such a chain for columns and one for rows. For a block $B$: $\min B$, $\max B$, its first child, its number of children, its parent and its one-based index among its parent's children.
--
--   **Cells.** A cell at level $i$ is $E=C\times R$ for a column block $C$ and a row block $R$ of that level; it is **occupied** if it contains a plot point. $\deg(C)$ is the number of occupied cells of $C$, listed top to bottom (for a row block, left to right). The **continuation state** of $E$ (occupied or not) is $(p(E),c(E),d(E))$ with
--   $$p(E)=|P_\tau\cap([\min C-1]\times[\min R-1])|,$$
--   $c(E)$ the number of occupied cells of $C$ strictly above $E$ and $d(E)$ the number of occupied cells of $R$ strictly to its left. For $0\le c\le\deg(C)$ and $\min C-1\le x\le\max C$,
--   $$G_C(x,c)=|S(C,c)\cap([\min C,x]\times[m])|,$$
--   where $S(C,c)$ is the set of points in the first $c$ occupied cells of $C$; $G_R(y,d)$ is the same with the axes exchanged, and $\kappa_E(x,y)=|P_\tau\cap([\min C,x]\times[\min R,y])|$. Row-block notions are column-block notions of the transposed plot with the two chains exchanged.
--
--   **Local queries.** For a column block $C$ at level $i<\ell$: child column $u$ (one-based), occupied parent cell $h$ (one-based, top to bottom), child row $v$ of that parent cell. $\mathrm{rectCount}_C(u_1,u_2,h_1,v_1,h_2,v_2)=|P_\tau\cap(I\times J)|$ where $I$ spans child columns $u_1$ to $u_2$ and $J$ runs from the first row of child row $v_1$ of cell $h_1$ to the last row of child row $v_2$ of cell $h_2$, or, when $v_2=0$ and $h_1<h_2$, to the row just before cell $h_2$. $\mathrm{nonEmpty}_C(u,h,v)$ is $1$ if that child cell is occupied, else $0$; $\mathrm{cellRank}_C(u,h,v)$ counts occupied child cells strictly above it in child column $u$. At the finest level $u_j$ are column offsets in $[1,|C|]$ and $v_j$ ranks among the occupied rows of cell $h_j$, and $\mathrm{cellOffset}_C(u,h)$ counts the points of occupied cell $h$ in the first $u$ columns of $C$. Each query comes with its admissible arguments, exactly as listed on printed p. 12.
--
--   **Gateway search.** For an anchor row block $R$ with level-$i$ ancestors $R_i$, $S_R$ is the set of column blocks $C$ at levels $i\le a$ with $C\times R_i$ occupied; $\lambda(C)$, $\eta(C)$ are the one-based ranks of the first and last anchor column blocks below $C$; the endpoints are the values $\lambda(C)$ and $\eta(C)+1$; and the gateway level of $(x,y)$ is the largest $i\le a$ with $C_i(x)\times R_i(y)$ occupied.
--
--   **Formalization Note** $\ell$ is an `sInf` and $a$ a `Nat.findGreatest`; for $m\ge1$ the set defining $\ell$ is nonempty because $\omega_i$ reaches $1$, and $a$ is used only above a threshold where the root level qualifies. `bmin`, `bmax`, `lam`, `eta` are `sInf`/`sSup` and are used only on existing blocks.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §3.3 (K1)–(K4), printed pp. 11–13 (PDF pp. 12–14); §4, printed pp. 13–16 (PDF pp. 14–17); §5.1, printed p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm

set_option autoImplicit false

namespace PatternRangeCounting1593.RangeCounting

open Classical

/-!
# Nested divisions, the Kozma–Opler scales, cells, continuation states and boundary prefixes

Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §3.3 (K1)–(K4), printed
pp. 11–13 (PDF pp. 12–14); §4, printed pp. 13–16 (PDF pp. 14–17); §5.1, printed p. 17 (PDF p. 18).

Coordinates are one-based, `1 ≤ x ≤ m`. Column `x` is a position, row `y` a value; "above" means
smaller row index, "left" smaller column index.
-/

/-! ## The scale parameters of (K1) -/

/-- The target block sizes `ω₀ = m`, `ω_{i+1} = ⌊ω_i^{5/6}⌋`. -/
noncomputable def scale (m : ℕ) : ℕ → ℕ
  | 0 => m
  | i + 1 => ⌊((scale m i : ℕ) : ℝ) ^ ((5 : ℝ) / 6)⌋₊

/-- `L = ⌊m / √(log₂ m)⌋`, the number of finest blocks per axis. -/
noncomputable def finestCount (m : ℕ) : ℕ :=
  ⌊(m : ℝ) / Real.sqrt (Real.logb 2 m)⌋₊

/-- `ℓ`, the least `i` with `m / ω_i ≥ L` (the set is nonempty for every `m ≥ 1`, since `ω_i`
reaches `1` and `L ≤ m`). -/
noncomputable def depth (m : ℕ) : ℕ :=
  sInf {i : ℕ | (finestCount m : ℝ) ≤ (m : ℝ) / (scale m i : ℝ)}

/-- `m_i`, the number of blocks per axis at level `i`: `⌊m/ω_i⌋` for ordinary levels `i < ℓ`,
and `L` at the finest level. -/
noncomputable def blocksAt (m i : ℕ) : ℕ :=
  if i < depth m then ⌊(m : ℝ) / (scale m i : ℝ)⌋₊ else finestCount m

/-- `H = ∑_{i=0}^{ℓ} m_i`. -/
noncomputable def Hsum (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (depth m + 1), blocksAt m i

/-- The anchor level `a = max{i < ℓ : ω_i ≥ (log₂ m)²}` (`Nat.findGreatest`; it is `0` when no
level qualifies, which does not happen above the threshold used in the theorems). -/
noncomputable def anchorLevel (m : ℕ) : ℕ :=
  Nat.findGreatest (fun i => i < depth m ∧ (Real.logb 2 m) ^ 2 ≤ (scale m i : ℝ)) (depth m)

/-! ## Nested divisions -/

/-- A chain of divisions of the axis `[1, m]` at levels `0, …, ℓ`, given by `f i x`, the
zero-based index of the level-`i` block containing coordinate `x`: level `0` is one block, blocks
are consecutive nonempty intervals numbered left to right (indices start at `0` at `x = 1` and
increase by `0` or `1` per step), and every level-`(i+1)` block lies inside one level-`i` block. -/
def IsDivisionChain (m ell : ℕ) (f : ℕ → ℕ → ℕ) : Prop :=
  (∀ x, 1 ≤ x → x ≤ m → f 0 x = 0) ∧
  (∀ i ≤ ell, f i 1 = 0) ∧
  (∀ i ≤ ell, ∀ x, 1 ≤ x → x < m → f i (x + 1) = f i x ∨ f i (x + 1) = f i x + 1) ∧
  (∀ i < ell, ∀ x y, 1 ≤ x → x ≤ m → 1 ≤ y → y ≤ m → f (i + 1) x = f (i + 1) y → f i x = f i y)

/-- Nested column and row divisions at levels `0, …, ell`: `cb i x` is the column block of
column `x`, `rb i y` the row block of row `y`. -/
structure Hierarchy where
  ell : ℕ
  cb : ℕ → ℕ → ℕ
  rb : ℕ → ℕ → ℕ

/-- Both axes carry a division chain on `[1, m]`. -/
def Hierarchy.Valid (m : ℕ) (Hd : Hierarchy) : Prop :=
  IsDivisionChain m Hd.ell Hd.cb ∧ IsDivisionChain m Hd.ell Hd.rb

/-- The coordinates of block `b` at level `i` of the chain `f`. -/
def blockSet (f : ℕ → ℕ → ℕ) (m i b : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun x => f i x = b)

/-- The number of blocks at level `i`, `f i m + 1`. -/
def numBlocks (f : ℕ → ℕ → ℕ) (m i : ℕ) : ℕ := f i m + 1

/-- First coordinate `min B` (`sInf`, which is `0` for a nonexistent block). -/
noncomputable def bmin (f : ℕ → ℕ → ℕ) (m i b : ℕ) : ℕ := sInf (↑(blockSet f m i b) : Set ℕ)

/-- Last coordinate `max B` (`sSup`, which is `0` for a nonexistent block). -/
noncomputable def bmax (f : ℕ → ℕ → ℕ) (m i b : ℕ) : ℕ := sSup (↑(blockSet f m i b) : Set ℕ)

/-- The zero-based index of the first child (level `i+1`) of block `b` at level `i`. -/
noncomputable def firstChild (f : ℕ → ℕ → ℕ) (m i b : ℕ) : ℕ := f (i + 1) (bmin f m i b)

/-- The number of children of block `b` at level `i`. -/
noncomputable def nChildren (f : ℕ → ℕ → ℕ) (m i b : ℕ) : ℕ :=
  f (i + 1) (bmax f m i b) + 1 - firstChild f m i b

/-- The parent (level `i-1`) of block `b` at level `i ≥ 1`. -/
noncomputable def parentOf (f : ℕ → ℕ → ℕ) (m i b : ℕ) : ℕ := f (i - 1) (bmin f m i b)

/-- The one-based index of block `b` (level `i ≥ 1`) among the children of its parent; `0` at
level `0`. -/
noncomputable def childIndex (f : ℕ → ℕ → ℕ) (m i b : ℕ) : ℕ :=
  if i = 0 then 0 else b + 1 - firstChild f m (i - 1) (parentOf f m i b)

/-! ## Oriented views, cells and occupancy

A `View` fixes which axis plays the role of "columns". The column view of `τ` is the plot with
the hierarchy's column and row divisions; the row view is the transposed plot with the two
divisions exchanged, so every row-block notion of the paper is the column-block notion of the
row view ("exchange axes"). -/

/-- A point set with a "column" chain `cb` and a "row" chain `rb` on `[1, m]`. -/
structure View where
  m : ℕ
  P : Finset (ℕ × ℕ)
  cb : ℕ → ℕ → ℕ
  rb : ℕ → ℕ → ℕ

/-- The column view of `τ` under `Hd`. -/
def colView {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) : View :=
  ⟨m, plot τ, Hd.cb, Hd.rb⟩

/-- The row view (axes exchanged). -/
def rowView {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) : View :=
  ⟨m, (plot τ).image Prod.swap, Hd.rb, Hd.cb⟩

/-- The view of axis `ax` (`0` = column blocks, otherwise row blocks). -/
def axisView {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) (ax : ℕ) : View :=
  if ax = 0 then colView τ Hd else rowView τ Hd

/-- The division chain of axis `ax` (`0` = columns). -/
def axisChain (Hd : Hierarchy) (ax : ℕ) : ℕ → ℕ → ℕ := if ax = 0 then Hd.cb else Hd.rb

/-- The cell (column block `b`, row block `b'`) at level `i` is occupied: it contains a point. -/
def occ (V : View) (i b b' : ℕ) : Prop := ∃ p ∈ V.P, V.cb i p.1 = b ∧ V.rb i p.2 = b'

/-- The row blocks of the occupied cells of column block `b` at level `i`. -/
noncomputable def occF (V : View) (i b : ℕ) : Finset ℕ :=
  (Finset.range (V.m + 1)).filter (fun b' => occ V i b b')

/-- `deg(B)`, the number of occupied cells of column block `b` at level `i`. -/
noncomputable def deg (V : View) (i b : ℕ) : ℕ := (occF V i b).card

/-- The row block of the `h`-th occupied cell of column block `b` (one-based, top to bottom). -/
noncomputable def occAt (V : View) (i b h : ℕ) : ℕ :=
  ((occF V i b).sort (· ≤ ·)).getD (h - 1) 0

/-- The cut of cell `(b, b')`: the number of occupied cells of column block `b` strictly above
row block `b'` (`c(E)`; in the row view this is `d(E)`). Defined for empty cells too. -/
noncomputable def cutAbove (V : View) (i b b' : ℕ) : ℕ := ((occF V i b).filter (· < b')).card

/-- `G_C(x, c) = |S(C, c) ∩ ([min C, x] × [m])|`: the points of column block `b` (level `i`) that
lie in its first `c` occupied cells (top to bottom) and in columns `≤ x`. -/
noncomputable def Gpref (V : View) (i b x c : ℕ) : ℕ :=
  (V.P.filter (fun p => V.cb i p.1 = b ∧ p.1 ≤ x ∧ cutAbove V i b (V.rb i p.2) < c)).card

/-- `p(E) = |P ∩ ([min C − 1] × [min R − 1])|`, the points strictly northwest of the cell. -/
noncomputable def nwCount (V : View) (i b b' : ℕ) : ℕ :=
  (V.P.filter (fun p => p.1 < bmin V.cb V.m i b ∧ p.2 < bmin V.rb V.m i b')).card

/-- `κ_E(x, y) = |P ∩ ([min C, x] × [min R, y])|`. -/
noncomputable def kappa (V : View) (i b b' x y : ℕ) : ℕ :=
  (V.P.filter (fun p => bmin V.cb V.m i b ≤ p.1 ∧ p.1 ≤ x ∧
    bmin V.rb V.m i b' ≤ p.2 ∧ p.2 ≤ y)).card

/-! ## Local queries of (K4) (column-block form; the row form is the row view) -/

/-- Above the finest level (`i < ℓ`): the column interval `I` of child columns `u₁ … u₂`. -/
noncomputable def aboveI (V : View) (i b u₁ u₂ : ℕ) : ℕ × ℕ :=
  (bmin V.cb V.m (i + 1) (firstChild V.cb V.m i b + u₁ - 1),
   bmax V.cb V.m (i + 1) (firstChild V.cb V.m i b + u₂ - 1))

/-- The row block (level `i+1`) of child row `v` of the `h`-th occupied parent cell. -/
noncomputable def childRowOf (V : View) (i b h v : ℕ) : ℕ :=
  firstChild V.rb V.m i (occAt V i b h) + v - 1

/-- Above the finest level: the row interval `J`, from the first row of child row `v₁` of parent
cell `h₁` to the last row of child row `v₂` of parent cell `h₂`; for `v₂ = 0` it ends just before
the first row of parent cell `h₂`. -/
noncomputable def aboveJ (V : View) (i b h₁ v₁ h₂ v₂ : ℕ) : ℕ × ℕ :=
  (bmin V.rb V.m (i + 1) (childRowOf V i b h₁ v₁),
   if v₂ = 0 then bmin V.rb V.m i (occAt V i b h₂) - 1
   else bmax V.rb V.m (i + 1) (childRowOf V i b h₂ v₂))

/-- The points of `V` in `[I.1, I.2] × [J.1, J.2]`. -/
def boxCount (V : View) (I J : ℕ × ℕ) : ℕ :=
  (V.P.filter (fun p => I.1 ≤ p.1 ∧ p.1 ≤ I.2 ∧ J.1 ≤ p.2 ∧ p.2 ≤ J.2)).card

/-- Admissible arguments of `rectCount_C(u₁,u₂,h₁,v₁,h₂,v₂)` above the finest level. -/
def ValidAbove (V : View) (i b u₁ u₂ h₁ v₁ h₂ v₂ : ℕ) : Prop :=
  1 ≤ u₁ ∧ u₁ ≤ u₂ ∧ u₂ ≤ nChildren V.cb V.m i b ∧
  1 ≤ h₁ ∧ h₁ ≤ h₂ ∧ h₂ ≤ deg V i b ∧
  1 ≤ v₁ ∧ v₁ ≤ nChildren V.rb V.m i (occAt V i b h₁) ∧
  ((1 ≤ v₂ ∧ v₂ ≤ nChildren V.rb V.m i (occAt V i b h₂)) ∨ (v₂ = 0 ∧ h₁ < h₂)) ∧
  (h₁ = h₂ → v₁ ≤ v₂)

/-- The answer of `rectCount_C` above the finest level: `|P ∩ (I × J)|`. -/
noncomputable def rectAboveSem (V : View) (i b u₁ u₂ h₁ v₁ h₂ v₂ : ℕ) : ℕ :=
  boxCount V (aboveI V i b u₁ u₂) (aboveJ V i b h₁ v₁ h₂ v₂)

/-- Admissible arguments `(u, h, v)` of `nonEmpty_C` and `cellRank_C`. -/
def ValidCell (V : View) (i b u h v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ nChildren V.cb V.m i b ∧ 1 ≤ h ∧ h ≤ deg V i b ∧
  1 ≤ v ∧ v ≤ nChildren V.rb V.m i (occAt V i b h)

/-- `nonEmpty_C(u, h, v)`: `1` if the child cell (child column `u`, child row `v` of parent cell
`h`) is occupied, else `0`. -/
noncomputable def nonEmptySem (V : View) (i b u h v : ℕ) : ℕ :=
  if occ V (i + 1) (firstChild V.cb V.m i b + u - 1) (childRowOf V i b h v) then 1 else 0

/-- `cellRank_C(u, h, v)`: the number of occupied child cells strictly above that child cell in
child column `u`. -/
noncomputable def cellRankSem (V : View) (i b u h v : ℕ) : ℕ :=
  cutAbove V (i + 1) (firstChild V.cb V.m i b + u - 1) (childRowOf V i b h v)

/-- At the finest level: the occupied rows of the `h`-th occupied cell of column block `b`, top
to bottom. -/
noncomputable def occRows (V : View) (i b h : ℕ) : List ℕ :=
  ((V.P.filter (fun p => V.cb i p.1 = b ∧ V.rb i p.2 = occAt V i b h)).image Prod.snd).sort
    (· ≤ ·)

/-- Admissible arguments of `rectCount_C` at the finest level (column offsets and occupied-row
ranks). -/
def ValidFinest (V : View) (i b u₁ u₂ h₁ v₁ h₂ v₂ : ℕ) : Prop :=
  1 ≤ u₁ ∧ u₁ ≤ u₂ ∧ u₂ ≤ (blockSet V.cb V.m i b).card ∧
  1 ≤ h₁ ∧ h₁ ≤ h₂ ∧ h₂ ≤ deg V i b ∧
  1 ≤ v₁ ∧ v₁ ≤ (occRows V i b h₁).length ∧ 1 ≤ v₂ ∧ v₂ ≤ (occRows V i b h₂).length ∧
  (h₁ = h₂ → v₁ ≤ v₂)

/-- The answer of `rectCount_C` at the finest level: columns `min C + u₁ − 1 … min C + u₂ − 1`,
rows from the `v₁`-th occupied row of cell `h₁` to the `v₂`-th occupied row of cell `h₂`. -/
noncomputable def rectFinestSem (V : View) (i b u₁ u₂ h₁ v₁ h₂ v₂ : ℕ) : ℕ :=
  boxCount V (bmin V.cb V.m i b + u₁ - 1, bmin V.cb V.m i b + u₂ - 1)
    ((occRows V i b h₁).getD (v₁ - 1) 0, (occRows V i b h₂).getD (v₂ - 1) 0)

/-- `cellOffset_C(u, h)`: the points of the `h`-th occupied cell in the first `u` columns of
`C`. -/
noncomputable def cellOffsetSem (V : View) (i b u h : ℕ) : ℕ :=
  (V.P.filter (fun p => V.cb i p.1 = b ∧ V.rb i p.2 = occAt V i b h ∧
    p.1 ≤ bmin V.cb V.m i b + u - 1)).card

/-! ## The gateway search of §4.2 -/

/-- The level-`i` ancestor `R_i` of anchor row block `r` (anchor level `a`). -/
noncomputable def rowAnc (Hd : Hierarchy) (m a r i : ℕ) : ℕ := Hd.rb i (bmin Hd.rb m a r)

/-- `S_R`: the marked column nodes `(i, C)`, `i ≤ a`, whose cell `C × R_i` is occupied. -/
noncomputable def markedSet {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) (a r : ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.range (a + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun ic => ic.2 < numBlocks Hd.cb m ic.1 ∧ occ (colView τ Hd) ic.1 ic.2 (rowAnc Hd m a r ic.1))

/-- The zero-based anchor column blocks descending from column block `c` at level `i`. -/
noncomputable def anchorDesc (Hd : Hierarchy) (m a i c : ℕ) : Set ℕ :=
  {j | j < numBlocks Hd.cb m a ∧ Hd.cb i (bmin Hd.cb m a j) = c}

/-- `λ(C)`: the one-based rank of the first anchor column block descending from `C`. -/
noncomputable def lam (Hd : Hierarchy) (m a i c : ℕ) : ℕ := sInf (anchorDesc Hd m a i c) + 1

/-- `η(C)`: the one-based rank of the last anchor column block descending from `C`. -/
noncomputable def eta (Hd : Hierarchy) (m a i c : ℕ) : ℕ := sSup (anchorDesc Hd m a i c) + 1

/-- The endpoints `λ(C)` and `η(C) + 1` over `C ∈ S_R`. -/
noncomputable def endpoints {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) (a r : ℕ) :
    Finset ℕ :=
  (markedSet τ Hd a r).image (fun ic => lam Hd m a ic.1 ic.2) ∪
    (markedSet τ Hd a r).image (fun ic => eta Hd m a ic.1 ic.2 + 1)

/-- The gateway level through the anchor: the largest `i ≤ a` such that the cell
`C_i(x) × R_i(y)` is occupied (`0` if none). -/
noncomputable def gatewayLevel {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) (a x y : ℕ) :
    ℕ :=
  Nat.findGreatest (fun i => occ (colView τ Hd) i (Hd.cb i x) (Hd.rb i y)) a

end PatternRangeCounting1593.RangeCounting


