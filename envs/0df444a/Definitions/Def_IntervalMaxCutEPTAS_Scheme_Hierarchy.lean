-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy
-- name    : IntervalMaxCutEPTAS_Scheme_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:21.526759+00:00
-- url     : https://prove2.me/theorems/22cbbf6f-596c-4539-aec2-f01d04de132e
-- title:
--   The hierarchy of cells, the shift, rounding, the edited graph, anchors, groups, recent and old groups (§4.2–§4.5)
-- statement:
--   Fix a rank representation $\rho$, an integer $b$ (with $\sigma=2^{-b}$, $\tau=2b$) and a shift $\theta$.
--
--   1. $M$ is the least power of two with $M\ge 2n+1$. The **cells** form the binary tree of open intervals with root $(-2M,2M)$; the cell $(\zeta,\zeta+D)$ with $D\ge2$ has children $(\zeta,\zeta+D/2)$ and $(\zeta+D/2,\zeta+D)$, and cells of length $1$ are leaves. Cells are named by heap indices (root $1$, children of $C$ are $2C,2C+1$), the depth of $C$ is $\lfloor\log_2 C\rfloor$.
--   2. $L_v=r_v-\ell_v$, the **scale** $s_v$ is the largest power of two $\le L_v$, the **home length** is $D_v=\min\{4M,s_v/\sigma\}$. With shifted endpoints $\ell_v-\theta,r_v-\theta$, a vertex is **rejected** if no cell of length $D_v$ contains $[\ell_v-\theta,r_v-\theta]$; $Z_\theta$ is the set of rejected vertices; otherwise the **home** of $v$ is that cell.
--   3. $h_v=\max\{1,\sigma s_v\}$, $A_v=h_v\lceil(\ell_v-\theta)/h_v\rceil$, $B_v=h_v\lfloor(r_v-\theta)/h_v\rfloor$, and $I_v=[A_v,B_v]$. The **edited graph** $H$ joins retained $u\ne v$ when $I_u\cap I_v\neq\emptyset$; rejected vertices are isolated.
--   4. The **anchor** $\mathrm{anc}(v)$ is reached from the home by moving to a child containing $I_v$ as long as one exists. **Groups** are classes of retained vertices with the same anchor, scale and rounded interval, each named by its least vertex.
--   5. For a cell $C$: $V_C$ is the set of retained vertices anchored in the subtree of $C$, $W(C)=|V_C|$; $A(C)$ the groups anchored at $C$; $R(C)$ (recent) and $O(C)$ (old) the groups anchored at a proper ancestor of $C$ that meet $C$ and have age $\mathrm{depth}(C)-\mathrm{depth}(\mathrm{anc}(g))$ less than $\tau$, respectively at least $\tau$.
--   6. The shift satisfies the bound of Lemma 4.2 if $\sum_{v\in Z_\theta}\deg_G(v)\le 4\sigma m$.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §4.2–§4.5 (hierarchy, shift, rounding, anchors and groups, recent and old groups), PDF p. 15 (printed p. 14); PDF pp. 16–17 (printed pp. 15–16)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

open Classical

/-! # The hierarchy, the shift, rounding, the edited graph, anchors, groups (§4.2–§4.5)

Cells are named by heap indices: the root is `1`, the children of `C` are `2C` and `2C + 1`.
The cell with heap index `C` at depth `d = ⌊log₂ C⌋` is the open interval
`(−2M + (C − 2^d)·D, −2M + (C − 2^d + 1)·D)` with `D = 4M / 2^d`.  The valid indices are
`1 ≤ C < 8M`, i.e. the `8M − 1` cells of the paper. -/

/-- `M`: the smallest power of two with `M ≥ 2n + 1`. -/
def bigM (n : ℕ) : ℕ := 2 ^ Nat.clog 2 (2 * n + 1)

/-- `C` is (the heap index of) a cell of the hierarchy. -/
def IsCell (n C : ℕ) : Prop := 1 ≤ C ∧ C < 8 * bigM n

/-- `depth(C)`, the root having depth 0. -/
def cellDepth (C : ℕ) : ℕ := Nat.log 2 C

/-- `|C|`, the length of the cell. -/
def cellLen (n C : ℕ) : ℕ := 4 * bigM n / 2 ^ cellDepth C

/-- `ζ`, the left end of the open cell `(ζ, ζ + |C|)`. -/
def cellLo (n C : ℕ) : ℤ :=
  -2 * (bigM n : ℤ) + ((C - 2 ^ cellDepth C : ℕ) : ℤ) * (cellLen n C : ℤ)

/-- `ζ + |C|`, the right end of the open cell. -/
def cellHi (n C : ℕ) : ℤ := cellLo n C + cellLen n C

/-- Leaves are the cells of length 1. -/
def IsLeaf (n C : ℕ) : Prop := cellLen n C = 1

/-- `C'` lies in the subtree of `C` (`C'` is `C` or a descendant of `C`). -/
def InSubtree (C C' : ℕ) : Prop := ∃ k : ℕ, C' / 2 ^ k = C

/-- `C` is a proper ancestor of `C'`. -/
def IsProperAncestor (C C' : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ C' / 2 ^ k = C

/-- Two cells are comparable if one lies in the subtree of the other. -/
def Comparable (C C' : ℕ) : Prop := InSubtree C C' ∨ InSubtree C' C

/-- The open cell `C` contains the closed interval `[a, b]` (for `a ≤ b`): `ζ < a` and `b < ζ + |C|`. -/
def CellContains (n C : ℕ) (a b : ℤ) : Prop := cellLo n C < a ∧ b < cellHi n C

/-- The data that §4 fixes: a rank representation `ρ`, the integer `b` (σ = 2^{-b}, τ = 2b) and a
shift `θ`. -/
structure Setup (n : ℕ) where
  ρ : RankRep n
  b : ℕ
  θ : ℕ

variable {n : ℕ} (P : Setup n)

/-- The graph `G` (of the rank representation). -/
abbrev Setup.G : SimpleGraph (Fin n) := P.ρ.graph

/-- The rank length `L_v = r_v − l_v`. -/
def rankLen (v : Fin n) : ℕ := P.ρ.r v - P.ρ.l v

/-- The scale `s_v`: the largest power of two with `s_v ≤ L_v`. -/
def scale (v : Fin n) : ℕ := 2 ^ Nat.log 2 (rankLen P v)

/-- The home length `D_v = min{4M, s_v/σ} = min{4M, s_v·2^b}`. -/
def homeLen (v : Fin n) : ℕ := min (4 * bigM n) (scale P v * 2 ^ P.b)

/-- Shifted left endpoint `l_v − θ`. -/
def sl (v : Fin n) : ℤ := (P.ρ.l v : ℤ) - (P.θ : ℤ)

/-- Shifted right endpoint `r_v − θ`. -/
def sr (v : Fin n) : ℤ := (P.ρ.r v : ℤ) - (P.θ : ℤ)

/-- `v` is rejected (for the shift `θ`): no cell of length `D_v` contains `[l_v − θ, r_v − θ]`.
(For `D_v = 4M` the only cell of that length is the root, which contains every shifted interval
when `θ < 2M`, so such a vertex is never rejected, as in the paper.) -/
def Rejected (v : Fin n) : Prop :=
  ¬ ∃ C, IsCell n C ∧ cellLen n C = homeLen P v ∧ CellContains n C (sl P v) (sr P v)

/-- `Z_θ`, the set of rejected vertices. -/
noncomputable def Z : Finset (Fin n) := Finset.univ.filter (Rejected P)

/-- The home of `v`: the cell of length `D_v` whose closure-from-the-left contains `l_v − θ`
(depth `log₂(4M) − log₂ D_v`, position `⌊(l_v − θ + 2M)/D_v⌋`); for a retained vertex it is the
cell of length `D_v` that contains the shifted interval, and for `D_v = 4M` it is the root. -/
def home (v : Fin n) : ℕ :=
  2 ^ (Nat.log 2 (4 * bigM n) - Nat.log 2 (homeLen P v)) +
    ((sl P v + 2 * (bigM n : ℤ)) / (homeLen P v : ℤ)).toNat

/-- `h_v = max{1, σ s_v} = max{1, s_v / 2^b}` (exact: `s_v` and `2^b` are powers of two, and the
natural-number quotient is `0` exactly when `σ s_v < 1`). -/
def roundUnit (v : Fin n) : ℕ := max 1 (scale P v / 2 ^ P.b)

/-- `A_v = h_v ⌈(l_v − θ)/h_v⌉` (shifted coordinates). -/
def A (v : Fin n) : ℤ := (roundUnit P v : ℤ) * ⌈((sl P v : ℚ) / (roundUnit P v : ℚ))⌉

/-- `B_v = h_v ⌊(r_v − θ)/h_v⌋` (shifted coordinates). -/
def B (v : Fin n) : ℤ := (roundUnit P v : ℤ) * ⌊((sr P v : ℚ) / (roundUnit P v : ℚ))⌋

/-- The edited graph `H` on `V(G)`: retained `u ≠ v` are adjacent iff `I_u ∩ I_v ≠ ∅`; rejected
vertices are isolated. -/
noncomputable def H : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ¬ Rejected P u ∧ ¬ Rejected P v ∧ max (A P u) (A P v) ≤ min (B P u) (B P v)
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2.1, h.2.1, by rw [max_comm, min_comm]; exact h.2.2.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

noncomputable instance : DecidableRel (H P).Adj := Classical.decRel _

/-- The descent of §4.4: from cell `C`, as long as the current cell has a child (i.e. has length
`≥ 2`) that contains `[a, b]`, move to that child; `fuel` bounds the number of steps. -/
noncomputable def descend (n : ℕ) (a b : ℤ) : ℕ → ℕ → ℕ
  | 0, C => C
  | fuel + 1, C =>
    if 2 ≤ cellLen n C ∧ CellContains n (2 * C) a b then descend n a b fuel (2 * C)
    else if 2 ≤ cellLen n C ∧ CellContains n (2 * C + 1) a b then descend n a b fuel (2 * C + 1)
    else C

/-- The anchor `anc(v)`: the cell where the descent from the home of `v` with `I_v = [A_v, B_v]`
stops (the fuel `log₂(4M) + 1` exceeds the height of the hierarchy). -/
noncomputable def anchor (v : Fin n) : ℕ :=
  descend n (A P v) (B P v) (Nat.log 2 (4 * bigM n) + 1) (home P v)

/-- The data that defines a group: anchor, scale and rounded interval. -/
noncomputable def key (v : Fin n) : ℕ × ℕ × ℤ × ℤ := (anchor P v, scale P v, A P v, B P v)

/-- The group of `v`: the retained vertices with the same anchor, scale and rounded interval. -/
noncomputable def groupOf (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => ¬ Rejected P u ∧ key P u = key P v)

/-- A group is named by its least vertex (its *id*). -/
def IsGroupRep (g : Fin n) : Prop := ¬ Rejected P g ∧ ∀ u ∈ groupOf P g, g ≤ u

/-- The set of groups, each given by its id. -/
noncomputable def groups : Finset (Fin n) := Finset.univ.filter (IsGroupRep P)

/-- The id of the group of `v` (meaningful for retained `v`). -/
noncomputable def rep (v : Fin n) : Fin n :=
  if h : (groupOf P v).Nonempty then (groupOf P v).min' h else v

/-- `|g|`, the number of vertices of the group with id `g`. -/
noncomputable def gsize (g : Fin n) : ℕ := (groupOf P g).card

/-- The group (with id) `g` meets the cell `C`: `I_g ∩ C ≠ ∅` (closed interval, open cell). -/
def Meets (g : Fin n) (C : ℕ) : Prop :=
  ∃ x : ℝ, (A P g : ℝ) ≤ x ∧ x ≤ (B P g : ℝ) ∧ (cellLo n C : ℝ) < x ∧ x < (cellHi n C : ℝ)

/-- `g ∼ g'`: distinct groups whose rounded intervals intersect. -/
def GAdj (g g' : Fin n) : Prop := g ≠ g' ∧ max (A P g) (A P g') ≤ min (B P g) (B P g')

/-- `V_C`: the retained vertices whose anchor lies in the subtree of `C`. -/
noncomputable def VC (C : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ¬ Rejected P v ∧ InSubtree C (anchor P v))

/-- `W(C) = |V_C|`. -/
noncomputable def W (C : ℕ) : ℕ := (VC P C).card

/-- `A(C)`: the own groups of `C`, i.e. the groups anchored at `C`. -/
noncomputable def own (C : ℕ) : Finset (Fin n) := (groups P).filter (fun g => anchor P g = C)

/-- The age of `g` at `C`: `depth(C) − depth(anc(g))` (used for `C` below `anc(g)`). -/
noncomputable def age (g : Fin n) (C : ℕ) : ℕ := cellDepth C - cellDepth (anchor P g)

/-- `R(C)`: groups anchored at a proper ancestor of `C`, of age `< τ = 2b` at `C`, meeting `C`. -/
noncomputable def recent (C : ℕ) : Finset (Fin n) :=
  (groups P).filter (fun g =>
    IsProperAncestor (anchor P g) C ∧ age P g C < 2 * P.b ∧ Meets P g C)

/-- `O(C)`: groups anchored at a proper ancestor of `C`, of age `≥ τ = 2b` at `C`, meeting `C`. -/
noncomputable def old (C : ℕ) : Finset (Fin n) :=
  (groups P).filter (fun g =>
    IsProperAncestor (anchor P g) C ∧ 2 * P.b ≤ age P g C ∧ Meets P g C)

/-- The bound of Lemma 4.2 for the shift `θ`: `Σ_{v ∈ Z_θ} deg_G(v) ≤ 4σm`, i.e.
`2^b · Σ_{v ∈ Z_θ} deg_G(v) ≤ 4m`. -/
def GoodShift : Prop :=
  2 ^ P.b * ∑ v ∈ Z P, P.G.degree v ≤ 4 * P.G.edgeFinset.card

end IntervalMaxCutEPTAS.Scheme


