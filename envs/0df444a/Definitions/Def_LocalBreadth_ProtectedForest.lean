-- Prove2me | Definitions.Def_LocalBreadth_ProtectedForest
-- name    : LocalBreadth_ProtectedForest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:09.63949+00:00
-- url     : https://prove2.me/theorems/a027af59-736c-4092-9cad-779d326d02db
-- title:
--   The protected forest with formal copies
-- statement:
--   For every $L\in\mathcal X$ and $m\ge1$ there is a **formal vertex** $a=(L,m)$ with label $L_a=L$, requirement $q_a=(b(L)-2^{-m})_+$ and threshold $s_a=(b(L)-2^{-m-1})_+$. All formal vertices are enumerated in one sequence in which $(L,m)$ appears before $(L,m+1)$. Each vertex carries a scale $N_a\ge1$ with $1/N_a\le2^{-m-1}$ and, if $s_a>0$, $s_a<b_{N_a}(L_a)$.
--
--   The **protected forest** consists of the following data, built in index order:
--
--   1. the parent of $v$, given by the parent scan on the sets $P_u$, $u<v$;
--   2. a partition of $\mathbb Z$ into consecutive intervals, the $v$-boards, coarsening the parent's, with $N_v\le|L_v\cap I|\le B_v$ on every board, where $B_v=N_v$ at a root and $B_v=N_v+B_u-1$ at a child of $u$;
--   3. for each $a\preceq v$ with $s_a>0$, a protected set $\mathrm{Prot}_a(\overline H[a,v])$ for $(L_a,N_a,s_a)$;
--   4. the total protected set
--   $$P_v=\bigcup_{\substack{a\preceq v\\s_a>0}}\Bigl(\mathrm{Prot}_a(\overline H[a,v])\cup\bigcup_{I\in\mathrm{Bad}(a,v)}(L_v\cap I)\Bigr),$$
--   where $\mathrm{Bad}(a,v)$ is the set of $a$-boards $I$ with $p(\overline H[a,v],L_a\cap I)<s_a$.
--
--   The forest supports all targets and all accuracy requirements at once, and it is what the single generator of the main theorem reads.
--
--   **Formalization Note** The paper's construction makes a free choice at each step, so each step is a field and a term of this structure is one outcome of the construction. Boards may be unbounded intervals of integers; their traces are finite. The partition's classes are given by `board v x`, the board of $x$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), §5.4, pp.31–33; §§5.8.1–5.8.3, 5.8.6, pp.37–40; eq. (21), p.33

import Mathlib
import Definitions.Def_LocalBreadth_bComb
import Definitions.Def_LocalBreadth_IsSafe
import Definitions.Def_LocalBreadth_scanParent

namespace LocalBreadth

/-- The **formal vertices** of §5.8.1, p.37: every pair `(L, m)` with `L ∈ X`, `m ≥ 1`, enumerated in one
countable sequence in which `(L, m)` appears before `(L, m + 1)`. Kleinberg, Wei, STOC 2027 submission
(manuscript sha256 f924cbfc…).

**Formalization Note.** The second coordinate `k` of `vert i` stands for the copy `m = k + 1`. -/
structure FormalEnum (X : Set (Set ℤ)) where
  /-- The enumeration of the formal vertices. -/
  vert : ℕ ≃ {L : Set ℤ // L ∈ X} × ℕ
  /-- `(L, m)` appears before `(L, m + 1)`. -/
  vert_order : ∀ (L : {L : Set ℤ // L ∈ X}) (k i j : ℕ), vert i = (L, k) → vert j = (L, k + 1) → i < j

namespace FormalEnum

variable {X : Set (Set ℤ)} (E : FormalEnum X)

/-- The language label `L_a`. -/
def L (v : ℕ) : Set ℤ := (E.vert v).1.1

/-- The copy number `m ≥ 1` of the vertex. -/
def m (v : ℕ) : ℕ := (E.vert v).2 + 1

/-- The density requirement `q_a = (b(L) − 2^{−m})⁺`. -/
noncomputable def q (v : ℕ) : ℝ := max (b X (E.L v) - (1 / 2 : ℝ) ^ E.m v) 0

/-- The safety threshold `s_a = (b(L) − 2^{−m−1})⁺`. -/
noncomputable def s (v : ℕ) : ℝ := max (b X (E.L v) - (1 / 2 : ℝ) ^ (E.m v + 1)) 0

end FormalEnum

/-- A partition of `ℤ` into consecutive intervals, given by the class `I x` of each point (p.31).

**Formalization Note.** A class may be unbounded as an interval of integers (p.32). -/
def IsBoardPartition (I : ℤ → Set ℤ) : Prop :=
  (∀ x, x ∈ I x) ∧ (∀ x y, y ∈ I x → I y = I x) ∧ ∀ x, (I x).OrdConnected

/-- `Bad(a, v)` (§5.4, p.33, with §5.8.3, p.39): the `a`-boards `I` with `p(H[a, v], L_a ∩ I) < s_a`. -/
def badBoards (L : ℕ → Set ℤ) (parent : ℕ → Option ℕ) (board : ℕ → ℤ → Set ℤ) (s : ℕ → ℝ) (a v : ℕ) :
    Set (Set ℤ) :=
  {I | (∃ x, I = board a x) ∧ pScore (chainFrom L parent a v) (L a ∩ I) < s a}

/-- The **static protected forest with formal copies**. Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…), §5.4, pp.31–33, with §§5.8.1–5.8.3, 5.8.6, pp.37–40.

**Formalization Note.** The page builds the forest by a recursion on the vertex index with a free choice
at each step (`N_a`, the boards, the protected sets). Each field is one step of that recursion, so a
term of this structure is exactly one outcome of the construction; `lemma_5_13` asserts one exists. The
data at `v` depends only on the data at earlier vertices: `scanParent` reads `P u` for `u < v` only. -/
structure ProtectedForest (X : Set (Set ℤ)) extends FormalEnum X where
  /-- The scale `N_a`. -/
  N : ℕ → ℕ
  N_pos : ∀ v, 1 ≤ N v
  /-- `1/N_a ≤ 2^{−m−1}`. -/
  N_inv : ∀ v, (1 : ℝ) / (N v : ℝ) ≤ (1 / 2 : ℝ) ^ (toFormalEnum.m v + 1)
  /-- If `s_a > 0` then `s_a < b_{N_a}(L_a)`. -/
  N_spec : ∀ v, 0 < toFormalEnum.s v → toFormalEnum.s v < bComb X (N v) (toFormalEnum.L v)
  /-- The total protected set `P_v`. -/
  P : ℕ → Finset ℤ
  /-- The parent of each vertex, by the parent scan. -/
  parent : ℕ → Option ℕ
  parent_eq : ∀ v, parent v = scanParent toFormalEnum.L P v
  /-- `board v x` is the `v`-board `I_v(x)` of `x`. -/
  board : ℕ → ℤ → Set ℤ
  /-- The population bound `B_v`. -/
  B : ℕ → ℕ
  board_partition : ∀ v, IsBoardPartition (board v)
  /-- Every `v`-board is a union of consecutive boards of the parent. -/
  board_coarsen : ∀ v u, parent v = some u → ∀ x, board u x ⊆ board v x
  board_finite : ∀ v x, (toFormalEnum.L v ∩ board v x).Finite
  board_lower : ∀ v x, N v ≤ (toFormalEnum.L v ∩ board v x).ncard
  board_upper : ∀ v x, (toFormalEnum.L v ∩ board v x).ncard ≤ B v
  /-- `B_v = N_v` at a root. -/
  B_root : ∀ v, parent v = none → B v = N v
  /-- `B_v = N_v + B_u − 1` at a child of `u`. -/
  B_child : ∀ v u, parent v = some u → B v = N v + B u - 1
  /-- `Prot a v` is the protected set `Prot_a(H[a, v])`. -/
  Prot : ℕ → ℕ → Finset ℤ
  /-- For every `a ⪯ v` with `s_a > 0`, it is a protected set for the parameters `(L_a, N_a, s_a)`. -/
  Prot_spec : ∀ a v, IsAnc parent a v → 0 < toFormalEnum.s a →
    IsProtectedSet X (N a) (toFormalEnum.s a) (chainFrom toFormalEnum.L parent a v) (Prot a v)
  /-- Eq. (21), p.33: `P_v = ⋃_{a ⪯ v, s_a > 0} (Prot_a(H[a, v]) ∪ ⋃_{I ∈ Bad(a, v)} (L_v ∩ I))`. -/
  P_eq : ∀ v, (P v : Set ℤ) = ⋃ a ∈ {a | IsAnc parent a v ∧ 0 < toFormalEnum.s a},
    ((Prot a v : Set ℤ) ∪ ⋃ I ∈ badBoards toFormalEnum.L parent board toFormalEnum.s a v,
      (toFormalEnum.L v ∩ I))

end LocalBreadth


