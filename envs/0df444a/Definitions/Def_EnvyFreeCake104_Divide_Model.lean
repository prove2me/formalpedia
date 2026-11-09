-- Prove2me | Definitions.Def_EnvyFreeCake104_Divide_Model
-- name    : EnvyFreeCake104_Divide_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:56:04.947881+00:00
-- url     : https://prove2.me/theorems/5a5d95f2-bb71-4507-a2fe-4e1ea9159579
-- title:
--   Cake, valuations, ordered pieces, prefixes and suffixes, allocations, domination
-- statement:
--   The **cake** is the interval $[0,1]$. Each agent $i$ has a **valuation**: a density $v_i:[0,1]\to\mathbb R$ that is nonnegative and integrable on $[0,1]$; her value of a set $S$ is
--   $$V_i(S)=\int_{S\cap[0,1]} v_i(x)\,dx .$$
--   No boundedness, continuity or positivity is assumed, and normalization $V_i([0,1])=1$ is imposed only where the paper imposes it.
--
--   An **interval** is given by endpoints $a\le b$ and denotes $[a,b)$, except that a nondegenerate interval ending at $1$ denotes $[a,1]$. A **piece** is a finite *ordered* list of intervals; its set is the union of its intervals, and it is well formed when all endpoints lie in $[0,1]$ and its intervals are pairwise disjoint. The order of the intervals need not be left to right.
--
--   A **position** $(k,x)$ of a piece is an interval index $k$ (0-based) and a point $x\in[a_k,b_k]$. The **prefix** up to $(k,x)$ consists of the first $k$ intervals and $[a_k,x)$; the **suffix** after $(k,x)$ consists of $[x,b_k)$ and the remaining intervals, in order. A set $S$ is a suffix of a piece $P$ if $S=\emptyset$ or $S$ is the set of the suffix of $P$ after some position.
--
--   For a set $N$ of agents and a cake $C$: a **partial allocation** of $C$ gives each $i\in N$ a bundle $A_i\subseteq C$, bundles of distinct agents being disjoint; its **residue** is $C\setminus\bigcup_{i\in N}A_i$; it is **complete** if $\bigcup_{i\in N}A_i=C$; it is **envy-free** if $V_i(A_i)\ge V_i(A_j)$ for all $i,j\in N$. In $(X,R)$ agent $i$ **dominates** $j$ if
--   $$V_i(X_i)\ge V_i(X_j)+V_i(R),$$
--   and a **dominated group** is a set $E$ with $\emptyset\ne E\subsetneq N$ such that every agent of $N\setminus E$ dominates every agent of $E$ (Definition 1).
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Allocations in the predicates are set-valued families indexed by an agent type, restricted to the participating set $N$. A degenerate interval $[a,a)$ is empty, also for $a=1$.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.1, 4, §1 (model), §1.3 (Pieces; Prefixes, suffixes and prefix cuts), §2 Definition 1 and dominated group

import Mathlib

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-! # The cake-cutting model of Psomas, *Cutting a Cake For Human Consumption*

Source: STOC 2027 submission #104, p.1 (model) and §1.3, p.4 (conventions), §2, p.4
(Definition 1 and dominated groups).

The cake is `[0,1] ⊆ ℝ`. -/

/-- A valuation: a density `v : [0,1] → ℝ` that is nonnegative and integrable on `[0,1]`
(p.1). No boundedness, continuity, positivity or normalization is assumed; normalization
`∫₀¹ v = 1` is imposed only where the paper imposes it (the top-level call). -/
structure Valuation where
  density : ℝ → ℝ
  nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ density x
  integrable : MeasureTheory.IntegrableOn density (Set.Icc (0 : ℝ) 1)

/-- `V(S) = ∫_{S ∩ [0,1]} v`, the value of a set `S` of points of the cake (p.1). -/
noncomputable def Valuation.value (v : Valuation) (S : Set ℝ) : ℝ :=
  ∫ x in S ∩ Set.Icc (0 : ℝ) 1, v.density x

/-- An interval of the cake, given by its endpoints `a ≤ b`. -/
structure Interval where
  a : ℝ
  b : ℝ

instance : Inhabited Interval := ⟨⟨0, 0⟩⟩

/-- §1.3: intervals are half-open `[a,b)`, except the interval ending at `1`, which includes
that endpoint. A degenerate interval `[a,a)` is empty, also when `a = 1`. -/
def Interval.toSet (I : Interval) : Set ℝ :=
  if I.b = 1 ∧ I.a < I.b then Set.Icc I.a I.b else Set.Ico I.a I.b

/-- A piece: a finite **ordered** list of intervals (§1.3: "every piece comes with a list of
its intervals in a specified order, which need not be their order on [0,1]"). -/
abbrev Piece := List Interval

/-- The set of points covered by a piece: the union of its intervals. -/
def Piece.toSet (P : Piece) : Set ℝ := {x | ∃ I ∈ P, x ∈ I.toSet}

/-- A well-formed piece: every interval satisfies `0 ≤ a ≤ b ≤ 1`, and its intervals are
pairwise disjoint ("a finite union of disjoint intervals of [0,1]", p.1). -/
def Piece.WF (P : Piece) : Prop :=
  (∀ I ∈ P, 0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1) ∧ P.Pairwise (fun I J => Disjoint I.toSet J.toSet)

/-- A position in a piece: the `k`-th interval (0-based) and a point `x` of it. -/
abbrev Pos := ℕ × ℝ

/-- A valid position of `P`: `k < length P` and `a_k ≤ x ≤ b_k`. -/
def Piece.ValidPos (P : Piece) (p : Pos) : Prop :=
  p.1 < P.length ∧ (P.getD p.1 default).a ≤ p.2 ∧ p.2 ≤ (P.getD p.1 default).b

/-- The prefix of `P` up to position `(k, x)`: its first `k` intervals (0-based) followed by
the initial part `[a_k, x)` of interval `k` (§1.3). For `x = b_k` this is the whole of
interval `k`. Out-of-range positions give the whole piece. -/
def prefixList (P : Piece) (p : Pos) : Piece :=
  if p.1 < P.length then P.take p.1 ++ [⟨(P.getD p.1 default).a, p.2⟩] else P

/-- The suffix of `P` after position `(k, x)`: what remains after removing `prefixList P p`,
namely `[x, b_k)` followed by intervals `k+1, k+2, …` in the piece's order (§1.3). -/
def suffixList (P : Piece) (p : Pos) : Piece :=
  if p.1 < P.length then ⟨p.2, (P.getD p.1 default).b⟩ :: P.drop (p.1 + 1) else []

/-- `S` is (the set of) a suffix of the piece `P` (§1.3). The empty piece is a suffix of every
piece; the whole piece is the suffix after position `(0, a_0)`. -/
def IsSuffix (S : Set ℝ) (P : Piece) : Prop :=
  S = ∅ ∨ ∃ p : Pos, P.ValidPos p ∧ S = (suffixList P p).toSet

/-! ## Allocations (p.1 and §2) -/

section Alloc

variable {ι : Type}

/-- A partial allocation of the cake `C` among the agents of `N`: every bundle `A i`
(`i ∈ N`) lies inside `C`, and bundles of distinct agents are disjoint (p.1). -/
def IsPartialAlloc (N : Finset ι) (C : Set ℝ) (A : ι → Set ℝ) : Prop :=
  (∀ i ∈ N, A i ⊆ C) ∧ ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (A i) (A j)

/-- The residue of `A` in `C`: `C \ ⋃_{i ∈ N} A i` (p.1). -/
def residue (N : Finset ι) (C : Set ℝ) (A : ι → Set ℝ) : Set ℝ :=
  C \ ⋃ i ∈ N, A i

/-- Completeness: `⋃_{i ∈ N} A i = C` (p.1). -/
def IsComplete (N : Finset ι) (C : Set ℝ) (A : ι → Set ℝ) : Prop :=
  (⋃ i ∈ N, A i) = C

/-- Envy-freeness: `V_i(A_i) ≥ V_i(A_j)` for all `i, j ∈ N` (p.1). -/
def EnvyFree (V : ι → Valuation) (N : Finset ι) (A : ι → Set ℝ) : Prop :=
  ∀ i ∈ N, ∀ j ∈ N, (V i).value (A j) ≤ (V i).value (A i)

/-- Definition 1 (p.4): in the partial allocation `X` with residue `R`, agent `i` dominates
agent `j` if `V_i(X_i) ≥ V_i(X_j) + V_i(R)`. -/
def Dominates (V : ι → Valuation) (X : ι → Set ℝ) (R : Set ℝ) (i j : ι) : Prop :=
  (V i).value (X j) + (V i).value R ≤ (V i).value (X i)

/-- A dominated group of `(X, R)` (p.4): a set `E` of agents with `∅ ≠ E ⊊ N` such that every
agent of `N \ E` dominates every agent of `E`. -/
def IsDominatedGroup (V : ι → Valuation) (N : Finset ι) (X : ι → Set ℝ) (R : Set ℝ)
    (E : Finset ι) : Prop :=
  E ⊆ N ∧ E.Nonempty ∧ E ≠ N ∧ ∀ i ∈ N, i ∉ E → ∀ j ∈ E, Dominates V X R i j

end Alloc

end EnvyFreeCake104.Divide


