-- Prove2me | Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
-- name    : TarskiQuasiFPT_UpperBound_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:11.772538+00:00
-- url     : https://prove2.me/theorems/e3d69728-7125-441d-8b47-4f40c0de3e26
-- title:
--   The grid $[n]^k$, labels $\{\pm1\}$, solutions of Tarski$^*$, slices and safe functions
-- statement:
--   Fix integers $n\ge1$ and $k\ge0$. The **grid** $[n]^k=\{1,\dots,n\}^k$ carries the coordinatewise order: $x\preceq y$ iff $x_i\le y_i$ for every $i\in[k]$. A **label** is an element of $\{\pm1\}$, ordered $-1<+1$.
--
--   **Solutions (Definition 2).** For a map $f:[n]^k\to[n]^k\times\{\pm1\}$ write $f(x)=(f(x)_{1..k},\,f(x)_{k+1})$; $f$ is monotone when $x\preceq y$ implies $f(x)\preceq f(y)$ in all $k+1$ coordinates, labels included. A point $x$ is a **positive solution** of $f$ if $(x,0)\preceq f(x)$, i.e.
--   $$x\preceq f(x)_{1..k}\quad\text{and}\quad f(x)_{k+1}=+1,$$
--   a **negative solution** if $f(x)\preceq(x,0)$, i.e. $f(x)_{1..k}\preceq x$ and $f(x)_{k+1}=-1$, and a **solution** if it is either.
--
--   **Slices (§2.1).** A slice is $s\in([n]\cup\{*\})^k$. Its free coordinates are $F(s)=\{i: s_i=*\}$ and its points are $L_s=\{x\in[n]^k: x_i=s_i \text{ for } i\notin F(s)\}$. A point $x\in L_s$ is a **fixed point of $f$ on $s$** if $f(x)_i=x_i$ for all $i\in F(s)$.
--
--   **Safe functions (Definition 3).** $f:[n]^k\to[n]^k\times\{\pm1\}$ is **safe** if it is monotone and has a unique fixed point on every slice $s$ of $[n]^k$ (the all-$*$ slice and slices with no free coordinate included).
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note** A grid point is a map `Fin k → Fin n` with the pointwise order (the value $a$ stands for $a+1\in[n]$). Labels are an inductive type `Label` with constructors `neg` ($-1$) and `pos` ($+1$), ordered `neg < pos`; the product order on `Point n k × Label` is componentwise. A slice is a map `Fin k → Option (Fin n)`, `none` being $*$; membership $x\in L_s$ and being fixed on $s$ are separate predicates.
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, §1 (grid, PDF p. 2 / printed p. 1), §2.1 Definition 2 and solutions (PDF p. 4 / printed p. 3), slices and Definition 3 (PDF p. 4 / printed p. 3)

import Mathlib

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-! # The grid `[n]^k`, labels, solutions, slices and safe functions

Chen, Gao, Li, Rubinstein, Yannakakis, *Tarski Fixed Points in Quasi-FPT Queries*,
STOC 2027 submission #403, §1 (PDF p. 2) and §2.1, Definitions 2–3 (PDF pp. 4–5).

The grid `[n]^k = {1,…,n}^k` with the coordinatewise order is encoded as `Fin k → Fin n`
with Mathlib's pointwise (Pi) order; the value `a : Fin n` stands for `a + 1 ∈ [n]`. -/

/-- A point of the grid `[n]^k`: a map `Fin k → Fin n`, ordered coordinatewise
(`x ≤ y ↔ ∀ i, x i ≤ y i`). -/
abbrev Point (n k : ℕ) := Fin k → Fin n

/-- The label set `{±1}` of Definition 2: `neg` is `−1`, `pos` is `+1`, ordered `neg < pos`. -/
inductive Label where
  | neg
  | pos
  deriving DecidableEq, Repr

namespace Label

/-- The order embedding `neg ↦ 0`, `pos ↦ 1` used to transport the order of `Fin 2`. -/
def toFin : Label → Fin 2
  | neg => 0
  | pos => 1

theorem toFin_injective : Function.Injective toFin := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- `{±1}` as a two-element linear order with `−1 < +1`. -/
instance : LinearOrder Label := LinearOrder.lift' toFin toFin_injective

theorem neg_lt_pos : neg < pos := by
  show toFin neg < toFin pos
  decide

end Label

variable {n k : ℕ}

/-! ## Solutions of `Tarski*` (Definition 2)

The input of `Tarski*(n,k)` is a map `f : [n]^k → [n]^k × {±1}`, monotone for the product
order on `[n]^k × {±1}` (all `k + 1` coordinates, the label included). We write
`f x = ((f x).1, (f x).2)`. -/

/-- `x` is a **positive solution** of `f`: `(x, 0) ⪯ f(x)`, i.e. `x ⪯ (f x).1` and the label
of `x` is `+1` (the only label `≥ 0`). -/
def IsPosSolution (f : Point n k → Point n k × Label) (x : Point n k) : Prop :=
  x ≤ (f x).1 ∧ (f x).2 = Label.pos

/-- `x` is a **negative solution** of `f`: `f(x) ⪯ (x, 0)`, i.e. `(f x).1 ⪯ x` and the label
of `x` is `−1` (the only label `≤ 0`). -/
def IsNegSolution (f : Point n k → Point n k × Label) (x : Point n k) : Prop :=
  (f x).1 ≤ x ∧ (f x).2 = Label.neg

/-- `x` is a **solution** of `f`: a positive or a negative solution. -/
def IsSolution (f : Point n k → Point n k × Label) (x : Point n k) : Prop :=
  IsPosSolution f x ∨ IsNegSolution f x

/-! ## Slices and safe functions (§2.1, Definition 3) -/

/-- A slice `s ∈ ([n] ∪ {∗})^k`: `s i = none` is `∗` (a free coordinate), `s i = some a`
fixes coordinate `i` to `a`. -/
abbrev Slice (n k : ℕ) := Fin k → Option (Fin n)

/-- The set `F(s) = {i : s_i = ∗}` of free coordinates of a slice. -/
def free (s : Slice n k) : Finset (Fin k) :=
  Finset.univ.filter fun i => s i = none

/-- `x ∈ L_s`: `x` agrees with `s` on every non-free coordinate. -/
def InSlice (s : Slice n k) (x : Point n k) : Prop :=
  ∀ i : Fin k, ∀ a : Fin n, s i = some a → x i = a

/-- `x` is a **fixed point of `f` on slice `s`**: `f(x)_i = x_i` for every free coordinate
`i ∈ F(s)` (membership `x ∈ L_s` is stated separately with `InSlice`). -/
def IsSliceFixed (f : Point n k → Point n k × Label) (s : Slice n k) (x : Point n k) : Prop :=
  ∀ i : Fin k, s i = none → (f x).1 i = x i

/-- Definition 3: `f : [n]^k → [n]^k × {±1}` is **safe** if it is monotone (for the product
order, labels included) and has a unique fixed point on every slice `s` of `[n]^k`
(every slice, including the all-`∗` slice and slices without free coordinates). -/
def IsSafe (f : Point n k → Point n k × Label) : Prop :=
  Monotone f ∧ ∀ s : Slice n k, ∃! x : Point n k, InSlice s x ∧ IsSliceFixed f s x

end TarskiQuasiFPT.UpperBound


