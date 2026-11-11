-- Prove2me | Definitions.Def_DynLZ77_Main_Structure
-- name    : DynLZ77_Main_Structure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:20:47.968993+00:00
-- url     : https://prove2.me/theorems/5adea609-2914-43d1-bb96-296ed35f450a
-- title:
--   Periods and runs, irreducible LPF′ positions $\mathrm{Ired}_S$, the LPF′-tree and its trimmed tree, and $I$-local $\tau$-synchronizing sets
-- statement:
--   An integer $p\ge1$ is a **period** of $S[1..n]$ if $S[i]=S[i+p]$ for every $i\in[1..n-p]$; $\mathrm{per}(S)$ is the smallest period (every $p>n$ is a period, so $\mathrm{per}(\varepsilon)=1$). $S$ is **highly periodic** if $|S|\ge 3\,\mathrm{per}(S)$. A **run** with period $p$ is a substring $R=S[a..b]$ with $\mathrm{per}(R)=p$, $R$ periodic ($\mathrm{per}(R)\le|R|/2$), $S[a-1]\ne S[a-1+p]$ and $S[b+1]\ne S[b+1-p]$, a comparison involving an undefined position counting as satisfied (`IsRun`).
--
--   The **irreducible LPF′ positions** of $S$ are
--   $$\mathrm{Ired}_S=\{1\}\cup\{\,i\in[2..n] \mid i+\mathrm{LPF}'_S(i)\ne i-1+\mathrm{LPF}'_S(i-1)\,\},$$
--   the positions at which the non-decreasing sequence $i+\mathrm{LPF}'_S(i)$ is not a unit step from its predecessor. (This is the §8 definition with $\mathrm{LPF}'$; the overview on p. 11 uses $\mathrm{LPF}$.)
--
--   The **LPF′-tree** $T_S$ has nodes $[1..n+1]$, root $n+1$, and an edge from each $i\in[n]$ to its parent $i+\mathrm{LPF}'_S(i)$. $\mathrm{depth}_S(i)$ is the number of edges from $i$ to the root, `pathNode S k` the node reached from $1$ after $k$ edges, `IsLeaf S v` says $v$ has no child, and `internalNodes S` is the set of nodes with at least one child, i.e. the node set of the **trimmed tree** $\mathrm{trimmed}(T_S)$ ($|\mathrm{trimmed}(T_S)|$ is its number of nodes).
--
--   For a string $T[1..n]$, $I\subseteq[1..n]$ and an integer $\tau\in[1..\lfloor n/2\rfloor]$ let $\mathrm{Close}_\tau(I)=\bigcup_{i\in I}[i-10\tau..i+10\tau]$. A set $\mathsf S$ is an **$I$-local $\tau$-synchronizing set** of $T$ (Definition 8.3) if
--   1. (consistency) for all $i,j\in\mathrm{Close}_\tau(I)\cap[1..n-2\tau+1]$, $T[i..i+2\tau-1]=T[j..j+2\tau-1]$ implies ($i\in\mathsf S\iff j\in\mathsf S$);
--   2. (density) for every $i\in\mathrm{Close}_\tau(I)\cap[1..n-3\tau+2]$, $[i..i+\tau)\cap\mathsf S=\emptyset$ if and only if $\mathrm{per}(T[i..i+3\tau-2])\le\tau/3$.
--
--   These objects carry Lemmas 1.2, 8.4, 8.8, 9.7, Observation 4.8 and Claims 8.10–8.12.
--
--   **Formalization Note.** $\mathrm{Ired}_S$ is a set of positions of $S$, so $\mathrm{Ired}_\varepsilon=\emptyset$. Positions in $\mathrm{Close}_\tau(I)$ are natural numbers (the negative part of an interval $[i-10\tau..\,]$ never meets $[1..n]$); the comparison $\mathrm{per}\le\tau/3$ is over the reals; $n-2\tau+1$ and $n-3\tau+2$ are written $n+1-2\tau$ and $n+2-3\tau$ in natural numbers, which give the empty range exactly when the paper's range is empty. The definition file contains the one-line lemma `exists_isPeriod` (the period $|S|+1$) that makes `per` well defined.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 15 (PDF 17) periods and runs; p. 18 (PDF 20) LPF′-tree; p. 47 (PDF 49) Ired_S; p. 48 (PDF 50) Definition 8.3; p. 49 (PDF 51) highly periodic; pp. 53-54 (PDF 55-56) trimmed tree, Definition 9.1

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings

set_option autoImplicit false

namespace DynLZ77.Main

/-!
# Periods, runs, irreducible LPF′ positions, the LPF′-tree and local synchronizing sets

Boneh, Fried, Golan, Kraus, *Dynamic LZ77: No Space for Improvement*, STOC 2027 submission
(manuscript sha256 2a15e146…): periods and runs, p. 15 (PDF 17); the LPF′-tree, p. 18 (PDF 20);
`Ired_S`, p. 47 (PDF 49); Definition 8.3, p. 48 (PDF 50); highly periodic strings, p. 49
(PDF 51); trimmed trees and tree oracles, pp. 53-54 (PDF 55-56).

**Formalization Note.**
* `p ≥ 1` is a period of `S` if `S[i] = S[i + p]` for every `i ∈ [1..n − p]` (no upper bound on
  `p`, as on p. 15); `per S` is the smallest period, so `per [] = 1` and `per S ≤ max(|S|, 1)`.
* A run `S[a..b]` with period `p`: `per(S[a..b]) = p`, periodic (`2·p ≤ |S[a..b]|`, i.e.
  `per ≤ n/2`), and `S[a−1] ≠ S[a−1+p]`, `S[b+1] ≠ S[b+1−p]`, a comparison with an undefined
  position (`charAt = none`) counting as satisfied.
* `Ired S = {1} ∪ {i ∈ [2..n] | i + LPF′(i) ≠ i − 1 + LPF′(i − 1)}`, as a set of positions of
  `S` (the §8 version with LPF′, p. 47). Position `1` exists only when `n ≥ 1`, so
  `Ired [] = ∅`.
* The LPF′-tree `T_S` has nodes `[1..n+1]`, root `n + 1`, and the edge `i → i + LPF′_S(i)` for
  `i ∈ [1..n]`. `depth S i` is the number of edges from `i` to the root; `pathNode S k` is the
  node reached from `1` after `k` edges. `internalNodes S` is the node set of `trimmed(T_S)`
  (nodes with at least one child), and `IsLeaf S v` says `v` has no child.
* `Close_τ(I) = ⋃_{i ∈ I} [i − 10τ..i + 10τ]` (natural-number positions; the negative part of the
  paper's integer interval is irrelevant, every use intersects with `[1..·]`). The density test
  `per(T[i..i + 3τ − 2]) ≤ τ/3` is over the reals. Upper ends `n − 2τ + 1` and `n − 3τ + 2` are
  written `n + 1 − 2τ` and `n + 2 − 3τ` (natural subtraction: the range is empty exactly when the
  paper's is).
-/

variable {α : Type}

/-- `p` is a period of `S`: `p ≥ 1` and `S[i] = S[i + p]` for every `i ∈ [1..|S| − p]`. -/
def IsPeriod (S : List α) (p : ℕ) : Prop :=
  1 ≤ p ∧ ∀ i : ℕ, 1 ≤ i → i + p ≤ S.length → S[i - 1]? = S[i + p - 1]?

/-- Every string has the period `|S| + 1`. -/
theorem exists_isPeriod (S : List α) : ∃ p, IsPeriod S p :=
  ⟨S.length + 1, by omega, fun i _ h => by omega⟩

open Classical in
/-- `per(S)`, the smallest period of `S`. -/
noncomputable def per (S : List α) : ℕ := Nat.find (exists_isPeriod S)

/-- `S` is highly periodic: `|S| ≥ 3·per(S)`. -/
def HighlyPeriodic (S : List α) : Prop := 3 * per S ≤ S.length

/-- `S[a..b]` is a run of `S` with period `p`. -/
def IsRun (S : List α) (a b p : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ S.length ∧ per (sub S a b) = p ∧ 2 * p ≤ b + 1 - a ∧
    charAt S (a - 1) ≠ charAt S (a - 1 + p) ∧ charAt S (b + 1) ≠ charAt S (b + 1 - p)

variable [DecidableEq α]

/-- `Ired_S`, the irreducible LPF′ positions (p. 47). -/
def Ired (S : List α) : Finset ℕ :=
  (Finset.Icc 1 S.length).filter (fun i => i = 1 ∨ i + lpf' S i ≠ i - 1 + lpf' S (i - 1))

/-- The parent `i + LPF′_S(i)` of a node `i ∈ [1..n]` in the LPF′-tree. -/
def treeParent (S : List α) (i : ℕ) : ℕ := i + lpf' S i

/-- `depth_S(i)`: the number of edges from node `i` to the root `n + 1` of the LPF′-tree. -/
def depth (S : List α) (i : ℕ) : ℕ :=
  if 1 ≤ i ∧ i ≤ S.length then depth S (i + lpf' S i) + 1 else 0
termination_by S.length + 1 - i
decreasing_by
  have h1 : 1 ≤ lpf' S i := le_max_right _ _
  omega

/-- The node reached from node `1` after `k` edges of the LPF′-tree (for `k ≤ depth_S(1)`). -/
def pathNode (S : List α) (k : ℕ) : ℕ := (treeParent S)^[k] 1

/-- `v` is a leaf of the LPF′-tree: no `j ∈ [1..n]` has parent `v`. -/
def IsLeaf (S : List α) (v : ℕ) : Prop :=
  ¬ ∃ j ∈ Finset.Icc 1 S.length, treeParent S j = v

/-- The internal nodes of the LPF′-tree (the nodes with at least one child, i.e. the parents
`j + LPF′_S(j)` of the nodes `j ∈ [1..n]`): the node set of `trimmed(T_S)`. -/
def internalNodes (S : List α) : Finset ℕ :=
  (Finset.Icc 1 S.length).image (treeParent S)

/-- `Close_τ(I) = ⋃_{i ∈ I} [i − 10τ..i + 10τ]`. -/
def close (τ : ℕ) (I : Finset ℕ) : Finset ℕ :=
  I.biUnion (fun i => Finset.Icc (i - 10 * τ) (i + 10 * τ))

/-- `Sy` is an `I`-local `τ`-synchronizing set of `T` (Definition 8.3): consistency and density
for the positions of `Close_τ(I)`. -/
def IsLocalSyncSet (T : List α) (I : Finset ℕ) (τ : ℕ) (Sy : Finset ℕ) : Prop :=
  (∀ i ∈ close τ I ∩ Finset.Icc 1 (T.length + 1 - 2 * τ),
    ∀ j ∈ close τ I ∩ Finset.Icc 1 (T.length + 1 - 2 * τ),
      sub T i (i + 2 * τ - 1) = sub T j (j + 2 * τ - 1) → (i ∈ Sy ↔ j ∈ Sy)) ∧
  (∀ i ∈ close τ I ∩ Finset.Icc 1 (T.length + 2 - 3 * τ),
    ((∀ x ∈ Finset.Ico i (i + τ), x ∉ Sy) ↔
      ((per (sub T i (i + 3 * τ - 2)) : ℝ) ≤ (τ : ℝ) / 3)))

end DynLZ77.Main


