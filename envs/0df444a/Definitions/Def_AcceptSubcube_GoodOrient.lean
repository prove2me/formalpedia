-- Prove2me | Definitions.Def_AcceptSubcube_GoodOrient
-- name    : AcceptSubcube_GoodOrient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:46.510213+00:00
-- url     : https://prove2.me/theorems/561e43a0-82d9-4692-ac7b-6856476f5eac
-- title:
--   One-inclusion graph orientations and the guarantee of Lemma 3.2
-- statement:
--   The **one-inclusion graph** of a finite family $F\subseteq\{0,1\}^T$ has vertex set $F$ and joins $y$ and $y\oplus e_i$ when both lie in $F$; that edge has **direction** $i$. An **orientation** directs every edge one way; the **outdegree** of $y$ is the number of edges at $y$ directed away from it.
--
--   An **orientation rule** receives a labelled coordinate set $T$ (a list of distinct variable labels) and a family on $T$ given explicitly as a list of patterns, and returns an orientation as a list of directed edges (tail, direction). The rule has the **guarantee of Lemma 3.2** if, for every $T$ and $F$, its output is an orientation of the one-inclusion graph of $F$ of maximum outdegree at most $\mathrm{VCdim}(F)$.
--
--   Lemma 3.3's recovery procedure predicts a withheld coordinate by the head of an edge under such an orientation, fixed before the coordinate is chosen (Example 3.5).
--
--   **Formalization Note** "If $\mathrm{VCdim}(F)\le v$ then maximum outdegree $\le v$", for every $v$, is the bound by $\mathrm{VCdim}(F)$. A rule is a function of $(T,F)$, so its output depends only on them, the property the paper requires (p.12).
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §3.2, p.12 (one-inclusion graph, Lemma 3.2); Example 3.5, p.14

import Mathlib
import Definitions.Def_AcceptSubcube_FK

namespace AcceptSubcube

/-- `y ⊕ e_i`: flip coordinate `i`. -/
def flipAt {ι : Type*} [DecidableEq ι] (y : ι → Bool) (i : ι) : ι → Bool :=
  Function.update y i (!y i)

/-- **Orientation of the one-inclusion graph** of `F`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §3.2, p.12: "The one-inclusion graph of a
finite family F ⊆ {0,1}^T has vertex set F and joins two members at Hamming distance one; the edge
between y and y ⊕ e_i … has direction i."

`O y i = true` means that the edge of direction `i` at `y` (present when `y, y ⊕ e_i ∈ F`) is
oriented away from `y`. An orientation orients every edge exactly one way. -/
def IsOrientation {ι : Type*} [DecidableEq ι] (F : Finset (ι → Bool))
    (O : (ι → Bool) → ι → Bool) : Prop :=
  ∀ y ∈ F, ∀ i, flipAt y i ∈ F → O y i = !O (flipAt y i) i

/-- Outdegree of `y` under `O`: the number of edges at `y` oriented away from it. -/
def outdeg {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset (ι → Bool))
    (O : (ι → Bool) → ι → Bool) (y : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun i => flipAt y i ∈ F ∧ O y i = true)).card

/-- The family on `d` coordinates given explicitly by a list of patterns (patterns of the wrong
length are ignored). -/
def famOf (d : ℕ) (L : List (List Bool)) : Finset (Fin d → Bool) :=
  Finset.univ.filter (fun y => List.ofFn y ∈ L)

/-- An orientation given explicitly as the list of its directed edges `(tail, direction)`: the edge
of direction `i` at `y` is oriented away from `y` iff `(y, i)` is listed. -/
def orientOf (d : ℕ) (out : List (List Bool × ℕ)) : (Fin d → Bool) → Fin d → Bool :=
  fun y i => decide ((List.ofFn y, (i : ℕ)) ∈ out)

/-- **The guarantee of Lemma 3.2** for an orientation rule `orient` that receives the labeled
coordinate set `T` (a list of distinct variable labels) and the family `F ⊆ {0,1}^T` (a list of
patterns, coordinate `j` being variable `T_j`): its output is an orientation of the one-inclusion
graph of `F` of maximum outdegree at most `VCdim(F)`.

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.2, p.12.

**Formalization Note.** "If VCdim(F) ≤ v … maximum outdegree at most v" for every `v` is the same as
maximum outdegree at most `VCdim(F)`. Since `orient` is a function of `(T, F)`, its output
"depends only on the labeled coordinate set T and on F" (p.12; Example 3.5, p.14). -/
def GoodOrient (orient : List ℕ × List (List Bool) → List (List Bool × ℕ)) : Prop :=
  ∀ (T : List ℕ) (L : List (List Bool)), T.Nodup →
    IsOrientation (famOf T.length L) (orientOf T.length (orient (T, L))) ∧
    ∀ y ∈ famOf T.length L,
      outdeg (famOf T.length L) (orientOf T.length (orient (T, L))) y ≤
        (toSets (famOf T.length L)).vcDim

end AcceptSubcube


