-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Encoding
-- name    : FasterWCTFPTAS_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:51.398713+00:00
-- url     : https://prove2.me/theorems/fcbeb926-d1df-4de3-99b9-c63b33086bc1
-- title:
--   Input and output encodings for instances, point sets and selected subsets
-- statement:
--   All inputs and outputs of programs are lists of real numbers (see the machine definition). The number of machines $m$ is never an input: programs are chosen after $m$ is fixed.
--
--   1. A scheduling instance with accuracy $\varepsilon$ is the list $[\varepsilon,p_1,\dots,p_n,w_1,\dots,w_n]$.
--   2. A point $(a,b)\in\mathbb R^{m-1}\times\mathbb R$ is written as its $m$ coordinates $[a_1,\dots,a_{m-1},b]$; a list of $N$ points is the concatenation of their coordinates.
--   3. The input of an $\varepsilon$-kernel computation is $[\varepsilon]$ followed by the points; the input of a relaxed-representative-set computation is $[\delta,A,B,X]$ followed by the points.
--   4. An output assignment $\sigma$ is the list $[\sigma(1),\dots,\sigma(n)]$ of machine indices in $\{0,\dots,m-1\}$; an output subset of the input points is the list of their indices $0,\dots,N-1$ (any order, repetitions allowed), and the selected set is the set of points with those indices.
--
--   These encodings fix how the running-time statements of Lemmas 3.4–3.6, Corollary 4.7 and Theorem 1.1 are read on the machine.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 11 (PDF p. 12), Lemmas 3.4–3.6 and Theorem 1.1; p. 15 (PDF p. 16), Corollary 4.7 (encodings not specified in the source)

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Geometry

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-!
# Input and output encodings on the machine

All inputs are lists of reals, placed in memory cells `1, 2, …` (cell `0` holds the length);
all outputs are lists of reals read from memory cells `-1, -2, …` (see `Machine`). The number of
machines `m` is never part of an input: programs are chosen after `m` is fixed.

* A scheduling instance with accuracy `ε`: `[ε, p_1, …, p_n, w_1, …, w_n]`.
* A point of `ℝ^m = ℝ^{m−1} × ℝ` is written as its `m` coordinates `[a_1, …, a_{m−1}, b]`; a list
  of `N` points as the concatenation of their coordinates.
* An ε-kernel input: `[ε]` followed by the points.
* A relaxed-representative-set input: `[δ, A, B, X]` followed by the points.
* An output assignment `σ` is the list of machine indices `[σ(1), …, σ(n)]`, machines numbered
  `0, …, m−1`; an output subset of the input points is the list of their indices `0, …, N−1` in
  the input (in any order, repetitions allowed).
-/

/-- The input `[ε, p_1, …, p_n, w_1, …, w_n]` of a scheduling instance. -/
def schedInput {n : ℕ} (ε : ℝ) (p w : Fin n → ℝ) : List ℝ :=
  ε :: List.ofFn p ++ List.ofFn w

/-- A list of natural numbers written as reals. -/
noncomputable def natOutput (l : List ℕ) : List ℝ := l.map fun k => (k : ℝ)

/-- The output encoding `[σ(1), …, σ(n)]` of an assignment (machines numbered `0, …, m−1`). -/
noncomputable def assignmentOutput {n m : ℕ} (σ : Fin n → Fin m) : List ℝ :=
  natOutput (List.ofFn fun j => (σ j : ℕ))

/-- The `m` coordinates `[a_1, …, a_{m−1}, b]` of a point `(a, b)`. -/
def ptCoords {m : ℕ} (s : Pt m) : List ℝ := List.ofFn s.1 ++ [s.2]

/-- The coordinates of `N` points, concatenated. -/
def pointsCoords {m N : ℕ} (pts : Fin N → Pt m) : List ℝ :=
  (List.ofFn fun i => ptCoords (pts i)).flatten

/-- The input `[ε]` followed by `N` points of `ℝ^m`. -/
def kernelInput {m N : ℕ} (ε : ℝ) (pts : Fin N → Pt m) : List ℝ :=
  ε :: pointsCoords pts

/-- The input `[δ, A, B, X]` followed by `N` points of `ℝ^m`. -/
def repInput {m N : ℕ} (δ A B X : ℝ) (pts : Fin N → Pt m) : List ℝ :=
  δ :: A :: B :: X :: pointsCoords pts

/-- The output encoding of a list of indices of input points. -/
noncomputable def indexOutput {N : ℕ} (idx : List (Fin N)) : List ℝ :=
  natOutput (idx.map fun i => (i : ℕ))

/-- The set of input points selected by a list of indices. -/
def idxSet {m N : ℕ} (pts : Fin N → Pt m) (idx : List (Fin N)) : Set (Pt m) :=
  {x | ∃ i ∈ idx, pts i = x}

end FasterWCTFPTAS.Main


