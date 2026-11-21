-- Prove2me | Definitions.Def_blowup_lattice_27
-- name    : blowup_lattice_27
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T13:50:31.370723+00:00
-- url     : https://prove2.me/theorems/fe8fcc18-6fb5-4130-a3d8-b5fa45e9c97b
-- title:
--   The blowup Picard lattice and the $27$ classes
-- statement:
--   This file models the Picard lattice of $X=\mathrm{Bl}_{p_1,\dots,p_6}\mathbb{P}^2$, the blowup of the projective plane at six sufficiently general points, purely as an abelian group with a bilinear form.
--
--   Following the source, every class is written $D=aL-\sum_{i=1}^6 b_iE_i$, where $L$ is the class of a line avoiding the six points and $E_i$ is the exceptional divisor over $p_i$. It is represented by the coordinate pair $(a,b)\in\mathbb{Z}\times(\mathrm{Fin}\,6\to\mathbb{Z})$ (`BlLattice`). The intersection pairing is
--   $$(a,b)\cdot(a',b')=aa'-\sum_{i=1}^6 b_ib_i',$$
--   which encodes the source's rules $L^2=1$, $L\cdot E_i=0$, $E_i\cdot E_j=0$ for $i\ne j$, and $E_i^2=-1$.
--
--   Named classes: `classL` $=L$; `classE i` $=E_i$ (whose $b$-coordinate is $-1$ at $i$, since $D=aL-\sum b_iE_i$); `classH` $=H=3L-\sum_iE_i$, the hyperplane class of the cubic embedding; `classK` $=K_X=-3L+\sum_iE_i$, the canonical class; `lineClass i j` $=L-E_i-E_j$, the class of the line through $p_i$ and $p_j$; and `conicClass i` $=2L-\sum_{k\ne i}E_k$, the class of the conic through the five points other than $p_i$.
--
--   `the27` is the finite set of the $27$ classes exhibited by the source: the $6$ exceptional divisors, the $15$ pair-lines (one for each unordered pair $\{i,j\}$), and the $6$ five-point conics.
--
--   **Formalization Note.** This is a concrete lattice, not a geometric blowup: it carries exactly the intersection rules the source uses and no further axioms. The sign convention $D=aL-\sum b_iE_i$ means the exceptional class $E_i$ has $b_i=-1$; the classification theorems instead assume $b_i\ge0$ with $a>0$, matching the source's treatment of the non-exceptional classes.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora (author: Jack Huizenga, Penn State). Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, 'Blowup description of a cubic surface' (intersection rules 1–4, H = 3L − E₁ − ⋯ − E₆, K_X = −3L + E₁ + ⋯ + E₆) and 'Counting lines' items 1–3 (the three families of classes).

import Mathlib

open Finset

namespace CubicSurface27

/-- The Picard lattice of the blowup of ℙ² at six points, in the source's coordinates:
the class D = a·L − ∑ i, b i • E i is represented by the pair (a, b). -/
abbrev BlLattice := ℤ × (Fin 6 → ℤ)

/-- The intersection pairing, determined by L² = 1, L·Eᵢ = 0, Eᵢ·Eⱼ = 0 (i ≠ j), Eᵢ² = −1. -/
def inter (D D' : BlLattice) : ℤ :=
  D.1 * D'.1 - ∑ i : Fin 6, D.2 i * D'.2 i

/-- The class of a line in ℙ² meeting none of the six points. -/
def classL : BlLattice := (1, fun _ => 0)

/-- The exceptional divisor over the i-th point (its b-coordinate is −1 at i). -/
def classE (i : Fin 6) : BlLattice := (0, fun j => if j = i then -1 else 0)

/-- The hyperplane class of the cubic embedding: H = 3L − E₁ − ⋯ − E₆. -/
def classH : BlLattice := (3, fun _ => 1)

/-- The canonical class of the blowup: K = −3L + E₁ + ⋯ + E₆. -/
def classK : BlLattice := (-3, fun _ => -1)

/-- The class of the line through points i and j: L − Eᵢ − Eⱼ. -/
def lineClass (i j : Fin 6) : BlLattice := (1, fun k => if k = i ∨ k = j then 1 else 0)

/-- The class of the conic through the five points other than i: 2L − ∑ k ≠ i, Eₖ. -/
def conicClass (i : Fin 6) : BlLattice := (2, fun k => if k = i then 0 else 1)

/-- The 27 classes of the source's count: 6 exceptional divisors, 15 pair-lines,
6 five-point conics. -/
def the27 : Finset BlLattice :=
  (univ.image classE) ∪
  ((univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2)).image (fun p => lineClass p.1 p.2)) ∪
  (univ.image conicClass)

end CubicSurface27


