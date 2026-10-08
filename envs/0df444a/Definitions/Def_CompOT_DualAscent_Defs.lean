-- Prove2me | Definitions.Def_CompOT_DualAscent_Defs
-- name    : CompOT_DualAscent_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:42.726143+00:00
-- url     : https://prove2.me/theorems/65a6e465-da45-4c5f-9466-2e229fd0ae71
-- title:
--   Definition 3.2 and balanced pairs, p. 415 — the indicator vectors 1_S, 1_S′ and the balanced edges of a dual pair (f, g)
-- statement:
--   Fix $n, m \ge 1$, a cost matrix $C \in \mathbb{R}^{n\times m}$ and a pair of potentials $(f,g) \in \mathbb{R}^n\times\mathbb{R}^m$. This file adds the two objects of the dual ascent methods of §3.6 to the shared definitions of couplings $U(a,b)$, dual feasibility $R(C)$, the dual objective $\langle f, a\rangle + \langle g, b\rangle$, dual optimality for Problem (3.4) and complementarity (Definition 3.1).
--
--   1. **Indicator vectors** (Definition 3.2, p. 415). For $S \subset [\![n]\!]$, $\mathbb{1}_S \in \mathbb{R}^n$ is the vector of zeros except for ones at the indices in $S$; likewise $\mathbb{1}_{S'} \in \mathbb{R}^m$ for $S' \subset [\![m]\!]'$.
--   2. **Balanced edges** (p. 415). The pair $(i, j')$ is balanced for $(f,g)$ if $f_i + g_j = C_{i,j}$ (and inactive otherwise).
--
--   These are the objects in which the optimality-or-ascent alternative (Proposition 3.6) and its supporting results are stated.
--
--   **Formalization Note** Indices are `Fin n` and `Fin m` (0-based); the book's primed column set $[\![m]\!]' = \{1', \dots, m'\}$ is just `Fin m`. $\mathbb 1_S$ is the real-valued function `indicatorVec S` for a `Finset` $S$. Couplings, $R(C)$, the dual objective, `IsDualOptimal` and `Complementary` come from the shared modules `CompOT.Assignment.Defs` and `CompOT.Duality.Defs`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Definition 3.2 and the definition of balanced pairs, p. 415

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.DualAscent

open Finset

/-- Definition 3.2, p. 415: the indicator vector `𝟙_S` of a set of indices `S`: zeros except
for ones at the indices in `S`. -/
def indicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- p. 415: the pair `(i, j')` is balanced for `(f, g)` if `f_i + g_j = C_{i,j}`. -/
def Balanced {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (i : Fin n) (j : Fin m) : Prop :=
  f i + g j = C i j

end CompOT.DualAscent


