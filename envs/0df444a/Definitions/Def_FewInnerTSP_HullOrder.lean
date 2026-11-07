-- Prove2me | Definitions.Def_FewInnerTSP_HullOrder
-- name    : FewInnerTSP_HullOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:55.347201+00:00
-- url     : https://prove2.me/theorems/7c3f53cc-1897-46d4-b6c7-93a1ea96e603
-- title:
--   Counterclockwise hull order and the chain form (5) of a tour
-- statement:
--   Let $P$ be an instance and $h=|H|$.
--
--   1. A **counterclockwise hull order** is a bijection $j\mapsto h_j$ from $\{0,\dots,h-1\}$ onto the hull indices such that for **every** $i<j<l$ the triple $(P_{h_i},P_{h_j},P_{h_l})$ turns counterclockwise, i.e. its orientation determinant
--   $$\det\begin{pmatrix}x_{h_j}-x_{h_i} & x_{h_l}-x_{h_i}\\ y_{h_j}-y_{h_i} & y_{h_l}-y_{h_i}\end{pmatrix}$$
--   is positive. The start $h_0$ is arbitrary.
--   2. A tour $\pi$ has the **chain form** (5) with chains $S_0,\dots,S_{h-1}$ (lists of indices) if the sequence
--   $$h_0, S_0, h_1, S_1, \dots, h_{h-1}, S_{h-1}$$
--   is a cyclic rotation of $\pi(0),\dots,\pi(n-1)$ or of its reversal, and the chains together contain exactly the interior indices.
--
--   The chain $S_j$ sits in the **gap** $j$ between $h_j$ and $h_{j+1}$ (indices mod $h$). Since the sequence is a rotation of a permutation, the chains are disjoint and duplicate-free.
--
--   **Formalization Note** Positivity on consecutive triples alone would admit a pentagram order on a convex pentagon, so all triples are required.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §3, p.3 (PDF p.5), display (5)

import Mathlib
import Definitions.Def_FewInnerTSP_Instance

namespace FewInnerTSP

/-- The orientation determinant of a triple of points; positive when `a, b, c` turn
counterclockwise. -/
noncomputable def orient (a b c : Pt) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- **The hull in counterclockwise order** `H = (h₀, …, h_{h-1})`.
`hull` is a bijection from `Fin h` onto the hull indices and the orientation of `(h_i, h_j, h_l)` is
positive for **every** `i < j < l`.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), §3, p.3 (PDF p.5).

**Formalization Note** Consecutive triples alone would admit a pentagram order, because each turn of
a pentagram on a convex pentagon is positive. The start `h₀` is any hull vertex. -/
structure IsHullOrder {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) : Prop where
  injective : Function.Injective hull
  mem_iff : ∀ x, x ∈ hullIdx P ↔ ∃ i, hull i = x
  ccw : ∀ i j l : Fin h, i < j → j < l → 0 < orient (P (hull i)) (P (hull j)) (P (hull l))

/-- **The tour form (5)**: `h₀, S₀, h₁, S₁, …, h_{h-1}, S_{h-1}, h₀`, up to the choice of the start
and of the orientation. The concatenation is a rotation of the sequence of `π` or of its reversal,
and the chains `S j` together contain exactly the interior indices.
Source: Li, Ma, Gong, §3, (5), p.3 (PDF p.5).

**Formalization Note** The rotation of a sequence of the permutation `π` has no repetition, so the
chains are pairwise disjoint and each chain is duplicate-free. -/
def HasChainForm {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) (S : Fin h → List (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  (((List.finRange h).flatMap fun j => hull j :: S j) ~r List.ofFn π ∨
    ((List.finRange h).flatMap fun j => hull j :: S j) ~r (List.ofFn π).reverse) ∧
  ((List.finRange h).flatMap S).toFinset = interiorIdx P

end FewInnerTSP


