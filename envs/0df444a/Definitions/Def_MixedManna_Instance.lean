-- Prove2me | Definitions.Def_MixedManna_Instance
-- name    : MixedManna_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:02.178874+00:00
-- url     : https://prove2.me/theorems/5f1a5466-c414-41da-a896-53c50892b6c0
-- title:
--   Mixed-manna exchange instance with SPLC utilities
-- statement:
--   A **mixed-manna instance** consists of a finite set $N$ of agents, a finite set $M$ of divisible items, endowments $W_{ij}\ge 0$ (the amount of item $j$ that agent $i$ brings), and for every agent $i$ and item $j$ a separable piecewise-linear concave function $u_{ij}:\mathbb R_+\to\mathbb R$. The function $u_{ij}$ has $|u_{ij}|$ segments; segment $k$ has slope $U_{ijk}$ and, unless it is the last one, length $L_{ijk}$. The last segment has infinite length, so for $x\ge 0$
--   $$
--   u_{ij}(x)=\sum_{k}U_{ijk}\,\min\Big\{\max\Big(x-\sum_{k'<k}L_{ijk'},0\Big),\,L_{ijk}\Big\},\qquad L_{ij|u_{ij}|}=\infty ,
--   $$
--   and agent $i$'s utility for a bundle $y\in\mathbb R_+^M$ is $u_i(y)=\sum_{j\in M}u_{ij}(y_j)$.
--
--   An item is a **good** ($j\in M^+$) if some agent has a positive first slope $U_{ij1}>0$, and a **bad** or chore ($j\in M^-$) otherwise. The module also fixes the sign $\pm1$ of an item (good / bad).
--
--   These are the data of every statement of the mission; their standing conditions are collected in `StandingAssumptions`.
--
--   **Formalization Note** Segments are indexed from $0$: the paper's $U_{ij1}$ is `U i j 0` and the final segment $|u_{ij}|$ is `K i j - 1`. Lengths at the last index are ignored by the utility.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §2.1 p.5 and §4 p.14 (SPLC utilities, segments, goods and bads)

import Mathlib

namespace MixedManna

/-- **A mixed-manna exchange instance with SPLC utilities** (Chaudhury, Garg, McGlaughlin, Mehta,
*Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, §2.1 p.5 and §4 p.14).

Agents form the finite type `N`, items the finite type `M`. `W i j ≥ 0` is agent `i`'s endowment
of item `j`. For each agent `i` and item `j`, the separable piecewise-linear concave function
`u_ij` has `K i j` segments; segment `k` (0-based, the paper's segment `k + 1`) has slope
`U i j k` and, if it is not the last one (`k + 1 < K i j`), length `L i j k`. The last segment has
infinite length (p.14: "Note that the length of last segment is infinite").

**Formalization Note** Segments are 0-based: the paper's `U_ij1` is `U i j 0` and its final
segment `|u_ij|` is `K i j - 1`. Values of `U`, `L` at indices `k ≥ K i j`, and `L` at the last
index, are never used by the utility; the conditions on the data are in
`MixedManna.StandingAssumptions`. -/
structure Instance (N M : Type*) where
  /-- endowment `W_ij` -/
  W : N → M → ℝ
  /-- number of segments `|u_ij|` -/
  K : N → M → ℕ
  /-- slope `U_ijk` of segment `k` (0-based) -/
  U : N → M → ℕ → ℝ
  /-- length `L_ijk` of segment `k` (used for `k + 1 < K i j` only) -/
  L : N → M → ℕ → ℝ

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **Goods** (p.14, "Identifying Goods and Bads"): item `j` is a good (`j ∈ M⁺`) iff some agent
has a positive first slope `U_ij1 > 0`; otherwise it is a bad (`j ∈ M⁻`). -/
def IsGood (I : Instance N M) (j : M) : Prop := ∃ i, 0 < I.U i j 0

open Classical in
/-- The sign of item `j`: `+1` on a good, `−1` on a bad. It writes the paper's split sums
`Σ_{j∈M⁺} − Σ_{j∈M⁻}` as one sum. -/
noncomputable def itemSign (I : Instance N M) (j : M) : ℝ := if IsGood I j then 1 else -1

/-- The amount of `x ≥ 0` units that falls on segment `k` of `u_ij`: segment `k` covers
`[a_k, a_k + L_ijk]` with `a_k = Σ_{k' < k} L_ijk'`, and the last segment `[a_{K-1}, ∞)`. -/
noncomputable def segAmount (I : Instance N M) (i : N) (j : M) (k : ℕ) (x : ℝ) : ℝ :=
  if k + 1 < I.K i j then
    min (max (x - ∑ k' ∈ Finset.range k, I.L i j k') 0) (I.L i j k)
  else max (x - ∑ k' ∈ Finset.range k, I.L i j k') 0

/-- The SPLC function `u_ij(x) = Σ_k U_ijk · (amount of x on segment k)`, last segment infinite
(p.14). -/
noncomputable def itemUtility (I : Instance N M) (i : N) (j : M) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (I.K i j), I.U i j k * segAmount I i j k x

/-- Agent `i`'s additively separable utility `u_i(y) = Σ_{j ∈ M} u_ij(y_j)` (p.14). -/
noncomputable def utility (I : Instance N M) (i : N) (y : M → ℝ) : ℝ :=
  ∑ j, itemUtility I i j (y j)

end MixedManna


