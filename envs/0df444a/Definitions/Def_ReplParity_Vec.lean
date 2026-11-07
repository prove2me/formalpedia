-- Prove2me | Definitions.Def_ReplParity_Vec
-- name    : ReplParity_Vec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:46.644214+00:00
-- url     : https://prove2.me/theorems/460b052b-75df-4938-9f68-7938d2faaa9f
-- title:
--   Vectors $\mathbb F_2^n$, subspaces and labeled examples
-- statement:
--   Throughout, $\mathbb F_2^n$ is the space of length-$n$ vectors over the two-element field, written as functions from $\{0,\dots,n-1\}$ to $\mathbb F_2$. Subspaces of $\mathbb F_2^n$ are its $\mathbb F_2$-linear subspaces. A labeled example over $\mathbb F_2^d$ is a pair $(x,y)$ with $x\in\mathbb F_2^d$ and a label $y\in\{0,1\}$, the label being read as an element of $\mathbb F_2$.
--
--   **Formalization Note** Coordinates are indexed from $0$ rather than $1$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.10–11 (PDF pp.12–13)

import Mathlib

namespace ReplParity

/-- **Vectors, subspaces and labeled examples over 𝔽₂.** Shen, Zhong, *Replicable Parity Learning:
Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), §2.1, p.11 (PDF p.13).

`Vec n` is 𝔽ⁿ₂, written as functions `Fin n → ZMod 2`.

**Formalization Note.** Coordinates are indexed by `Fin n = {0, …, n−1}` instead of `{1, …, n}`. -/
abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2

/-- Subspaces of 𝔽ⁿ₂ (§2.1, p.11). -/
abbrev Subsp (n : ℕ) : Type := Submodule (ZMod 2) (Vec n)

/-- A labeled example over 𝔽ᵈ₂: a point `x ∈ 𝔽ᵈ₂` and a label `y`. The paper's label set `{0, 1}`
is written as `ZMod 2` (§2.1, p.10). -/
abbrev Example (d : ℕ) : Type := Vec d × ZMod 2

end ReplParity


