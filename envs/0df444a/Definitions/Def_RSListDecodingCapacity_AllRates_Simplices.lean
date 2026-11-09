-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_Simplices
-- name    : RSListDecodingCapacity_AllRates_Simplices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:57.317907+00:00
-- url     : https://prove2.me/theorems/07c2f57a-04b9-407a-9c6c-13363918f59b
-- title:
--   The weighted simplex $S_z$ and half-open lattice cubes
-- statement:
--   In $\mathbb R^{d-1}$ (coordinates $x_1,\dots,x_{d-1}$):
--   1. the **scaled simplex** $S_z=\{x\in\mathbb R_{\ge0}^{d-1}:\sum_{i=1}^{d-1}i\cdot x_i\le z\}$;
--   2. the **half-open unit cube** $u+[0,1)^{d-1}$ at $u\in\mathbb Z_{\ge0}^{d-1}$;
--   3. the union $\bigcup_{u\in\mathbb Z_{\ge0}^{d-1}:\ \sum_i i\,u_i\le z}\big(u+[0,1)^{d-1}\big)$.
--
--   They compare the lattice count $\Lambda(z)$ with the volume of $S_z$.
--
--   **Formalization Note** Lean index $i$ of `Fin (d-1)` is the source's coordinate $x_{i+1}$, with weight $i+1$.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), §3.2.1, pp.18–19 (Corollary 3.5, Propositions 3.6–3.7)

import Mathlib

namespace RSListDecodingCapacity.AllRates

/-!
# The weighted simplex `S_z` and half-open lattice cubes

Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, §3.2.1, pp.18–19.
Points of `ℝ^{d−1}` are functions `Fin (d − 1) → ℝ`; the coordinate with Lean index `i` is the
source's `x_{i+1}`, which carries the weight `i + 1`.
-/

/-- **The scaled simplex** (Corollary 3.5, p.18):
`S_z = {x ∈ ℝ_{≥0}^{d−1} : ∑_{i=1}^{d−1} i · x_i ≤ z}`. -/
def simplexS (d : ℕ) (z : ℝ) : Set (Fin (d - 1) → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (d - 1), ((i : ℕ) + 1 : ℝ) * x i ≤ z}

/-- The half-open unit cube `u + [0, 1)^{d−1}` at a lattice point `u ∈ ℤ_{≥0}^{d−1}` (p.18). -/
def unitCube {d : ℕ} (u : Fin (d - 1) → ℕ) : Set (Fin (d - 1) → ℝ) :=
  {x | ∀ i, (u i : ℝ) ≤ x i ∧ x i < (u i : ℝ) + 1}

/-- The union `⋃_{u ∈ ℤ_{≥0}^{d−1} : ∑ᵢ i uᵢ ≤ z} (u + [0, 1)^{d−1})` (Propositions 3.6–3.7,
pp.18–19). -/
def latticeCubeUnion (d : ℕ) (z : ℝ) : Set (Fin (d - 1) → ℝ) :=
  ⋃ (u : Fin (d - 1) → ℕ) (_ : ∑ i : Fin (d - 1), ((i : ℕ) + 1 : ℝ) * (u i : ℝ) ≤ z), unitCube u

end RSListDecodingCapacity.AllRates


