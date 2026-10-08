-- Prove2me | Definitions.Def_RevenueOrdered_Tightness_TightInstance
-- name    : RevenueOrdered_Tightness_TightInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:51:00.488958+00:00
-- url     : https://prove2.me/theorems/956d3651-3731-49eb-9c45-655dd11dd4e3
-- title:
--   The tight instance of Theorem 3.4: products $(i,j)$, revenue $\varepsilon^{-j}$, choice probability $\varepsilon^i$
-- statement:
--   Fix $k\ge 1$ and $0<\varepsilon\le\tfrac12$. The product set is
--   $$
--   \mathcal C=\{(i,j): i\in[k],\ j\in[i]\},
--   $$
--   of size $k(k+1)/2$; product $(i,j)$ has revenue $\varepsilon^{-j}$, so the distinct revenues are $r_i=\varepsilon^{-i}$. For $S\subseteq\mathcal C$ and $(i,j)\in S$,
--   $$
--   \mathcal P((i,j),S)=\begin{cases}\varepsilon^i & \text{if }(i,1),\dots,(i,j-1)\notin S,\\ 0 & \text{otherwise,}\end{cases}
--   $$
--   and $\mathcal P((i,j),S)=0$ for $(i,j)\notin S$. In words, a consumer of type $i$ arrives with probability $\varepsilon^i$ and buys the cheapest offered product of row $i$.
--
--   The module also defines the **row** $S_i=\{(i,j)\in S\}$ of a choice set (not the threshold set $S_i$ of §3) and the set $S^*=\{(i,i): i\in[k]\}$.
--
--   This instance witnesses that all three revenue-ordered guarantees are exactly tight.
--
--   **Formalization Note** The pairs keep the paper's 1-based indices: a product is a pair $(i,j)\in\{0,\dots,k\}^2$ with $1\le j\le i$. The definitions do not assume $0<\varepsilon\le\tfrac12$; every theorem about the instance does. The type is nonempty whenever $k\neq 0$ (`NeZero k`).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4

import Mathlib

namespace RevenueOrdered.Tightness

/-! The tight instance of the proof of Theorem 3.4
(Berbeglia & Joret, arXiv:1606.01371v3, p. 10).

Products are the pairs `(i, j)` with `i ∈ [k]` and `j ∈ [i]`, kept with the paper's 1-based
indices as the pairs `(i, j) : Fin (k+1) × Fin (k+1)` with `1 ⩽ j ⩽ i` (so `1 ⩽ i ⩽ k`). -/

/-- The product set `𝒞 = {(i, j) : i ∈ [k], j ∈ [i]}`, of size `k(k+1)/2`. -/
abbrev TightProduct (k : ℕ) : Type :=
  {p : Fin (k + 1) × Fin (k + 1) // 1 ≤ p.2.val ∧ p.2.val ≤ p.1.val}

instance (k : ℕ) [NeZero k] : Nonempty (TightProduct k) :=
  ⟨⟨(⟨1, by have := NeZero.ne k; omega⟩, ⟨1, by have := NeZero.ne k; omega⟩), le_rfl, le_rfl⟩⟩

/-- The revenue `ε^{-j}` of product `(i, j)`. -/
noncomputable def tightRevenue (k : ℕ) (ε : ℝ) (x : TightProduct k) : ℝ :=
  (ε ^ x.val.2.val)⁻¹

/-- The choice probabilities: for `(i, j) ∈ S`, `𝒫((i, j), S) = ε^i` if
`(i, 1), …, (i, j - 1) ∉ S` and `0` otherwise; for `(i, j) ∉ S`, `𝒫((i, j), S) = 0`. -/
noncomputable def tightP (k : ℕ) (ε : ℝ) (x : TightProduct k) (S : Finset (TightProduct k)) : ℝ :=
  if x ∈ S ∧ ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val then ε ^ x.val.1.val else 0

/-- Row `i` of a choice set, `S_i = {(i, j) : j ∈ [i], (i, j) ∈ S}` (p. 10). Not the threshold
set `S_i` of §3. -/
def row {k : ℕ} (S : Finset (TightProduct k)) (i : ℕ) : Finset (TightProduct k) :=
  S.filter (fun x => x.val.1.val = i)

/-- The paper's optimal solution `S^* = {(i, i) : i ∈ [k]}` (p. 11). -/
def diagonalSet (k : ℕ) : Finset (TightProduct k) :=
  Finset.univ.filter (fun x => x.val.2 = x.val.1)

end RevenueOrdered.Tightness


