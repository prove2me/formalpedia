-- Prove2me | Definitions.Def_QuantumMaxCutMatchingPadding
-- name    : QuantumMaxCutMatchingPadding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T02:16:37.556145+00:00
-- url     : https://prove2.me/theorems/35b27e20-35ea-47a5-98aa-0f0109fe1d27
-- title:
--   Padding an edge weight to a doubly stochastic matrix: $\mathrm{padWeight}\,x$ with diagonal deficits $1-\mathrm{load}_x(a)$
-- statement:
--   **Padding a fractional edge weight to a doubly stochastic matrix.**
--
--   For a graph on $n$ vertices and a weight $x$ on its edges, write $x_{\{a,b\}}$ for the weight of the
--   unordered pair $\{a,b\}$ (zero if $a=b$), and $\mathrm{load}_x(a)=\sum_{e\ni a}x_e$ for the load of a vertex.
--
--   * `pairWeight x a b` is $x_{\{a,b\}}$: symmetric in $a,b$ and zero on the diagonal.
--   * `padWeight x` is the $n\times n$ matrix with $x_{\{a,b\}}$ off the diagonal and the *deficit*
--     $1-\mathrm{load}_x(a)$ on the diagonal,
--   $$\bigl(\mathrm{padWeight}\,x\bigr)_{ab}=\begin{cases}1-\mathrm{load}_x(a), & a=b,\\[2pt] x_{\{a,b\}}, & a\ne b.\end{cases}$$
--
--   **Why the diagonal is the deficit.** Summing a row costs the deficit plus all incident edges, which is
--   $1$ exactly when the loads are at most $1$:
--   $\sum_b(\mathrm{padWeight}\,x)_{ab}=\bigl(1-\mathrm{load}_x(a)\bigr)+\mathrm{load}_x(a)=1$. The matrix is
--   symmetric, so the column sums agree. Thus a point of the fractional matching polytope becomes a *doubly
--   stochastic* matrix — the object Birkhoff's theorem decomposes into permutation matrices
--   (`QuantumMaxCutEnergy.padWeight_mem_doublyStochastic`, `QuantumMaxCutEnergy.padWeight_eq_sum_perm`).
--
--   **Role.** This is the padding step of the bipartite case of Edmonds' exactness. When the graph is bipartite
--   with colouring $c$, every entry of `padWeight x` off the diagonal joins the two colour classes; a permutation
--   whose non-fixed steps all cross a bipartition splits into alternating even cycles, and one of the two
--   alternating matchings of each cycle carries at least half of its weight. That turns the Birkhoff decomposition
--   into an honest matching of weight at least $\sum_e w_e x_e$.
-- source:
--   Birkhoff-von Neumann (Birkhoff 1946; von Neumann 1953); Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Lee-Parekh arXiv:2401.03616 Section 2.3 (the matching state whose fractional weight this padding is designed to round).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-!
# Padding a fractional edge weight to a doubly stochastic matrix

For the bipartite warm-up of Edmonds' exactness we read an edge weight `x` as a symmetric matrix on the
vertex set and pad the diagonal by the *deficit* `1 - loadAt x a`, so that every row and column sums to
`1`. This file fixes the two objects:

* `pairWeight x a b` — the weight of the unordered pair `{a,b}` (symmetric, zero on the diagonal);
* `padWeight x` — the symmetric matrix with `pairWeight x a b` off the diagonal and `1 - loadAt x a` on it.

`QuantumMaxCutEnergy.padWeight_mem_doublyStochastic` proves that `padWeight x` is doubly stochastic
whenever `x` has vertex loads at most `1`, and
`QuantumMaxCutEnergy.padWeight_eq_sum_perm` (Birkhoff) writes it as a convex combination of permutation
matrices. A permutation whose non-fixed steps all cross a bipartition therefore decomposes into
alternating even cycles, half of whose weight is carried by a matching — which is the content of the
bipartite case of Edmonds' exactness.
-/

namespace QuantumMaxCutEnergy

/-- The weight of the *unordered* pair `{a, b}` read off from an edge weight `x`. -/
def pairWeight {n : ℕ} (x : Edge n → ℝ) (a b : Fin n) : ℝ :=
  if h : a < b then x ⟨(a, b), h⟩ else if h : b < a then x ⟨(b, a), h⟩ else 0

/-- The symmetric padding of an edge weight: the pair weights off the diagonal and the deficit
`1 - loadAt x a` on it. Rows and columns sum to `1` exactly when the loads are at most `1`. -/
def padWeight {n : ℕ} (x : Edge n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => if a = b then 1 - loadAt x a else pairWeight x a b

lemma padWeight_apply_self {n : ℕ} (x : Edge n → ℝ) (a : Fin n) :
    padWeight x a a = 1 - loadAt x a := by
  simp [padWeight]

lemma padWeight_apply_of_ne {n : ℕ} (x : Edge n → ℝ) {a b : Fin n} (h : a ≠ b) :
    padWeight x a b = pairWeight x a b := by
  simp [padWeight, h]

lemma pairWeight_self {n : ℕ} (x : Edge n → ℝ) (a : Fin n) : pairWeight x a a = 0 := by
  simp [pairWeight]

lemma pairWeight_comm {n : ℕ} (x : Edge n → ℝ) (a b : Fin n) :
    pairWeight x a b = pairWeight x b a := by
  unfold pairWeight
  rcases lt_trichotomy a b with h | h | h
  · rw [dif_pos h, dif_neg (not_lt.mpr h.le), dif_pos h]
  · subst h; simp
  · rw [dif_neg (not_lt.mpr h.le), dif_pos h, dif_pos h]

end QuantumMaxCutEnergy


