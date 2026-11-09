-- Prove2me | Definitions.Def_NadlerCLS_kuhnInterp
-- name    : NadlerCLS_kuhnInterp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:04.815379+00:00
-- url     : https://prove2.me/theorems/c5d087e2-b63c-45a3-b2b3-a490175e206e
-- title:
--   Simplex-based (Kuhn) interpolation on the grid of length $2^{-m}$
-- statement:
--   Fix $m\ge1$ and $h=2^{-m}$. For $x\in[0,1]^n$:
--
--   1. In each coordinate choose the grid interval containing $x_i$, where a positive grid boundary belongs to the interval on its left and $0$ belongs to the first interval; let $c$ be the lower corner of the chosen cube and $t_i=(x_i-c_i)/h\in[0,1]$.
--   2. Let $\pi$ order the coordinates so that $t_{\pi(1)}\ge\dots\ge t_{\pi(n)}$, ties broken by increasing index; equivalently the rank of $i$ is $\rho_i=1+\#\{k<i:t_k\ge t_i\}+\#\{k>i:t_k>t_i\}$.
--   3. The vertices are $v_0=c$ and $v_j=c+h\sum_{\ell\le j}e_{\pi(\ell)}$ for $1\le j\le n$ (C.1), and the weights are $w_0=1-t_{\pi(1)}$, $w_j=t_{\pi(j)}-t_{\pi(j+1)}$ for $1\le j<n$, $w_n=t_{\pi(n)}$ (C.2).
--
--   For a map $g:\mathbb R^n\to\mathbb R^r$ the interpolant is
--   $$ I_hg(x)=\sum_{j=0}^{n}w_j\,g(v_j). $$
--
--   This is the interpolation of Lemma C.1, used to turn a Hölder instance into a Lipschitz one in Theorem C.2.
--
--   **Formalization Note** The module defines the grid length `kuhnH`, the cell index, the corner, the normalized coordinates, the 0-based ranks (the rank formula of p.34 without the leading $1$), the sorted coordinates, the weights, the vertices and the interpolant. Vertices are indexed by `Fin (n + 1)` from $0$.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), proof of Lemma C.1, pp.32–34, Eqs. (C.1)–(C.2), and the rank formula, p.34

import Mathlib

set_option autoImplicit false

namespace NadlerCLS

/-- The **grid length** `h = 2^{−m}` of Lemma C.1 (Xiong–Vlatakis-Gkaragkounis, *On the Complexity
of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, Lemma C.1, p.31: "let h = 2−m for an integer m ≥ 1"). -/
noncomputable def kuhnH (m : ℕ) : ℝ := ((2 : ℝ) ^ m)⁻¹

variable {n : ℕ}

/-- The index of the grid interval chosen for coordinate `i` (proof of Lemma C.1, p.32: "in each
coordinate, a positive grid boundary belongs to the interval immediately to its left, and zero
belongs to the first interval"): `0` if `x i ≤ 0`, else `⌈x i · 2^m⌉ − 1`, capped at `2^m − 1`
(the cap only matters outside the cube). -/
noncomputable def kuhnCell (m : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℕ :=
  if x i ≤ 0 then 0 else min (2 ^ m - 1) (⌈x i * 2 ^ m⌉₊ - 1)

/-- The lower corner `c` of the chosen grid cube (p.32). -/
noncomputable def kuhnCorner (m : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (kuhnCell m x i : ℝ) * kuhnH m

/-- The normalized coordinates `t_i = (x_i − c_i)/h` (p.32). -/
noncomputable def kuhnT (m : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (x i - kuhnCorner m x i) / kuhnH m

/-- The 0-based rank of coordinate `i` in the decreasing order of `t`, ties broken by increasing
index (p.34: "ρi = 1 + ∑k<i 1[tk ≥ ti] + ∑k>i 1[tk > ti]"; here without the leading `1`). -/
noncomputable def kuhnRank (m : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => k < i ∧ kuhnT m x i ≤ kuhnT m x k)).card +
    (Finset.univ.filter (fun k : Fin n => i < k ∧ kuhnT m x i < kuhnT m x k)).card

/-- The sorted normalized coordinates `t_{π(j)}` at the 1-based position `j` (p.34:
"tπ(j) = ∑ ti 1[ρi = j]"), extended by `t_{π(0)} := 1` and `t_{π(j)} := 0` for `j > n`. -/
noncomputable def kuhnSortedT (m : ℕ) (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else ∑ i, if kuhnRank m x i + 1 = j then kuhnT m x i else 0

/-- The weights (C.2), p.32: `w₀ = 1 − t_{π(1)}`, `w_j = t_{π(j)} − t_{π(j+1)}` (`1 ≤ j < n`),
`w_n = t_{π(n)}`, written uniformly as `w_j = t_{π(j)} − t_{π(j+1)}` with the conventions of
`kuhnSortedT`. -/
noncomputable def kuhnWeight (m : ℕ) (x : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  kuhnSortedT m x j.val - kuhnSortedT m x (j.val + 1)

/-- The vertices (C.1), p.32: `v₀ = c`, `v_j = c + h ∑_{ℓ ≤ j} e_{π(ℓ)}`, computed as on p.34 by
`(v_j)_i = c_i + h 1[ρ_i ≤ j]` (1-based ranks), i.e. `kuhnRank i < j` with 0-based ranks. -/
noncomputable def kuhnVertex (m : ℕ) (x : Fin n → ℝ) (j : Fin (n + 1)) : Fin n → ℝ :=
  fun i => kuhnCorner m x i + kuhnH m * (if kuhnRank m x i < j.val then 1 else 0)

/-- The **simplex-based (Kuhn) interpolant** `I_h g` of Lemma C.1 (Xiong–Vlatakis-Gkaragkounis,
arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, proof of Lemma C.1,
pp.32–34): `I_h g(x) = ∑_{j=0}^{n} w_j g(v_j)` with the weights (C.2) and vertices (C.1) of the
simplex selected at `x` on the grid of length `h = 2^{−m}`.

**Formalization Note** Vertex indices are 0-based in `Fin (n + 1)` and coordinates 0-based in
`Fin n`; ranks are 0-based. `g` is an arbitrary function `ℝⁿ → ℝʳ`; only its values at the
selected vertices are used. -/
noncomputable def kuhnInterp {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ))
    (x : Fin n → ℝ) : Fin r → ℝ :=
  ∑ j : Fin (n + 1), kuhnWeight m x j • g (kuhnVertex m x j)

end NadlerCLS


