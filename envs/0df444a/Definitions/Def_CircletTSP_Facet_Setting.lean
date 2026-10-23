-- Prove2me | Definitions.Def_CircletTSP_Facet_Setting
-- name    : CircletTSP_Facet_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:36.386072+00:00
-- url     : https://prove2.me/theorems/42bb1e4a-24ba-4475-9790-2b7eea14bb89
-- title:
--   pp. 2–3, 8, 10–11, 14–15, 19 — cyclic edge length, circlet coefficients, length counts t_i, STSP(n), the structures of Figure 4, windows, the contraction of §4
-- statement:
--   This file fixes the objects of Gutekunst and Williamson, *The Circlet Inequalities: A New, Circulant-Based, Facet-Defining Inequality for the TSP*.
--
--   **Cities, edges and tours.** The cities are the vertices of the complete graph $K_n$. A Hamiltonian cycle $H$ is described by an ordering $\pi$ of the cities, visited cyclically $\pi(0),\pi(1),\dots,\pi(n-1),\pi(0)$; its incidence vector $\chi_H$ puts weight $1$ on each edge the cycle traverses and $0$ elsewhere. The **symmetric traveling salesman polytope** is
--   $$STSP(n)=\operatorname{conv}\{\chi_H : H \text{ a Hamiltonian cycle on } K_n\}.$$
--
--   **Lengths and coefficients.** Write $d=n/2$. The length of the edge $\{i,j\}$ is
--   $$\ell_{i,j}=\min\{|i-j|,\ n-|i-j|\},$$
--   the distance between $i$ and $j$ around a circle of $n$ equally spaced points; every edge has a length in $\{1,\dots,d\}$. For $1\le i\le d$ the circlet coefficients are $c_i=i$ for odd $i$ and $c_i=d-i$ for even $i$ (for $n=12$: $1,4,3,2,5,0$). For a vector $x$ indexed by edges, $t_i=\sum_{\{s,t\}\in E:\ \ell_{s,t}=i} x_{s,t}$ is the total weight on edges of length $i$, and the **circlet form** is $\sum_{i=1}^{d} c_i t_i$; Inequality (2) is $\sum_{i=1}^{d} c_i t_i\ge n-2$.
--
--   **Structures and windows.** Vertex labels are taken mod $n$. For a vertex $u$, structure **A** consists of the edges $\{u+d,u\},\{u,u+1\},\{u+1,u+1+d\}$; structure **B1** of $\{u+1,u\},\{u,u+d\},\{u+d,u+1+d\}$; structure **B2** of $\{u,u+1\},\{u+1,u+1+d\},\{u+1+d,u+d\}$ (Figure 4). The window count of a Hamiltonian cycle at $u$ is
--   $$T_u=\mathbb 1_{u\sim u+1}+\mathbb 1_{u+d\sim u+d+1}+\mathbb 1_{u\sim u+d}+\mathbb 1_{u+1\sim u+1+d},$$
--   where $\mathbb 1_{a\sim b}$ is $1$ if the cycle uses the edge $\{a,b\}$.
--
--   **Contraction (§4).** On the labels $1,\dots,n$: the vertices $1,2,d+1,d+2$ are deleted, and every other vertex $s$ gets the new label $s'=s-2$ if $2<s\le d$ and $s'=s-4$ if $s>d+2$. With $c_{i,j}:=c_{\ell_{i,j}}$ the cost of $\{i,j\}$ before contraction, the contracted graph on $n-4$ vertices has lengths $\ell'_{i,j}=\min\{|i-j|,\ n-4-|i-j|\}$ and costs $c'_{i,j}=\ell'_{i,j}$ for odd $\ell'_{i,j}$ and $d-2-\ell'_{i,j}$ for even $\ell'_{i,j}$, the circlet coefficients for $n-4$. The two edge sequences of Figure 7 are $\{j,1\},\{1,2\},\{2,d+2\},\{d+2,d+1\},\{d+1,k\}$ and $\{j,d+2\},\{d+2,2\},\{2,1\},\{1,d+1\},\{d+1,k\}$; contracting either replaces its five edges by the single edge $\{j',k'\}$.
--
--   These are the objects in which validity (Theorem 3.1) and the facet property (Theorem 5.1) are stated.
--
--   **Formalization Note** Cities are `Fin n` with 0-based labels; lengths depend only on label differences, so the shift from the paper's $1,\dots,n$ changes no length or coefficient. A Hamiltonian cycle is an ordering `π : Equiv.Perm (Fin n)` and its incidence vector is the published `MetricTSP.tourVec π`, a symmetric function `Fin n → Fin n → ℝ` (0/1 with zero diagonal for $n\ge 3$); $STSP(n)$ lives in these ordered-pair coordinates, which changes no affine dimension. $t_i$ counts each unordered edge once (pairs $u<v$), and the circlet form is literally $\sum_{i=1}^{n/2} c_i t_i$. "The cycle uses $\{a,b\}$" is `tourVec π a b = 1`, and $T_u$ adds the four entries of `tourVec π`. The contraction objects (`labLen`, `labCost`, `relabel`, `conLen`, `conCost`, `keptLabels`, `HasEdge`, `ChainOne`, `ChainTwo`) use the paper's 1-based labels in `ℕ` with integer arithmetic; `HasEdge π a b` says the cycle uses the edge between the vertices labelled $a$ and $b$ (vertex `v : Fin n` has label $v+1$). `contract n x j k` is the contracted vector on `Fin (n - 4)`: the restriction of $x$ to the surviving vertices, relabelled, plus weight $1$ on $\{j',k'\}$.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, pp. 2–3, 8 (Theorem 3.1, Inequality (2)), 10–11 (Figure 4, windows), 14–15 (contraction, s′, ℓ′, c′), 19 (STSP(n))

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_Disjunctive_Polarity_Projection

namespace CircletTSP.Facet

open MetricTSP

/-! ### Lengths, coefficients and the circlet form (pp. 2–3, 8)

Cities are `Fin n` (0-based labels `0, …, n - 1`; the paper uses `1, …, n`). All quantities below
depend only on differences of labels, so the shift by one changes nothing. -/

/-- The length `ℓ_{i,j} = min{|i - j|, n - |i - j|}` of the edge `{i, j}` (p. 8). -/
def cycLen (n : ℕ) (u v : Fin n) : ℕ :=
  min (Int.natAbs ((u.val : ℤ) - v.val)) (n - Int.natAbs ((u.val : ℤ) - v.val))

/-- The circlet coefficient `c_i` of Theorem 3.1 (p. 8): `c_i = i` for odd `i` and
`c_i = d - i` for even `i`, where `d = n / 2` (used for `1 ≤ i ≤ d`). -/
def coeff (n i : ℕ) : ℕ :=
  if i % 2 = 1 then i else n / 2 - i

/-- `t_i(x) = ∑_{{s,t} ∈ E, ℓ_{s,t} = i} x_{s,t}` (p. 8): the total weight of the edges of
length `i`, each unordered edge `{u, v}` counted once via `u < v`. -/
def lenCount (n i : ℕ) (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ u : Fin n, ∑ v : Fin n, if u < v ∧ cycLen n u v = i then x u v else 0

/-- The left-hand side `∑_{i=1}^{d} c_i t_i` of Inequality (2) (p. 8), `d = n / 2`. -/
def circletForm (n : ℕ) (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), (coeff n i : ℝ) * lenCount n i x

/-- The symmetric traveling salesman polytope `STSP(n) = conv{χ_H : H Hamiltonian cycle on K_n}`
(p. 19), in ordered-pair coordinates: every Hamiltonian cycle of `K_n` is the tour of an ordering
`π`, with incidence vector `MetricTSP.tourVec π`. -/
def STSP (n : ℕ) : Set (Fin n → Fin n → ℝ) :=
  convexHull ℝ (Set.range fun π : Equiv.Perm (Fin n) => tourVec π)

/-! ### The structures of Figure 4 and the windows (pp. 10–11)

Vertex labels are taken mod `n` (p. 10); `d = n / 2`. -/

/-- The vertex `u + k` (mod `n`). -/
def shift {n : ℕ} (u : Fin n) (k : ℕ) : Fin n :=
  ⟨(u.val + k) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt)⟩

/-- The tour of `π` contains the edge `{u, v}` (`u ∼ v`; for `n ≥ 3`, `tourVec π u v ∈ {0, 1}`). -/
def Adj {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) : Prop :=
  tourVec π u v = 1

/-- Type A of Figure 4 at `u`: the edges `{u + d, u}`, `{u, u + 1}`, `{u + 1, u + 1 + d}`. -/
def IsStructA {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) : Prop :=
  Adj π (shift u (n / 2)) u ∧ Adj π u (shift u 1) ∧ Adj π (shift u 1) (shift u (1 + n / 2))

/-- Type B1 of Figure 4 at `u`: the edges `{u + 1, u}`, `{u, u + d}`, `{u + d, u + 1 + d}`. -/
def IsStructB1 {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) : Prop :=
  Adj π (shift u 1) u ∧ Adj π u (shift u (n / 2)) ∧ Adj π (shift u (n / 2)) (shift u (1 + n / 2))

/-- Type B2 of Figure 4 at `u`: the edges `{u, u + 1}`, `{u + 1, u + 1 + d}`, `{u + 1 + d, u + d}`. -/
def IsStructB2 {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) : Prop :=
  Adj π u (shift u 1) ∧ Adj π (shift u 1) (shift u (1 + n / 2)) ∧
    Adj π (shift u (1 + n / 2)) (shift u (n / 2))

/-- The window count `T_u = 𝟙_{u∼u+1} + 𝟙_{u+d∼u+d+1} + 𝟙_{u∼u+d} + 𝟙_{u+1∼u+1+d}` (p. 11),
with the indicator of an edge read off the incidence vector `tourVec π`. -/
noncomputable def window {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) : ℝ :=
  tourVec π u (shift u 1) + tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) +
    tourVec π u (shift u (n / 2)) + tourVec π (shift u 1) (shift u (1 + n / 2))

/-! ### The contraction of §4 (pp. 14–15), on the paper's 1-based labels `1, …, n` -/

/-- The length `ℓ_{i,j} = min{|i - j|, n - |i - j|}` on labels, as an integer. -/
def labLen (n i j : ℕ) : ℤ :=
  min |(i : ℤ) - j| ((n : ℤ) - |(i : ℤ) - j|)

/-- The cost `c_{i,j} := c_{ℓ_{i,j}}` (p. 15): `ℓ_{i,j}` if odd, `d - ℓ_{i,j}` if even. -/
def labCost (n i j : ℕ) : ℤ :=
  if labLen n i j % 2 = 1 then labLen n i j else (n / 2 : ℕ) - labLen n i j

/-- The new label `s'` after contraction (p. 15): `s - 2` for `2 < s ≤ d`, `s - 4` for `s > d + 2`
(applied only to labels outside `{1, 2, d + 1, d + 2}`). -/
def relabel (n s : ℕ) : ℕ :=
  if s ≤ n / 2 then s - 2 else s - 4

/-- The length `ℓ'_{i,j} = min{|i - j|, n - 4 - |i - j|}` in the contracted graph (p. 15). -/
def conLen (n i j : ℕ) : ℤ :=
  min |(i : ℤ) - j| ((n : ℤ) - 4 - |(i : ℤ) - j|)

/-- The cost `c'_{i,j}` in the contracted graph (p. 15): `ℓ'_{i,j}` if odd, `d - 2 - ℓ'_{i,j}`
if even. -/
def conCost (n i j : ℕ) : ℤ :=
  if conLen n i j % 2 = 1 then conLen n i j else ((n / 2 : ℕ) : ℤ) - 2 - conLen n i j

/-- The labels that survive contraction: `[n] \ {1, 2, d + 1, d + 2}`. -/
def keptLabels (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n \ {1, 2, n / 2 + 1, n / 2 + 2}

/-- The tour of `π` contains the edge between the vertices with (1-based) labels `a` and `b`
(the vertex `v : Fin n` has label `v + 1`). -/
def HasEdge {n : ℕ} (π : Equiv.Perm (Fin n)) (a b : ℕ) : Prop :=
  ∃ u v : Fin n, u.val + 1 = a ∧ v.val + 1 = b ∧ tourVec π u v = 1

/-- The first edge sequence of Figure 7 (Proposition 4.4, p. 17): the tour contains
`{j, 1}, {1, 2}, {2, d + 2}, {d + 2, d + 1}, {d + 1, k}`. -/
def ChainOne {n : ℕ} (π : Equiv.Perm (Fin n)) (j k : ℕ) : Prop :=
  HasEdge π j 1 ∧ HasEdge π 1 2 ∧ HasEdge π 2 (n / 2 + 2) ∧
    HasEdge π (n / 2 + 2) (n / 2 + 1) ∧ HasEdge π (n / 2 + 1) k

/-- The second edge sequence of Figure 7 (Proposition 4.5, p. 17): the tour contains
`{j, d + 2}, {d + 2, 2}, {2, 1}, {1, d + 1}, {d + 1, k}`. -/
def ChainTwo {n : ℕ} (π : Equiv.Perm (Fin n)) (j k : ℕ) : Prop :=
  HasEdge π j (n / 2 + 2) ∧ HasEdge π (n / 2 + 2) 2 ∧ HasEdge π 2 1 ∧
    HasEdge π 1 (n / 2 + 1) ∧ HasEdge π (n / 2 + 1) k

/-- The vertex of the original graph whose contracted label is that of `w : Fin (n - 4)`:
contracted label `s' = w + 1` comes from `s = s' + 2` if `s' ≤ d - 2` and `s = s' + 4` otherwise;
as a 0-based vertex of `Fin n` this is `w + 2`, resp. `w + 4`. -/
def unrelabel (n : ℕ) (w : Fin (n - 4)) : Fin n :=
  ⟨if w.val + 1 ≤ n / 2 - 2 then w.val + 2 else w.val + 4, by
    have := w.isLt
    split <;> omega⟩

/-- The contracted vector (p. 14): delete the vertices `1, 2, d + 1, d + 2`, relabel every other
vertex `s` as `s'`, and replace the five contracted edges by the single edge `{j', k'}`. -/
noncomputable def contract (n : ℕ) (x : Fin n → Fin n → ℝ) (j k : ℕ) :
    Fin (n - 4) → Fin (n - 4) → ℝ :=
  fun a b => x (unrelabel n a) (unrelabel n b) +
    if (a.val + 1 = relabel n j ∧ b.val + 1 = relabel n k) ∨
        (a.val + 1 = relabel n k ∧ b.val + 1 = relabel n j) then 1 else 0

end CircletTSP.Facet


