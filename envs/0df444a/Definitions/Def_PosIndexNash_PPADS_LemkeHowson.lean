-- Prove2me | Definitions.Def_PosIndexNash_PPADS_LemkeHowson
-- name    : PosIndexNash_PPADS_LemkeHowson
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:29.674233+00:00
-- url     : https://prove2.me/theorems/747ef199-42dd-45e6-8a7c-9d259ad185d2
-- title:
--   The labeled product polytope, the missing-ℓ graph and its determinant orientation (§3.1, (6)–(10), (14), (18))
-- statement:
--   Let $A, B \in \mathbb{R}^{m\times n}$ be positive payoff matrices, $d = m + n$ and $C = \begin{pmatrix} 0 & A\\ B^\top & 0\end{pmatrix}$. The **product best response polytope** is $R = P\times Q = \{z \in \mathbb{R}^d : -z \le 0,\ Cz \le \mathbf 1\}$, with $2d$ labeled inequalities: $-z_r \le 0$ and $(Cz)_r \le 1$ both carry label $r$ (so $x_i \ge 0$ and $(Ay)_i \le 1$ carry $i$, $(B^\top x)_j \le 1$ and $y_j \ge 0$ carry $m + j$). A **vertex** is a point of $R$ whose binding outward normals span $\mathbb{R}^d$; it is **completely labeled** if its binding inequalities carry every label. The origin is the **artificial equilibrium**; a completely labeled $z = (x, y) \ne 0$ gives the equilibrium $(x/\mathbf 1^\top x,\ y/\mathbf 1^\top y)$ (7).
--
--   For a label $\ell$, the **missing-$\ell$ graph** has as vertices the vertices of $R$ whose binding labels contain $[d]\setminus\{\ell\}$, and as edges the segments $[u, v]$ between two of them that are one-dimensional faces of $R$ along which every label $r \ne \ell$ binds. For such an edge $E$, let $N_r(E)$ be the outward normal of its binding label-$r$ inequality, let $c_E$ be the generalized cross product
--   $$q^\top c_E = \det\big[N_1(E) \cdots N_{\ell-1}(E)\ q\ N_{\ell+1}(E)\cdots N_d(E)\big]\qquad (q \in \mathbb{R}^d), \tag{8}$$
--   and orient $E$ along $t_E := (-1)^{d+1}c_E$ (9): $u \to v$ when $t_E^\top(v - u) > 0$. The **sign** of a completely labeled vertex is $\sigma(v) := (-1)^{d+1}\mathrm{sign}\det[N_1\cdots N_d]$ (14), $N_r$ the outward normal of its binding label-$r$ inequality. The **basis code** $\chi(v) \in \{0,1\}^{2d}$ is the characteristic vector of the inequalities binding at $v$, in the order $-z_1\le 0, \dots, -z_d \le 0, (Cz)_1 \le 1, \dots, (Cz)_d\le 1$ (18).
--
--   **Formalization Note** Labels and coordinates are 0-based (`Fin (m + n)`, the $x$-coordinates first). The edge normal of label $r$ is the nonnegativity inequality if it binds at both ends, otherwise the payoff inequality; in a nondegenerate game exactly one of the two binds along a missing-$\ell$ edge. Orienting by $t_E^\top(v-u) > 0$ is the same as the incidence rule (10): $\iota(u, E) = \mathrm{sign}(N_u(E)^\top t_E) = -1$ at the tail.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), pp. 14–18, §3.1, (6)–(10), (14), (18)

import Mathlib

namespace PosIndexNash.PPADS

open Matrix

/-- **The matrix `C = (0 A; Bᵀ 0)`** of the product best response polytope (Kontogiannis,
Panageas, Pollatos, Yan, *Finding a Positive Index Nash Equilibrium is PPADS-Complete*,
arXiv:2609.23879, §3.1, p. 15), `d = m + n`; coordinates `z = (x, y)`, the `x`-coordinates first.

**Formalization Note** The block matrix is indexed by `Fin (m + n)` through `finSumFinEquiv`
(coordinate `i < m` is `x_i`, coordinate `m + j` is `y_j`; 0-based). -/
def lhC {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  (Matrix.fromBlocks 0 A Bᵀ 0).reindex finSumFinEquiv finSumFinEquiv

/-- **Outward normal of a labeled inequality of `R = {z : −z ≤ 0, Cz ≤ 1}`** (pp. 14–15, (6)).
The `2d` inequalities are indexed by `Fin d ⊕ Fin d`: `inl r` is `−z_r ≤ 0` (normal `−e_r`) and
`inr r` is `(Cz)_r ≤ 1` (normal = row `r` of `C`). -/
def lhNormal {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (h : Fin (m + n) ⊕ Fin (m + n)) :
    Fin (m + n) → ℝ :=
  Sum.elim (fun r => -(Pi.single r (1 : ℝ))) (fun r => lhC A B r) h

/-- Right-hand side of a labeled inequality: `0` for `−z_r ≤ 0`, `1` for `(Cz)_r ≤ 1`. -/
def lhRhs {d : ℕ} (h : Fin d ⊕ Fin d) : ℝ := Sum.elim (fun _ => 0) (fun _ => 1) h

/-- **Label of an inequality** (pp. 14–15): `x_i ≥ 0` and `(Ay)_i ≤ 1` carry label `i ∈ [m]`;
`(Bᵀx)_j ≤ 1` and `y_j ≥ 0` carry label `m + j`. In coordinates both `inl r` and `inr r` carry
label `r`. -/
def lhLabel {d : ℕ} (h : Fin d ⊕ Fin d) : Fin d := Sum.elim id id h

/-- **Membership in the product polytope `R = P × Q`** (p. 15): `−z ≤ 0` and `Cz ≤ 1`. -/
def InLHPolytope {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (z : Fin (m + n) → ℝ) : Prop :=
  ∀ h, lhNormal A B h ⬝ᵥ z ≤ lhRhs h

/-- The set of inequalities binding at `z`. -/
noncomputable def lhBinding {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (z : Fin (m + n) → ℝ) :
    Finset (Fin (m + n) ⊕ Fin (m + n)) :=
  Finset.univ.filter (fun h => lhNormal A B h ⬝ᵥ z = lhRhs h)

/-- **Vertex of `R`**: a point of `R` whose binding outward normals span `ℝ^d`. -/
def IsLHVertex {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (z : Fin (m + n) → ℝ) : Prop :=
  InLHPolytope A B z ∧
    Submodule.span ℝ (lhNormal A B '' (lhBinding A B z : Set _)) = ⊤

/-- **Completely labeled vertex** (p. 15): its binding inequalities carry every label in `[d]`. -/
def IsCompletelyLabeled {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (z : Fin (m + n) → ℝ) :
    Prop :=
  IsLHVertex A B z ∧ ∀ r, ∃ h ∈ lhBinding A B z, lhLabel h = r

/-- **Vertex of the missing-`ℓ` graph** (p. 15): a vertex of `R` whose binding labels contain
`[d] ∖ {ℓ}`. -/
def InMissingGraph {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (l : Fin (m + n))
    (z : Fin (m + n) → ℝ) : Prop :=
  IsLHVertex A B z ∧ ∀ r, r ≠ l → ∃ h ∈ lhBinding A B z, lhLabel h = r

/-- **Edge of the missing-`ℓ` graph** (p. 15): two distinct vertices `u, v` of the graph such that
the segment `[u, v]` is a one-dimensional face of `R` (the face cut out by the inequalities binding
at both `u` and `v` is exactly `[u, v]`) whose binding labels contain `[d] ∖ {ℓ}`. -/
def IsMissingEdge {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (l : Fin (m + n))
    (u v : Fin (m + n) → ℝ) : Prop :=
  InMissingGraph A B l u ∧ InMissingGraph A B l v ∧ u ≠ v ∧
    (∀ r, r ≠ l → ∃ h, lhLabel h = r ∧ h ∈ lhBinding A B u ∧ h ∈ lhBinding A B v) ∧
    ∀ z, InLHPolytope A B z →
      (∀ h, h ∈ lhBinding A B u → h ∈ lhBinding A B v → h ∈ lhBinding A B z) →
      z ∈ segment ℝ u v

/-- **Outward normal `N_r(E)` of the label-`r` inequality binding along the edge `E = [u, v]`**
(p. 16): the nonnegativity inequality of label `r` if it binds at both ends, otherwise the payoff
inequality of label `r`. In a nondegenerate game exactly one inequality of each label `r ≠ ℓ`
binds along a missing-`ℓ` edge. -/
noncomputable def edgeNormal {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (u v : Fin (m + n) → ℝ) (r : Fin (m + n)) : Fin (m + n) → ℝ :=
  if Sum.inl r ∈ lhBinding A B u ∧ Sum.inl r ∈ lhBinding A B v then lhNormal A B (Sum.inl r)
  else lhNormal A B (Sum.inr r)

/-- **The generalized cross product `c_E`** (p. 16, (8)): the vector with
`qᵀ c_E = det[N_1(E) ⋯ N_{ℓ−1}(E) q N_{ℓ+1}(E) ⋯ N_d(E)]` for all `q`, the normals in increasing
label order as columns; coordinate `j` is the determinant with `q = e_j`. -/
noncomputable def crossVec {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (l : Fin (m + n))
    (u v : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fun j => (Matrix.of fun i r =>
    if r = l then (Pi.single j (1 : ℝ) : Fin (m + n) → ℝ) i else edgeNormal A B u v r i).det

/-- **The orientation direction `t_E := (−1)^{d+1} c_E`** (p. 16, (9)), `d = m + n`. -/
noncomputable def edgeDir {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (l : Fin (m + n))
    (u v : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  ((-1 : ℝ) ^ (m + n + 1)) • crossVec A B l u v

/-- **Oriented edge `u → v` of the missing-`ℓ` graph** (p. 16, (9)–(10)): `[u, v]` is an edge and
`t_E` points from `u` to `v`, `t_Eᵀ (v − u) > 0`. Equivalently, the incidence sign
`ι(u, E) = sign(N_u(E)ᵀ t_E)` is `−1` (outgoing at `u`). -/
def LHOriented {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (l : Fin (m + n))
    (u v : Fin (m + n) → ℝ) : Prop :=
  IsMissingEdge A B l u v ∧ 0 < edgeDir A B l u v ⬝ᵥ (v - u)

/-- **The vertex sign `σ(v) := (−1)^{d+1} sign det[N_1 ⋯ N_d]`** (p. 17, (14)) of a completely
labeled vertex, with `N_r` the outward normal of its binding inequality of label `r`
(the nonnegativity inequality if it binds, else the payoff inequality). -/
noncomputable def vertexSign {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin (m + n) → ℝ) : ℤ :=
  (-1) ^ (m + n + 1) * ((SignType.sign (Matrix.of fun i r =>
    (if Sum.inl r ∈ lhBinding A B v then lhNormal A B (Sum.inl r)
      else lhNormal A B (Sum.inr r)) i).det : SignType) : ℤ)

/-- **The basis code `χ(v) ∈ {0,1}^{2d}`** (p. 18): the characteristic vector of the inequalities
binding at `v`, in the fixed order `−z_1 ≤ 0, …, −z_d ≤ 0, (Cz)_1 ≤ 1, …, (Cz)_d ≤ 1`. -/
noncomputable def basisCode {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin (m + n) → ℝ) : List Bool :=
  (List.finRange (m + n)).map (fun r => decide (Sum.inl r ∈ lhBinding A B v)) ++
    (List.finRange (m + n)).map (fun r => decide (Sum.inr r ∈ lhBinding A B v))

/-- **The Nash equilibrium of a completely labeled point** `z = (x, y)` (p. 15, (7)):
`(x / 1ᵀx, y / 1ᵀy)`; this function returns the row strategy. -/
noncomputable def lhRowStrategy {m n : ℕ} (z : Fin (m + n) → ℝ) : Fin m → ℝ :=
  fun i => z (Fin.castAdd n i) / ∑ k : Fin m, z (Fin.castAdd n k)

/-- The column strategy `y / 1ᵀy` of a completely labeled point `z = (x, y)` (p. 15, (7)). -/
noncomputable def lhColStrategy {m n : ℕ} (z : Fin (m + n) → ℝ) : Fin n → ℝ :=
  fun j => z (Fin.natAdd m j) / ∑ k : Fin n, z (Fin.natAdd m k)

end PosIndexNash.PPADS


