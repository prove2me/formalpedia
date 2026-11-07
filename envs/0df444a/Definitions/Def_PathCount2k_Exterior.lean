-- Prove2me | Definitions.Def_PathCount2k_Exterior
-- name    : PathCount2k_Exterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:43.444143+00:00
-- url     : https://prove2.me/theorems/909ab886-526b-4b96-9620-dda7adf82af3
-- title:
--   Defs. 2.1–2.3, 2.7, 2.17 — exterior algebra $\Lambda(R^k)$, wedge product, $\Phi(W)$, $\Delta_P$, auxiliary rows $\rho_W$
-- statement:
--   The **exterior algebra** $\Lambda(R^k)$ has basis $\{e_S : S\subseteq[k]\}$, with $e_\emptyset=1$ and $e_{\{i\}}$ identified with the standard basis vector $e_i$. The **wedge product** is defined on basis elements by $e_A\wedge e_B=0$ if $A\cap B\neq\emptyset$ and
--   $$
--   e_A\wedge e_B=(-1)^{\mathrm{inv}(A,B)}\,e_{A\cup B},\qquad \mathrm{inv}(A,B)=|\{(a,b)\in A\times B: a>b\}|,
--   $$
--   otherwise, and extended bilinearly. For vertex vectors $g_v\in R^k$, the **walk contribution** of $W=(v_1,\dots,v_p)$ is $\Phi(W)=g_{v_1}\wedge\cdots\wedge g_{v_p}$, and its exterior coordinates are $c_W[S]$, $\Phi(W)=\sum_S c_W[S]e_S$. The **path contribution** of $P=(v_1,\dots,v_k)$ is $\Delta_P=\det[g_{v_1}\cdots g_{v_k}]$ (the vectors are the columns). For matrices $H_{i,v}\in R^{D\times D}$ and $b_0=(1,0,\dots,0)^\top$, the **auxiliary row** of a walk is $\rho_W=b_0^\top H_{1,v_1}\cdots H_{p,v_p}$, and $b_0^\top H_{1,v_1}\cdots H_{k,v_k}b_0$ is the $(1,1)$ entry of the ordered product.
--
--   These objects carry the cancellation of walks with repeated vertices (Lemma 2.1) and the state of the dynamic program.
--
--   **Formalization Note** A concrete coordinate model over any commutative ring $R$: an element of $\Lambda(R^k)$ is a function `Finset (Fin k) → R`; $(x\wedge y)(S)=\sum_{A,B\text{ disjoint},\,A\cup B=S}(-1)^{\mathrm{inv}(A,B)}x(A)y(B)$; $\Phi$ is the left fold from $e_\emptyset$. Coordinates and positions are 0-based.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Definitions 2.1–2.3, pp.4–5; Definition 2.7, p.6; Definition 2.17, p.14

import Mathlib

namespace PathCount2k

/-- **The exterior algebra `Λ(R^k)`**, Definition 2.1, p.4 (Panolan, Saurabh, Xue, Zehavi,
*Counting Paths in Time O\*(2^k), …*, STOC 2027 submission manuscript, Nov 2026): "the real
vector space with basis `{e_S : S ⊆ [k]}`". An element is its coefficient vector
`x : Finset (Fin k) → R`, `x = ∑_S x(S) e_S`.

**Formalization Note.** This is a concrete coordinate model, over any commutative ring `R`
(the paper uses `ℝ`; the dynamic program of §2.10 runs over `ℤ`). Coordinates are 0-based:
the paper's `[k] = {1, …, k}` is `Fin k`. -/
abbrev Ext (R : Type*) (k : ℕ) := Finset (Fin k) → R

/-- `inv(A, B) = |{(a, b) ∈ A × B : a > b}|`, Definition 2.1, p.4. -/
def inv {k : ℕ} (A B : Finset (Fin k)) : ℕ :=
  ((A ×ˢ B).filter fun ab => ab.2 < ab.1).card

/-- The basis element `e_S` of `Λ(R^k)`, Definition 2.1, p.4; `e_∅ = 1`. -/
def basis {R : Type*} [CommRing R] {k : ℕ} (S : Finset (Fin k)) : Ext R k :=
  fun T => if T = S then 1 else 0

/-- **The wedge product**, Definition 2.1, p.4: "defined on basis elements by `e_A ∧ e_B = 0`
when `A ∩ B ≠ ∅` and `e_A ∧ e_B = (−1)^{inv(A,B)} e_{A∪B}` otherwise, … and extended
bilinearly". On coefficient vectors,
`(x ∧ y)(S) = ∑_{A, B disjoint, A ∪ B = S} (−1)^{inv(A,B)} x(A) y(B)`. -/
def wedge {R : Type*} [CommRing R] {k : ℕ} (x y : Ext R k) : Ext R k := fun S =>
  ∑ A : Finset (Fin k), ∑ B : Finset (Fin k),
    if Disjoint A B ∧ A ∪ B = S then (-1 : R) ^ inv A B * x A * y B else 0

/-- A vector `x ∈ R^k` as a degree-1 element, `x = ∑_j x(j) e_{j}`: Definition 2.1, p.4, "We
identify `e_{i}` with the standard basis vector `eᵢ ∈ R^k`". -/
def vec {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) : Ext R k :=
  fun S => ∑ j : Fin k, if S = {j} then x j else 0

/-- **Walk contributions**, Definition 2.2, p.4: for vertex vectors `g_v ∈ R^k` and a walk
`W = (v₁, …, v_p)`, `Φ(W) = g_{v₁} ∧ ⋯ ∧ g_{v_p}`. Computed as the left fold
`((1 ∧ g_{v₁}) ∧ g_{v₂}) ∧ ⋯`, starting from `e_∅ = 1`.

The exterior coordinates of Definition 2.17, p.14, are `c_W[S] = Phi g W S`. -/
def Phi {R : Type*} [CommRing R] {n k : ℕ} (g : Fin n → Fin k → R) {p : ℕ}
    (W : Fin p → Fin n) : Ext R k :=
  (List.ofFn fun i : Fin p => vec (g (W i))).foldl wedge (basis ∅)

/-- **Path contributions**, Definition 2.3, p.5: `Δ_P = det[g_{v₁} ⋯ g_{v_k}]`, "where the vectors
form the columns of the matrix": the matrix has entry `(i, j) = g_{v_j}(i)`. -/
def Delta {R : Type*} [CommRing R] {n k : ℕ} (g : Fin n → Fin k → R) (P : Fin k → Fin n) : R :=
  (Matrix.of fun i j : Fin k => g (P j) i).det

/-- The boundary vector `b₀ = (1, 0, …, 0)ᵀ ∈ R^D`, Definition 2.7, p.6. -/
def b0 {R : Type*} [CommRing R] (D : ℕ) : Fin D → R := fun a => if a.val = 0 then 1 else 0

/-- **The auxiliary row of a walk**, Definition 2.17, p.14 (and Observation 2.2, p.6):
`ρ_W = b₀ᵀ H_{1,v₁} ⋯ H_{p,v_p}` for a walk `W = (v₁, …, v_p)` with `p ≤ k`, where `H i v` is
the `D × D` matrix attached to position `i` and host vertex `v`.

**Formalization Note.** Positions are 0-based: the paper's `H_{i,v}` is `H ⟨i − 1, _⟩ v`.
Matrices are functions `Fin D → Fin D → R`, read with `Matrix.of`. -/
def walkRow {R : Type*} [CommRing R] {n k D : ℕ} (H : Fin k → Fin n → Fin D → Fin D → R)
    {p : ℕ} (hp : p ≤ k) (W : Fin p → Fin n) : Fin D → R :=
  fun b => ∑ a : Fin D, b0 D a *
    (List.ofFn fun i : Fin p => Matrix.of (H ⟨i.val, by omega⟩ (W i))).prod a b

/-- The `(1,1)` entry of the ordered product along a `k`-vertex sequence,
`b₀ᵀ H_{1,v₁} ⋯ H_{k,v_k} b₀` (Definitions 2.7 and 2.16, pp.6, 13). -/
def pathEntry {R : Type*} [CommRing R] {n k D : ℕ} (H : Fin k → Fin n → Fin D → Fin D → R)
    (P : Fin k → Fin n) : R :=
  ∑ b : Fin D, walkRow H le_rfl P b * b0 D b

end PathCount2k


