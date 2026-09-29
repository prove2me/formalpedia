-- Prove2me | Definitions.Def_usg_lattice_model
-- name    : usg_lattice_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T23:54:40.236126+00:00
-- url     : https://prove2.me/theorems/bb07d9a7-f37c-46be-ab56-2be29e7df2ad
-- title:
--   Translationally invariant nearest-neighbour Hamiltonians on a 2D square lattice
-- statement:
--   This file fixes the lattice model used throughout the mission.
--
--   For a side length $L$, the lattice is $\Lambda(L)=\{0,\dots,L-1\}^2$, whose elements are called **sites**; the first coordinate is the row index and the second the column index. Each site carries a $d$-dimensional quantum system, so the standard product basis of the whole lattice is indexed by the **configurations**, i.e. the assignments of a level in $\{0,\dots,d-1\}$ to every site. Operators on the lattice are complex matrices indexed by configurations.
--
--   **Open boundary conditions.** The horizontal (row) edges are the pairs of sites in a common row whose column indices are consecutive, and the vertical (column) edges are the pairs of sites in a common column whose row indices are consecutive. No edges wrap around, so the outer rows and columns are not connected.
--
--   **Embedding of local terms.** A two-body interaction $h\in B(\mathbb{C}^d\otimes\mathbb{C}^d)$ placed on an edge $(p,q)$ acts as $h$ on the two factors $p,q$ and as the identity on every other site; an on-site term $h_1\in B(\mathbb{C}^d)$ acts as $h_1$ on its site and as the identity elsewhere.
--
--   **The Hamiltonian.** Given an on-site matrix $h_1$ and two two-body matrices $h_{\mathrm{row}},h_{\mathrm{col}}$, the same three matrices being used at every site and every edge, the model on $\Lambda(L)$ is
--
--   $$H^{\Lambda(L)}=\sum_{(i,j)\ \text{row edge}}h_{\mathrm{row}}^{(i,j)}+\sum_{(i,j)\ \text{column edge}}h_{\mathrm{col}}^{(i,j)}+\sum_{k\in\Lambda(L)}h_1^{(k)} .$$
--
--   This is the translational invariance used in the source: the interaction depends on the edge only through its direction.
--
--   **Local interaction strength.** $\max\{\lVert h_1\rVert,\lVert h_{\mathrm{row}}\rVert,\lVert h_{\mathrm{col}}\rVert\}$, where $\lVert\cdot\rVert$ is the $\ell_2$ operator norm.
--
--   **The phase parameter.** For $n\in\mathbb{N}$, $\varphi(n)$ is the rational number in $[0,1)$ whose binary expansion after the point is the binary expansion of $n$ written in reverse order: if $n=b_{k-1}\cdots b_1b_0$ in binary then $\varphi(n)=0.b_0b_1\cdots b_{k-1}$, and $|\varphi(n)|=k$ is the number of digits of $n$. These are the numbers appearing in the phases $e^{i\pi\varphi}$ and $e^{i\pi 2^{-|\varphi|}}$ of the main theorem.
--
--   The model is the standard finite-lattice spin-system setting of mathematical physics, and it is reused by every statement of this mission.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 1.1 (Definitions and notation), pp. 2-3, eqs. (1.1)-(1.2) and the definition of the local interaction strength; Section 1.2, p. 3 (definition of the rational number phi(n)).

import Mathlib

set_option autoImplicit false

namespace UndecidableSpectralGap

/-- The sites of the `L × L` square lattice `Λ(L) = {1,…,L}²`.
The first component is the row index, the second the column index. -/
abbrev Site (L : ℕ) := Fin L × Fin L

/-- A standard basis state of the lattice system with local dimension `d`:
an assignment of a level in `Fin d` to every site. -/
abbrev Config (L d : ℕ) := Site L → Fin d

/-- The directed horizontal (row) edges of `Λ(L)` with **open** boundary conditions:
pairs of sites in the same row whose column indices are consecutive. -/
def rowEdges (L : ℕ) : Finset (Site L × Site L) :=
  Finset.univ.filter fun e => e.1.1 = e.2.1 ∧ (e.1.2 : ℕ) + 1 = (e.2.2 : ℕ)

/-- The directed vertical (column) edges of `Λ(L)` with **open** boundary conditions:
pairs of sites in the same column whose row indices are consecutive. -/
def colEdges (L : ℕ) : Finset (Site L × Site L) :=
  Finset.univ.filter fun e => e.1.2 = e.2.2 ∧ (e.1.1 : ℕ) + 1 = (e.2.1 : ℕ)

/-- The two-body interaction `h` acting on the pair of sites `(p, q)` of the lattice,
written in the standard product basis: it acts as `h` on the factors `p` and `q`
and as the identity on all other sites. -/
def embedTwo {L d : ℕ} (p q : Site L) (h : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Config L d) (Config L d) ℂ :=
  fun c c' => if ∀ s, s ≠ p → s ≠ q → c s = c' s then h (c p, c q) (c' p, c' q) else 0

/-- The on-site interaction `h` acting on the site `p`, written in the standard product
basis: it acts as `h` on the factor `p` and as the identity on all other sites. -/
def embedOne {L d : ℕ} (p : Site L) (h : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Config L d) (Config L d) ℂ :=
  fun c c' => if ∀ s, s ≠ p → c s = c' s then h (c p) (c' p) else 0

/-- The translationally invariant nearest-neighbour Hamiltonian
`H^{Λ(L)} = Σ_rows h_row + Σ_columns h_col + Σ_sites h₁`
on the `L × L` square lattice with open boundary conditions, local dimension `d`,
on-site term `h₁`, horizontal interaction `hrow` and vertical interaction `hcol`. -/
def latticeHam (L d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Config L d) (Config L d) ℂ :=
  (∑ e ∈ rowEdges L, embedTwo e.1 e.2 hrow) + (∑ e ∈ colEdges L, embedTwo e.1 e.2 hcol)
    + ∑ p : Site L, embedOne p h1

/-- The operator norm (largest singular value) of a square complex matrix,
viewed as an operator on the Euclidean space of its index type. -/
noncomputable def opNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

/-- The local interaction strength `max{‖h₁‖, ‖h_row‖, ‖h_col‖}` of a lattice model. -/
noncomputable def localInteractionStrength {d : ℕ} (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  max (opNorm h1) (max (opNorm hrow) (opNorm hcol))

/-- `phi n` is the rational number `φ(n) ∈ [0,1)` whose binary fractional expansion consists
of the binary digits of `n` in reverse order after the point: if `n = b_{k-1}…b_1b_0` in
binary, then `φ(n) = 0.b_0b_1…b_{k-1}`. -/
def phi (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n.size, if n.testBit i then (2 : ℚ) ^ (-(i + 1 : ℤ)) else 0

/-- `phiLen n` is the number `|φ(n)|` of binary digits of `n`, i.e. the length of the
fractional expansion of `φ(n)`. -/
def phiLen (n : ℕ) : ℕ := n.size

end UndecidableSpectralGap


