-- Prove2me | Definitions.Def_GL2QFT_RepBasics
-- name    : GL2QFT_RepBasics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:18.661608+00:00
-- url     : https://prove2.me/theorems/fdb4d77a-d84f-4ff3-8ac0-96b0f83f5da8
-- title:
--   Matrix representations, irreducibility, equivalence, and the Fourier transform $\mathfrak F_G$ of (22)
-- statement:
--   This module fixes the representation-theoretic vocabulary of §2 used throughout the mission.
--
--   1. A **representation** of a group $G$ on $\mathbb C^\iota$ is a map $R:G\to\mathbb C^{\iota\times\iota}$ with $R(1)=I$ and $R(gh)=R(g)R(h)$; it is **unitary** if every $R(g)$ is a unitary matrix.
--   2. A subspace $W\subseteq\mathbb C^\iota$ is **invariant** if $R(g)W\subseteq W$ for all $g$; $R$ is **irreducible** if $\iota\neq\emptyset$ and its only invariant subspaces are $\{0\}$ and $\mathbb C^\iota$.
--   3. $R$ and $R'$ are **equivalent on** a subset $S\subseteq G$ if an invertible matrix $A$ satisfies $AR(g)=R'(g)A$ for all $g\in S$; with $S=G$ this is $R\cong R'$.
--   4. The matrix entry of an operator $M$ between vectors $u,v$ is $\langle u|M|v\rangle=\sum_{x,y}\overline{u_x}M_{xy}v_y$ (convention (15): upper index = row = output).
--   5. For a family $(R_\mu)_\mu$ of representations in orthonormal bases $\mathcal B_\mu$ of sizes $d_\mu$, the **Fourier transform** of Proposition 2.7 is the matrix with rows $(\mu,i,j)$ and columns $g\in G$,
--   $$\mathfrak F_G|g\rangle=\sum_{\mu}\sqrt{\frac{d_\mu}{|G|}}\sum_{i,j=1}^{d_\mu}[R_\mu(g)]^i_j\,|\mu,i_\mu,j^*_\mu\rangle ,$$
--   with all phases equal to one.
--
--   These notions are reused by every statement of the mission: the QFT of $\mathrm{GL}_2(\mathbb F_q)$ and of its Borel subgroup are instances of item 5, and Lemma 6.5, Lemma 6.7 and the completeness of Table 2 are stated with items 1–3.
--
--   **Formalization Note** The definition of $\mathfrak F_G$ uses only a finite index type for the columns, so it also applies to a parametrization of a subgroup (the Borel subgroup is indexed by triples $(a,d,b)$).
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §2.1 p.13 (representation, invariant subspace, irreducible, equivalence), eq. (15) p.13, Definition 2.6 and Proposition 2.7, eq. (22), p.14 (PDF pp.14–15)

import Mathlib

namespace GL2QFT

open scoped ComplexConjugate

/-- Bruinsma–Posta–Stokvis–Grinko–Ozols, *Quantum Fourier transform toolbox*, arXiv:2608.28573
(held version, sha256 ecd45073…), §2.1, p.13: a (matrix) representation of `G` on `ℂ^ι`, i.e. a map
`R : G → Matrix ι ι ℂ` with `R 1 = 1` and `R (g h) = R g · R h`.

**Formalization Note** Representations are matrix-valued maps in a fixed orthonormal basis `ι`
(the paper's convention (15): `[A]^i_j = ⟨i|A|j⟩`, row index = output). -/
def IsMatRep {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι] (R : G → Matrix ι ι ℂ) : Prop :=
  R 1 = 1 ∧ ∀ g h : G, R (g * h) = R g * R h

/-- arXiv:2608.28573, §2.1, p.13: a unitary representation: a representation all of whose values
are unitary matrices. -/
def IsUnitaryRep {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι] (R : G → Matrix ι ι ℂ) :
    Prop :=
  IsMatRep R ∧ ∀ g : G, R g ∈ Matrix.unitaryGroup ι ℂ

/-- arXiv:2608.28573, §2.1, p.13: the subspace `W ⊆ ℂ^ι` is invariant under `R` (`R(g) W ⊆ W`
for every `g`; for a representation of a finite group this is the paper's `R(g)W = W`). -/
def IsInvariantSubspace {G ι : Type} [Fintype ι] (R : G → Matrix ι ι ℂ)
    (W : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ g : G, ∀ v ∈ W, (R g).mulVec v ∈ W

/-- arXiv:2608.28573, §2.1, p.13: a representation on `V ≠ {0}` is irreducible if its only
invariant subspaces are `{0}` and `V`. -/
def IsIrreducibleRep {G ι : Type} [Fintype ι] (R : G → Matrix ι ι ℂ) : Prop :=
  Nonempty ι ∧ ∀ W : Submodule ℂ (ι → ℂ), IsInvariantSubspace R W → W = ⊥ ∨ W = ⊤

/-- arXiv:2608.28573, §2.1, p.13: `R` and `R'` are equivalent on the subset `S ⊆ G` if some
invertible matrix `A` intertwines them there: `A R(g) = R'(g) A` for all `g ∈ S`. With
`S = Set.univ` this is the paper's `R ≅ R'`; with `S` a subgroup it is equivalence of the
restrictions. -/
def RepEquivOn {G ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Set G) (R : G → Matrix ι ι ℂ) (R' : G → Matrix κ κ ℂ) : Prop :=
  ∃ (A : Matrix κ ι ℂ) (B : Matrix ι κ ℂ), A * B = 1 ∧ B * A = 1 ∧
    ∀ g ∈ S, A * R g = R' g * A

/-- arXiv:2608.28573, §2.1, p.13: `R ≅ R'` (equivalence on the whole group). -/
def RepEquiv {G ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (R : G → Matrix ι ι ℂ) (R' : G → Matrix κ κ ℂ) : Prop :=
  RepEquivOn Set.univ R R'

/-- arXiv:2608.28573, (15), p.13: the matrix entry `⟨u|M|v⟩ = Σ_{x,y} conj(u_x) M_{xy} v_y` of
the operator `M` between the vectors `u`, `v` of `ℂ^X`. -/
noncomputable def matEntry {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v : X → ℂ) : ℂ :=
  ∑ x, ∑ y, conj (u x) * M x y * v y

/-- arXiv:2608.28573, Proposition 2.7, eq. (22), p.14: the Fourier transform of a finite group in
the chosen representatives `R μ` and orthonormal bases `B μ`, with all phases equal to one:
`F_G|g⟩ = Σ_μ √(d_μ/|G|) Σ_{i,j} [R_μ(g)]^i_j |μ, i_μ, j*_μ⟩`. Its rows are indexed by the triples
`(μ, i, j)` (`i` the row and `j` the column index of `R_μ(g)`), its columns by the group elements.

**Formalization Note** `d_μ` is the cardinality of the basis index type `B μ`. The definition only
needs a family of matrix-valued maps; it is the paper's `F_G` when `R` is a complete family of
pairwise inequivalent irreducible unitary representations. The group structure is not used, so `G`
may be any finite type parametrizing the group (for `B` the mission uses the triple
`(a, d, b) ↦ (1 b; 0 1)(a 0; 0 d)`). -/
noncomputable def fourierMatrix {G Λ : Type} [Fintype G] {B : Λ → Type} [∀ μ, Fintype (B μ)]
    (R : ∀ μ, G → Matrix (B μ) (B μ) ℂ) : Matrix (Σ μ, B μ × B μ) G ℂ :=
  Matrix.of fun r g =>
    (Real.sqrt ((Fintype.card (B r.1) : ℝ) / (Fintype.card G : ℝ)) : ℂ) * R r.1 g r.2.1 r.2.2

end GL2QFT


