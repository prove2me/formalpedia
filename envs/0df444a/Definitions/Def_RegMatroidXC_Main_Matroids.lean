-- Prove2me | Definitions.Def_RegMatroidXC_Main_Matroids
-- name    : RegMatroidXC_Main_Matroids
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:41.38699+00:00
-- url     : https://prove2.me/theorems/691b4777-7429-4b05-8d2c-ecc9885abccf
-- title:
--   Independence polytope P(M); regular, binary, graphic and cographic matroids; cycles; R10 (pp. 1, 3)
-- statement:
--   Let $M$ be a matroid on a ground set $E(M)$ (a subset of an ambient type $\alpha$), with independent sets $\mathcal I(M)$.
--
--   1. **Independence polytope** (p. 1). For $I \subseteq E(M)$ let $\chi^I \in \{0,1\}^{E(M)}$ be its characteristic vector. Then
--   $$P(M) = \operatorname{conv}\{\chi^I \in \{0,1\}^{E(M)} \mid I \in \mathcal I(M)\} \subseteq \mathbb R^{E(M)}.$$
--   2. **Representation.** A matrix $A$ over a field $K$ whose columns are indexed by $E(M)$ *represents* $M$ if, for every set $I$, $I$ is independent in $M$ exactly when $I \subseteq E(M)$ and the columns of $A$ indexed by $I$ are linearly independent over $K$.
--   3. **Regular matroid** (p. 1): $M$ is represented over $\mathbb R$ by a totally unimodular matrix (every square submatrix has determinant $0$ or $\pm 1$). The paper gives this as equivalent to "representable over every field".
--   4. **Binary matroid** (p. 3): $M$ is represented by a matrix over $\mathrm{GF}(2)$.
--   5. **Graphic matroid** (p. 1): $M = M(G)$ is the cycle matroid of a finite multigraph $G$, whose edges are the elements of $M$, each edge $e$ running from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$; a set of edges is independent exactly when it is a forest, i.e. when the vectors $\chi_{\mathrm{head}(e)} - \chi_{\mathrm{tail}(e)}$ of the oriented incidence matrix are linearly independent over $\mathbb R$. Loops and parallel edges are allowed.
--   6. **Cographic matroid** (p. 1): the dual $M^*$ is graphic, i.e. $M = M^*(G)$.
--   7. **Cycle** (p. 3): a (possibly empty) disjoint union of circuits of $M$.
--   8. **$R_{10}$**: $M$ is isomorphic to the column matroid over $\mathrm{GF}(2)$ of the $5\times 10$ matrix $[I_5 \mid A]$, where $A$ is the circulant with rows $11001, 11100, 01110, 00111, 10011$; that is, a bijection $E(M) \to \{0,\dots,9\}$ carries the independent sets of $M$ exactly onto the linearly independent sets of columns.
--
--   These are the objects of the main theorem: $P(M)$ for a regular matroid $M$ on $n = |E(M)|$ elements, and the basic classes (graphic, cographic, $R_{10}$) of Seymour's decomposition.
--
--   **Formalization Note** Matroids are Mathlib `Matroid α`; polytopes live in $\mathbb R^{E(M)}$, coordinates indexed by the subtype `M.E`. The paper does not print $R_{10}$ (it cites Seymour 1980); the matrix above is a modelling choice with $R_{10}$'s known invariants (162 bases, fifteen 4-circuits and fifteen 6-circuits).
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 1 (P(M), regular, graphic, cographic), p. 3 (binary, cycles), p. 2 (R10)

import Mathlib

namespace RegMatroidXC.Main

/-- **Independence polytope** `P(M)` (Aprile–Fiorini, arXiv:1909.08539v2, p. 1):
`P(M) = conv{χ^I ∈ {0,1}^{E(M)} | I ∈ I(M)}`, a subset of `ℝ^{E(M)}`. Coordinates are indexed by
the ground set `M.E` (as a subtype); `χ^I` is the indicator vector of the independent set `I`. -/
noncomputable def indepPolytope {α : Type} (M : Matroid α) : Set (M.E → ℝ) :=
  convexHull ℝ {x : M.E → ℝ | ∃ I : Set α, M.Indep I ∧
    ∀ e : M.E, x e = I.indicator (fun _ => (1 : ℝ)) (e : α)}

/-- The matrix `A`, whose columns are indexed by the ground set of `M`, **represents** `M` over the
field `K`: a set `I` is independent in `M` if and only if it lies in `E(M)` and the columns of `A`
indexed by `I` are linearly independent over `K`. -/
def IsRepresentedBy {α : Type} (M : Matroid α) (K : Type) [Field K] {m : Type}
    (A : Matrix m M.E K) : Prop :=
  ∀ I : Set α, M.Indep I ↔
    (I ⊆ M.E ∧ LinearIndepOn K (fun e : M.E => fun i => A i e) {e : M.E | (e : α) ∈ I})

/-- **Regular matroid** (p. 1): `M` is representable over the reals by a totally unimodular
matrix. (The paper also gives the equivalent form "representable over every field".) -/
def IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) M.E ℝ), A.IsTotallyUnimodular ∧ IsRepresentedBy M ℝ A

/-- **Binary matroid** (p. 3): `M` is representable over the two-element field `GF(2)`. -/
def IsBinary {α : Type} (M : Matroid α) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) M.E (ZMod 2)), IsRepresentedBy M (ZMod 2) A

/-- `M` is the **cycle matroid** `M(G)` of the multigraph `G` with vertex set `V` in which every
element `e ∈ E(M)` is an edge from `tail e` to `head e` (p. 1): a set of edges is independent iff
it forms a forest, i.e. iff its columns `χ_{head e} − χ_{tail e}` of the oriented incidence matrix
are linearly independent over `ℝ`. Loops (`tail e = head e`) and parallel edges are allowed. -/
def IsCycleMatroidOf {α : Type} (M : Matroid α) (V : Type) [DecidableEq V]
    (tail head : α → V) : Prop :=
  ∀ I : Set α, M.Indep I ↔
    (I ⊆ M.E ∧ LinearIndepOn ℝ
      (fun e : α => (Pi.single (head e) (1 : ℝ) - Pi.single (tail e) (1 : ℝ) : V → ℝ)) I)

/-- **Graphic matroid** (p. 1): `M = M(G)` for some finite multigraph `G`. -/
def IsGraphic {α : Type} (M : Matroid α) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (tail head : α → V),
    IsCycleMatroidOf M V tail head

/-- **Cographic matroid** (p. 1): `M = M*(G)`, i.e. the dual `M✶` is graphic. -/
def IsCographic {α : Type} (M : Matroid α) : Prop :=
  IsGraphic M✶

/-- **Cycle** of a matroid (p. 3): a (possibly empty) disjoint union of circuits. -/
def IsCycle {α : Type} (M : Matroid α) (C : Set α) : Prop :=
  C ⊆ M.E ∧ ∃ S : Set (Set α), S.PairwiseDisjoint id ∧ (∀ D ∈ S, M.IsCircuit D) ∧ ⋃₀ S = C

/-- The `5 × 10` matrix `[I₅ | A]` over `GF(2)` whose column matroid is Seymour's `R10`; `A` is the
circulant with rows `11001, 11100, 01110, 00111, 10011`. (The paper does not print `R10`; this
binary matrix is a modelling choice with R10's known invariants: 162 bases, fifteen 4-circuits and
fifteen 6-circuits.) -/
def r10Matrix : Matrix (Fin 5) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1, 1, 0, 0, 1;
     0, 1, 0, 0, 0, 1, 1, 1, 0, 0;
     0, 0, 1, 0, 0, 0, 1, 1, 1, 0;
     0, 0, 0, 1, 0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1, 0, 0, 1, 1]

/-- The `j`-th column of `r10Matrix`. -/
def r10Col (j : Fin 10) : Fin 5 → ZMod 2 := fun i => r10Matrix i j

/-- `M` **is (isomorphic to) `R10`**: some map `f` restricts to a bijection `E(M) → {0,…,9}` that
carries the independent sets of `M` exactly onto the sets of linearly independent columns of
`r10Matrix`. -/
def IsR10 {α : Type} (M : Matroid α) : Prop :=
  ∃ f : α → Fin 10, Set.BijOn f M.E Set.univ ∧
    ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndepOn (ZMod 2) r10Col (f '' I))

end RegMatroidXC.Main


