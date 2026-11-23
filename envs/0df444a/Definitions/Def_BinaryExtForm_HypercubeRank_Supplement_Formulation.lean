-- Prove2me | Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation
-- name    : BinaryExtForm_HypercubeRank_Supplement_Formulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:59:34.282784+00:00
-- url     : https://prove2.me/theorems/fff16c0d-8fb1-4d11-b25e-0408f29df55c
-- title:
--   pp. 4, 6, 9 — binary extended formulation Q, faces and their dimension, G_{I,α}, property P^i_{α_1,…,α_ℓ}, sequential convexification of y-variables, rank of P^i (Definition 4.1)
-- statement:
--   These definitions extend the vocabulary of the published file `BinaryExtForm.HypercubeRank.Model` (polytopes, binarizations, natural binarizations, slices $B(f)$, the lift-and-project rank) to a whole binary extended formulation, as in §§2.2, 3 and 4 of Aprile, Conforti and Di Summa.
--
--   **Binary extended formulation (p. 4).** Let $P \subseteq [0,k]^p \times \mathbb R^{n-p}$ be a polytope with variables $x_1, \dots, x_n$, and for each $i \in [p]$ let $B_i \subseteq \mathbb R \times [0,1]^d$ be a binarization of $x_i$, with variables $(x_i, y_i)$, $y_i = (y_{i1}, \dots, y_{id})$. The *binary extended formulation* of $P$ with binarizations $B_1, \dots, B_p$ is
--   $$Q := \{(x, y) \in \mathbb R^n \times [0,1]^{pd} : x \in P,\ (x_i, y_i) \in B_i\ \forall i \in [p]\}.$$
--   $V(Q)$ denotes its vertex set and $\pi_x$ the projection onto the $x$-space.
--
--   **Faces and the subspaces $G_{I,\alpha}$ (p. 6).** A *face* of the polytope $P$ is a convex subset $F \subseteq P$ such that whenever an open segment between two points of $P$ meets $F$, both endpoints lie in $F$; for polytopes these are exactly the usual faces, including $\emptyset$ and $P$. The *dimension* of $F$ is the dimension of the linear space spanned by the differences of its points. For $I \subseteq [p]$ and $\alpha \in \{0, \dots, k\}^I$,
--   $$G_{I,\alpha} := \{x \in \mathbb R^n : x_i = \alpha_i\ \forall i \in I\}.$$
--
--   **Property $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$ (p. 9).** For $i \in [p]$ and integers $\alpha_1, \dots, \alpha_\ell$, a set of points $(x,y)$ satisfies property $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$ if every vertex $(\bar x, \bar y)$ of it satisfies
--   $$\bar x_i \le \alpha_j \quad\text{or}\quad \bar x_i \ge \alpha_j + 1 \qquad \text{for all } j \in [\ell];$$
--   a vertex *violates* the property when $\alpha_j < \bar x_i < \alpha_j + 1$ for some $j$.
--
--   **Sequential convexification of $y$-variables and the rank (Definition 4.1, p. 9).** For a set $S$ of points $(x,y)$ and a variable $y_{ij}$, $S_{y_{ij}} = \operatorname{conv}(\{(x,y) \in S : y_{ij} = 0\} \cup \{(x,y) \in S : y_{ij} = 1\})$. The *rank of $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$* is the smallest integer $t$ such that for some variables $y_{ij_1}, \dots, y_{ij_t}$ of the $i$-th binarization the set $((Q_{y_{ij_1}})\dots)_{y_{ij_t}}$ satisfies $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$; it is $0$ when $Q$ itself satisfies the property.
--
--   These objects are the setting of Theorems 3.1, 3.2 and 4.6 and of Observation 4.2.
--
--   **Formalization Note.** A point $(x,y)$ is a pair `(x, y)` with `x : Fin n → ℝ` and `y : Fin p → Fin d → ℝ`, where `y i j` is $y_{i,j+1}$ (0-based indices). The binarized coordinates are the first $p$: $x_i$ is `xc hpn x i = x (Fin.castLE hpn i)`, with `hpn : p ≤ n`. The pair $(x_i, y_i)$ is `block hpn z i : Fin (d+1) → ℝ`, with $x_i$ at coordinate $0$, matching the encoding of the published binarization definitions. A face is `IsFace P F := Convex ℝ F ∧ IsExtreme ℝ P F` and its dimension is `affDim F = Module.finrank ℝ (vectorSpan ℝ F)`. `G hpn I α` takes `α : Fin p → ℕ`; only its values on `I` matter, and the theorems require $\alpha_i \le k$ for $i \in I$. The print of property $\mathcal P^i$ reads "$\alpha_j \le \bar x_i$ or $\bar x_i \ge \alpha_j + 1$"; `SatisfiesP` uses $\bar x_i \le \alpha_j$, the reading fixed by the paper's own description of the violating vertices as those with $\alpha_j < \bar x_i < \alpha_j + 1$ (p. 9, after Observation 4.2, and Theorem 4.6). `ySplit` is the one-step convexification for this point type (the published `SplitConvexify` is stated on `Fin n → ℝ`), and `iterYSplit` applies a list of variables of block $i$ from left to right. `propRank` is the `sInf` of the lengths of such lists, repetitions allowed; the set is nonempty, since convexifying all $d$ variables of block $i$ gives $\operatorname{conv}\{(x,y)\in Q : y_i \in \{0,1\}^d\}$, whose vertices have integral $x_i$.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 4 (§2.2, binary extended formulation Q), p. 6 (§3, G_{I,α}, faces of P), p. 9 (§4, property P^i_{α_1,…,α_ℓ}, Definition 4.1)

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank.Supplement

open BinaryExtForm.HypercubeRank

/-- A point `(x, y) ∈ ℝ^n × ℝ^{pd}` of a binary extended formulation (Aprile–Conforti–Di Summa,
arXiv:2106.00354v1, p. 4): `x : Fin n → ℝ`, and `y i j` is the component `y_{i,j+1}` of the block
`y_i` of the `i`-th binarization (`i : Fin p`, `j : Fin d`, both 0-based). -/
abbrev Pt (n p d : ℕ) : Type := (Fin n → ℝ) × (Fin p → Fin d → ℝ)

/-- The coordinate `x_i` (`i : Fin p`) of a point of `ℝ^n`, the binarized coordinates being the first
`p` ones (`P ⊆ [0, k]^p × ℝ^{n−p}`, p. 4). -/
def xc {n p : ℕ} (hpn : p ≤ n) (x : Fin n → ℝ) (i : Fin p) : ℝ := x (Fin.castLE hpn i)

/-- The pair `(x_i, y_i) ∈ ℝ × ℝ^d` of a point `(x, y)`, encoded as in the base model as a function
`Fin (d + 1) → ℝ` with `x_i` at coordinate `0` and `y_{i,j+1}` at coordinate `j.succ`. -/
def block {n p d : ℕ} (hpn : p ≤ n) (z : Pt n p d) (i : Fin p) : Fin (d + 1) → ℝ :=
  Fin.cons (α := fun _ : Fin (d + 1) => ℝ) (xc hpn z.1 i) (z.2 i)

/-- The binary extended formulation of `P` with binarizations `B₁, …, B_p` (p. 4):
`Q := {(x, y) ∈ ℝ^n × [0, 1]^{pd} : x ∈ P, (x_i, y_i) ∈ B_i ∀ i ∈ [p]}`. -/
def BEF {n p d : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (B : Fin p → Set (Fin (d + 1) → ℝ)) :
    Set (Pt n p d) :=
  {z | z.1 ∈ P ∧ (∀ i j, 0 ≤ z.2 i j ∧ z.2 i j ≤ 1) ∧ ∀ i, block hpn z i ∈ B i}

/-- A face of a polytope `P`: a convex extreme subset of `P` (for a polytope these are exactly its
faces, `∅` and `P` included). -/
def IsFace {E : Type*} [AddCommGroup E] [Module ℝ E] (P F : Set E) : Prop :=
  Convex ℝ F ∧ IsExtreme ℝ P F

/-- The (affine) dimension of a set: the dimension of the vector space spanned by its differences. -/
noncomputable def affDim {n : ℕ} (F : Set (Fin n → ℝ)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

/-- The subspace `G_{I,α} := {x ∈ ℝ^n : x_i = α_i ∀ i ∈ I}` for `I ⊆ [p]` (p. 6). Only the values
of `α` on `I` matter; the theorems require `α_i ∈ {0, …, k}` for `i ∈ I`. -/
def G {n p : ℕ} (hpn : p ≤ n) (I : Finset (Fin p)) (α : Fin p → ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i ∈ I, xc hpn x i = α i}

/-- A set `S` of points `(x, y)` satisfies property `P^i_{α_1,…,α_ℓ}` (p. 9) if every vertex
`(x̄, ȳ)` of `S` satisfies `x̄_i ≤ α_j` or `x̄_i ≥ α_j + 1` for all `j ∈ [ℓ]`. (The print reads
"`α_j ≤ x̄_i` or `x̄_i ≥ α_j + 1`"; the violating vertices are those with `α_j < x̄_i < α_j + 1`,
p. 9.) -/
def SatisfiesP {n p d ℓ : ℕ} (hpn : p ≤ n) (S : Set (Pt n p d)) (i : Fin p) (α : Fin ℓ → ℤ) :
    Prop :=
  ∀ z ∈ Set.extremePoints ℝ S, ∀ j, xc hpn z.1 i ≤ α j ∨ (α j : ℝ) + 1 ≤ xc hpn z.1 i

/-- One step of sequential convexification on the variable `y_{i,j+1}`:
`S_{y_{ij}} = conv(S ∩ {y_{ij} ∈ {0, 1}})` (the published `SplitConvexify`, for this point type). -/
def ySplit {n p d : ℕ} (S : Set (Pt n p d)) (i : Fin p) (j : Fin d) : Set (Pt n p d) :=
  convexHull ℝ (S ∩ {z | z.2 i j = 0 ∨ z.2 i j = 1})

/-- `((S_{y_{ij_1}}) …)_{y_{ij_t}}` for the list `[j_1, …, j_t]` of variables of block `i`,
applied left to right. -/
def iterYSplit {n p d : ℕ} (S : Set (Pt n p d)) (i : Fin p) (l : List (Fin d)) : Set (Pt n p d) :=
  l.foldl (fun T j => ySplit T i j) S

/-- Definition 4.1 (p. 9): the rank of `P^i_{α_1,…,α_ℓ}` for the binary extended formulation `Q`
of `P`, the least `t` such that for some variables `y_{ij_1}, …, y_{ij_t}` of the `i`-th
binarization, `((Q_{y_{ij_1}}) …)_{y_{ij_t}}` satisfies `P^i_{α_1,…,α_ℓ}` (`t = 0` when `Q` does). -/
noncomputable def propRank {n p d ℓ : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ))
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (i : Fin p) (α : Fin ℓ → ℤ) : ℕ :=
  sInf {t : ℕ | ∃ l : List (Fin d), l.length = t ∧
    SatisfiesP hpn (iterYSplit (BEF hpn P B) i l) i α}

end BinaryExtForm.HypercubeRank.Supplement


