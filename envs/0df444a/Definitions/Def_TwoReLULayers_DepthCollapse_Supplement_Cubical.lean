-- Prove2me | Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Cubical
-- name    : TwoReLULayers_DepthCollapse_Supplement_Cubical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:25:22.504147+00:00
-- url     : https://prove2.me/theorems/6f2cc65d-a6f1-4d35-bd7a-79e1440b7b92
-- title:
--   Formal simplex-edge cubes, augmentation, and face directions
-- statement:
--   Let $n,k\ge0$. Label the vertices of $\Delta^n=\operatorname{conv}(0,e_1,\ldots,e_n)$ by $0,1,\ldots,n$. Choose either orientation for each of its $r=\binom{n+1}{2}$ edges. Write $t_i\in\mathbb Z^n$ for the actual oriented edge vectors and $\Gamma=\mathbb Z^n$. Distinct edge labels remain distinct formal exterior generators, even if their geometric vectors are dependent.
--
--   The complexes are represented by their canonical rational bases:
--   $$C_k^n=\mathbb Q[\Gamma]\otimes_{\mathbb Q}\bigwedge^k\mathbb Q^r,
--   \qquad D_k^n=\bigwedge^k\mathbb Q^r.$$
--   A chain is a finitely supported rational function on pairs consisting of a lattice point and a $k$-element edge-label set, ordered by the encoded vertex pairs. On a basis vector the boundary is
--   $$d_C(\gamma\otimes e_{i_1}\wedge\cdots\wedge e_{i_k})=
--   \sum_{j=1}^k(-1)^{j-1}\big((\gamma+t_{i_j})-\gamma\big)\otimes e_{i_1}\wedge\cdots\wedge\widehat e_{i_j}\wedge\cdots\wedge e_{i_k}.$$
--   Here the difference means two formal basis terms. The degree-zero boundary is zero. A cycle satisfies $d_Cx=0$; a boundary is $d_Cy$ for an actual finite chain of degree $k+1$. Augmentation $\varepsilon$ forgets the lattice coordinate and adds coefficients separately for each exterior label. The differential on $D$ is zero.
--
--   For each $n$-element vertex set $J$, let $F_J$ be the linear span of its pairwise vertex differences. The face direction condition requires that every basis box with nonzero coefficient have all its vertices in some $F_J$; $J$ may depend on the term. This is containment in a linear subspace, not a bounded simplex facet. These definitions provide the actual formal complex and the geometric support condition used by Lemmas 10–13.
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. pp. 14–17, Sections 3.1, 3.3 and 4.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Polytopes

namespace TwoReLULayers.DepthCollapse.Supplement

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Lattice (n : ℕ) := Fin n → ℤ

/-- One distinct formal label for each unordered pair of simplex vertices,
ordered by its encoded pair. This order orders exterior monomials only. -/
abbrev EdgeLabel (n : ℕ) :=
  {e : Fin ((n + 1) * (n + 1)) // e.val / (n + 1) < e.val % (n + 1)}

abbrev EdgeOrientations (n : ℕ) := EdgeLabel n → Bool

def vertexZ {n : ℕ} (i : ℕ) : Lattice n := fun j => if i = j.val + 1 then 1 else 0

/-- Arbitrary orientation of every actual edge of conv(0,e₁,...,eₙ). -/
def edgeZ {n : ℕ} (o : EdgeOrientations n) (e : EdgeLabel n) : Lattice n :=
  let a := vertexZ (e.val.val / (n + 1))
  let b := vertexZ (e.val.val % (n + 1))
  if o e then b - a else a - b

def rationalLattice {n : ℕ} (g : Lattice n) : QSpace n := fun j => (g j : ℚ)

abbrev ExteriorLabel (n k : ℕ) := {I : Finset (EdgeLabel n) // I.card = k}
abbrev CubeLabel (n k : ℕ) := Lattice n × ExteriorLabel n k

/-- The canonical basis presentation of ℚ[ℤⁿ] ⊗ ⋀ᵏℚʳ. Formal exterior labels
remain independent when their geometric edge vectors are dependent. -/
abbrev C (n k : ℕ) := CubeLabel n k →₀ ℚ
abbrev D (n k : ℕ) := ExteriorLabel n k →₀ ℚ

def eraseLabel {n k : ℕ} (I : ExteriorLabel n k) (e : EdgeLabel n) (he : e ∈ I.val) :
    ExteriorLabel n (k - 1) :=
  ⟨I.val.erase e, by simpa [I.property] using Finset.card_erase_of_mem he⟩

/-- Exact signed cubical boundary: γ(gᵢ−1), with sign given by the zero-based
position in the increasing exterior monomial; the jth label alone is removed. -/
def cubeBoundary {n k : ℕ} (o : EdgeOrientations n) (b : CubeLabel n k) : C n (k - 1) :=
  ∑ e ∈ b.2.val.attach,
    ((-1 : ℚ) ^ ((b.2.val.filter (fun f => f < e.val)).card)) •
      (Finsupp.single (b.1 + edgeZ o e.val, eraseLabel b.2 e.val e.property) 1 -
       Finsupp.single (b.1, eraseLabel b.2 e.val e.property) 1)

def dC {n k : ℕ} (o : EdgeOrientations n) (x : C n k) : C n (k - 1) :=
  x.sum (fun b q => q • cubeBoundary o b)

/-- Ordinary nonnegative-degree cycles: d is zero in degree zero. -/
def IsCycle {n k : ℕ} (o : EdgeOrientations n) (x : C n k) : Prop := dC o x = 0

def IsBoundary {n k : ℕ} (o : EdgeOrientations n) (x : C n k) : Prop :=
  ∃ y : C n (k + 1), dC o y = x

/-- Group-algebra augmentation, tensored with the identity on formal exterior labels.
The target D has zero differential. -/
def epsilon {n k : ℕ} (x : C n k) : D n k :=
  x.sum (fun b q => Finsupp.single b.2 q)

/-- All vertices of the actual box, as a finite rational set. -/
def cubeVertices {n k : ℕ} (o : EdgeOrientations n) (b : CubeLabel n k) :
    Finset (QSpace n) :=
  b.2.val.powerset.image (fun J =>
    rationalLattice b.1 + ∑ e ∈ J, rationalLattice (edgeZ o e))

def vertexQ {n : ℕ} (i : Fin (n + 1)) : QSpace n := rationalLattice (vertexZ i.val)

/-- Linear direction space of a simplex facet, not the bounded facet itself. -/
def faceDirectionSpace {n : ℕ} (J : Finset (Fin (n + 1))) : Submodule ℚ (QSpace n) :=
  Submodule.span ℚ {z | ∃ i ∈ J, ∃ j ∈ J, z = vertexQ i - vertexQ j}

/-- Each nonzero basis term has its own witnessing n-vertex facet. -/
def FaceDirection {n k : ℕ} (o : EdgeOrientations n) (x : C n k) : Prop :=
  ∀ b ∈ x.support, ∃ J : Finset (Fin (n + 1)), J.card = n ∧
    ∀ v ∈ cubeVertices o b, v ∈ faceDirectionSpace J

end
end TwoReLULayers.DepthCollapse.Supplement


