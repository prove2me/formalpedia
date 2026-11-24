-- Prove2me | Definitions.Def_BicliqueSDP_Chain_Supplement_ProductFree
-- name    : BicliqueSDP_Chain_Supplement_ProductFree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:15:10.642699+00:00
-- url     : https://prove2.me/theorems/d514b569-4c2f-4866-b85d-649ddbb8ef96
-- title:
--   Appendix A — product-free sets, Cayley adjacency, λ₂ and complex representation dimensions
-- statement:
--   Let $\Gamma$ be a finite group and $A\subseteq\Gamma$. Product-free means that $uv\notin A$ for every $u,v\in A$. The bipartite Cayley graph has two copies of $\Gamma$, with $u$ on the left adjacent to $v$ on the right exactly when $uv\in A$.
--
--   $$M_{uv}=\mathbf 1_{uv\in A},\qquad A_{\Gamma,A}=\begin{pmatrix}0&M\\M^\mathsf T&0\end{pmatrix},\qquad\lambda_2=\lambda_2(A_{\Gamma,A}).$$
--
--   Eigenvalues are counted with multiplicity and sorted in non-increasing order. The second entry exists even for the trivial group because the adjacency matrix has $2|\Gamma|\ge2$ rows. Representations are Mathlib complex representations on $\mathbb C^d$. Nontrivial means that some group element acts by a map different from the identity, with no irreducibility or faithfulness requirement. The condition on $k$ is that it is the least dimension admitting such a representation.
--
--   These definitions fix the objects of Lemma A.1 and Theorem A.2. No value of $k$ is assigned to the trivial group, where that set of dimensions is empty. Its only product-free subset is empty. The eigenvalue definition uses Mathlib's ordered Hermitian spectral list, not a real supremum or a choice of eigenvectors.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, pp. 6, 35–36, eigenvalue notation and Appendix A

import Definitions.Def_BicliqueSDP_Chain_Model
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement
noncomputable section

variable {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]

/-- Product-free, with no commutativity assumption. -/
def IsProductFree (A : Finset Γ) : Prop := ∀ u ∈ A, ∀ v ∈ A, u * v ∉ A

/-- The source's Cayley cross-edge relation, in the order u*v. -/
def cayleyEdge (A : Finset Γ) (u v : Γ) : Prop := u * v ∈ A

instance (A : Finset Γ) : DecidableRel (cayleyEdge A) := fun u v => inferInstanceAs (Decidable (u * v ∈ A))

/-- Dimensions of nontrivial COMPLEX representations. A positive-dimensional trivial action
is excluded; irreducibility and faithfulness are not imposed. -/
def nontrivialRepDims (Γ : Type) [Group Γ] : Set ℕ :=
  {d | ∃ ρ : Representation ℂ Γ (Fin d → ℂ), ∃ g, ρ g ≠ 1}

/-- The minimum dimension is a genuine least element, not a default on the empty set. -/
def IsMinRepDim (Γ : Type) [Group Γ] (k : ℕ) : Prop := IsLeast (nontrivialRepDims Γ) k

/-- Full 2n by 2n adjacency matrix, NOT just the n by n cross block. -/
def cayleyAdj (A : Finset Γ) : Matrix (Γ ⊕ Γ) (Γ ⊕ Γ) ℝ := by
  classical
  exact fun u v => if (bipGraph (cayleyEdge A)).Adj u v then 1 else 0

/-- Structural symmetry of the undirected adjacency matrix. -/
theorem cayleyAdj_hermitian (A : Finset Γ) : (cayleyAdj A).IsHermitian := by
  ext u v
  simp only [Matrix.conjTranspose_apply, cayleyAdj, star_trivial]
  congr 1
  exact propext ((bipGraph (cayleyEdge A)).adj_comm v u)

/-- λ₂: zero-based index 1 in the non-increasing spectral list, with multiplicities.
The full graph always has at least two vertices since Γ is a group. -/
def lambda2 (A : Finset Γ) : ℝ :=
  (cayleyAdj_hermitian A).eigenvalues₀ ⟨1, by
    simp only [Fintype.card_sum]
    have : 0 < Fintype.card Γ := Fintype.card_pos
    omega⟩

end
end BicliqueSDP.Chain.Supplement


