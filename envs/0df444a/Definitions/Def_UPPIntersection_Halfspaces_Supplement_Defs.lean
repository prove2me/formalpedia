-- Prove2me | Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs
-- name    : UPPIntersection_Halfspaces_Supplement_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:59:09.249974+00:00
-- url     : https://prove2.me/theorems/76421f07-5c84-43c5-bdb5-f50c579e48c1
-- title:
--   §3.2, §7.2, §8 — spherical polynomials, degree-ordered orthonormal bases, Gegenbauer products, k-fold conjunctions and random sign matrices
-- statement:
--   These objects are used by the supplementary results of §3, §7.2 and §8. Throughout, $S^{d-1}\subseteq\mathbb R^d$ is the unit sphere with its uniform probability measure $\sigma_d$, and $G^d_i$ is the normalized Gegenbauer polynomial of Definition 3.3.
--
--   1. A function $q:S^{d-1}\to\mathbb R$ is a **polynomial of degree at most $n$** if it is the restriction to the sphere of a real polynomial in the $d$ ambient coordinates of total degree at most $n$.
--   2. A **degree-ordered orthonormal polynomial basis** is a sequence $p_0,p_1,\dots$ of polynomials on $S^{d-1}$ with degree labels $\ell(0),\ell(1),\dots$ such that each $p_j$ has degree at most $\ell(j)$, is orthogonal in $L^2(\sigma_d)$ to every polynomial of degree less than $\ell(j)$, the family is orthonormal, every polynomial on the sphere is a finite linear combination of the $p_j$, and $\ell$ is nondecreasing. Gram–Schmidt applied to the monomials in nondecreasing order of total degree (discarding zero residuals) produces such a basis, and $\ell(j)=\deg p_j$.
--   3. For $J=(j_1,\dots,j_k)\in\{0,1,2,\dots\}^k$, the tensor basis element is $\Psi_J(x_1,\dots,x_k)=\prod_{i=1}^k p_{j_i}(x_i)$.
--   4. For $\ell\in\{0,1,\dots\}^k$ and $s\in\mathbb R^k$, the Gegenbauer product is $\prod_{i=1}^kG^d_{\ell_i}(s_i)$, and the box of degree tuples of size $m$ is $\{\ell:\|\ell\|_\infty\le m\}$.
--   5. For finite $A,B\subseteq\mathbb R^d$ the sign matrix is $A_{a,b}=\operatorname{sgn}\langle a,b\rangle$.
--   6. The **$k$-fold disjoint conjunction** of a sign matrix $F$ has rows $(a_1,\dots,a_k)$, columns $(b_1,\dots,b_k)$ and entry $F_{a_1,b_1}\wedge\cdots\wedge F_{a_k,b_k}$, which is $-1$ exactly when every constituent entry is $-1$.
--   7. For points $u_1,\dots,u_N,v_1,\dots,v_N\in S^{d-1}$ the sign matrix $G_{i,j}=\operatorname{sgn}\langle u_i,v_j\rangle$.
--
--   **Formalization Note** Sign matrices are stored as matrices of bits with $\mathsf{true}$ standing for $+1$, as in the published definitions of this mission: an entry $\operatorname{sgn}\langle a,b\rangle$ is $\mathsf{true}$ iff $\langle a,b\rangle>0$ (a zero inner product is excluded by the hypotheses of every theorem that uses these matrices, or shown to have probability zero), and a $k$-fold conjunction entry is $\mathsf{true}$ iff some constituent entry is $\mathsf{true}$; for $k=2$ this is the published `andSquare`. The normalized Gegenbauer polynomials are the published `SphereSOS.Rate.geg`, defined by $G_0=1$, $G_1=t$ and the three-term recurrence of the normalized family.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 15–16 (Definition 3.3), p. 18 (§3.2: basis p_j, Ψ_J), pp. 18–19 (Theorem 3.7: coefficients and partial sums), p. 30 (G_{i,j}), pp. 31–32 (∧^k A); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace UPPIntersection.Halfspaces.Supplement

open MeasureTheory

/-- A real function `q` on the sphere `S^{d-1}` is a **polynomial of degree at most `n`** if it is
the restriction to the sphere of a real polynomial in the `d` ambient coordinates of total degree
at most `n` (§3.1–3.2, pp. 16, 18). -/
def IsSphPolyLE (d n : ℕ) (q : Sph d → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ n ∧
    ∀ x : Sph d, q x = MvPolynomial.eval (fun i => (x : EuclideanSpace ℝ (Fin d)) i) P

/-- A **degree-ordered orthonormal polynomial basis** of `L²(S^{d-1})` (§3.2, p. 18): a sequence
`p₀, p₁, …` of polynomials on the sphere with degree labels `deg j`, such that
1. `p j` is a polynomial of degree at most `deg j`;
2. `p j` is orthogonal (for the uniform probability measure) to every polynomial of degree `< deg j`;
3. the family is orthonormal;
4. every polynomial on the sphere is a finite linear combination of the `p j`;
5. the degree labels are nondecreasing.
Gram–Schmidt applied to the monomials in nondecreasing order of total degree, discarding zero
residuals, produces such a basis; `deg j` is then the exact degree of `p j`. -/
def IsDegreeOrderedONB (d : ℕ) (p : ℕ → Sph d → ℝ) (deg : ℕ → ℕ) : Prop :=
  (∀ j, IsSphPolyLE d (deg j) (p j)) ∧
  (∀ j (n : ℕ) (r : Sph d → ℝ), n < deg j → IsSphPolyLE d n r →
      ∫ x, p j x * r x ∂(sphereLaw d) = 0) ∧
  (∀ j j', ∫ x, p j x * p j' x ∂(sphereLaw d) = if j = j' then 1 else 0) ∧
  (∀ (n : ℕ) (r : Sph d → ℝ), IsSphPolyLE d n r →
      ∃ (S : Finset ℕ) (a : ℕ → ℝ), ∀ x, r x = ∑ j ∈ S, a j * p j x) ∧
  Monotone deg

/-- The tensor basis element `Ψ_J(x₁, …, x_k) = ∏_i p_{j_i}(x_i)` on `(S^{d-1})^k` (p. 18). -/
def psi {d k : ℕ} (p : ℕ → Sph d → ℝ) (J : Fin k → ℕ) (x : Fin k → Sph d) : ℝ :=
  ∏ i, p (J i) (x i)

/-- The product of normalized Gegenbauer polynomials `∏_i G^d_{ℓ_i}(s_i)` (Theorem 3.7, p. 18). -/
noncomputable def gegProd (d : ℕ) {k : ℕ} (ℓ : Fin k → ℕ) (s : Fin k → ℝ) : ℝ :=
  ∏ i, (SphereSOS.Rate.geg d (ℓ i)).eval (s i)

/-- The degree tuples `ℓ ∈ ℕ^k` with `‖ℓ‖_∞ ≤ m`, indexing the paper's finite partial sums (p. 19). -/
def boxIdx (k m : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (m + 1)

/-- The sign matrix `A_{a,b} = sgn⟨a,b⟩` of two finite sets `A, B ⊆ ℝ^d` (Lemma 8.4), stored with
`true = +1`: the entry is `true` iff `⟨a,b⟩ > 0`. -/
noncomputable def finSignMat {d : ℕ} (A B : Finset (EuclideanSpace ℝ (Fin d))) :
    Matrix A B Bool :=
  fun a b => decide (0 < inner ℝ (a : EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d)))

/-- The `k`-fold disjoint conjunction `∧^k F` of a sign matrix (§8, pp. 31–32): rows
`(a₁, …, a_k)`, columns `(b₁, …, b_k)`, entry `F(a₁,b₁) ∧ ⋯ ∧ F(a_k,b_k)`, which is `-1` exactly when
every constituent entry is `-1`. In the `Bool` encoding (`true = +1`) the entry is `true` iff some
constituent entry is `true`. -/
def kfoldAnd {X Y : Type} (k : ℕ) (F : Matrix X Y Bool) : Matrix (Fin k → X) (Fin k → Y) Bool :=
  fun a b => decide (∃ i, F (a i) (b i) = true)

/-- The random-point sign matrix `G_{i,j} = sgn⟨u_i, v_j⟩` (Theorems 7.2, 8.6), stored with
`true = +1`: the entry is `true` iff `⟨u_i, v_j⟩ > 0`. -/
noncomputable def randSignMat {d N : ℕ} (u v : Fin N → Sph d) : Matrix (Fin N) (Fin N) Bool :=
  fun i j => decide (0 < inner ℝ (u i : EuclideanSpace ℝ (Fin d)) (v j : EuclideanSpace ℝ (Fin d)))

end UPPIntersection.Halfspaces.Supplement


