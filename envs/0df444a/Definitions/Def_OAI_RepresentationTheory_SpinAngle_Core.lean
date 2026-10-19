-- Prove2me | Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core
-- name    : OAI_RepresentationTheory_SpinAngle_Core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:09:46.492045+00:00
-- url     : https://prove2.me/theorems/1bb60c64-a6c4-4771-b1aa-e520f2c32e49
-- title:
--   Irreducible polynomial carriers of $U(q)$, signed spin tensors, even densities, Haar twirls and matrix square roots
-- statement:
--   This file sets up the objects used to study isotypic projections for the group $U(q)\times U(q)$ acting on tensor powers of the signed spin space $\mathbb{C}^{S_q}$, where $S_q=[q]\times\{0,1\}$ is the signed spin alphabet.
--
--   **Notation.** $q\in\mathbb{N}$, $[q]=\{0,1,\dots,q-1\}$, $M_q$ is the algebra of complex $q\times q$ matrices and $U(q)\subseteq M_q$ the unitary group. The second coordinate $s$ of a letter $(j,s)\in S_q$ is a parity bit ($s=0$ even, $s=1$ odd). For a finite set $\iota$, $T_\iota=\mathbb{C}^{[q]^\iota}\cong(\mathbb{C}^q)^{\otimes\iota}$ is the Hilbert space with orthonormal basis $(e_x)_{x\in[q]^\iota}$; a matrix $a\in M_q$ acts on it by $a^{\otimes\iota}$, with entries $(a^{\otimes\iota})_{x,y}=\prod_{i\in\iota}a_{x_iy_i}$, and $g\mapsto g^{\otimes\iota}$ is the tensor-power representation of $U(q)$. For a Young diagram $D$ whose first column has length at most $q$ (so $D$ has at most $q$ rows), $\mathrm{cells}(D)$ is its set of cells $(i,j)$ (row $i$, column $j$), $|D|$ the number of cells, $r_i(D)$ the length of row $i$, $T_D=T_{\mathrm{cells}(D)}$, $\mathrm{Col}(D)$ the group of permutations of $\mathrm{cells}(D)$ that keep every cell in its column, and $\tau_D:\mathrm{cells}(D)\to[q]$, $(i,j)\mapsto i$, the row colouring. As in the base definitions, $\mathrm{Alt}(D)\subseteq T_D$ is the $U(q)$-invariant subspace of tensors $v$ with $v(x\circ\sigma)=\operatorname{sgn}(\sigma)\,v(x)$ for all $\sigma\in\mathrm{Col}(D)$, the highest vector is $h_D=\sum_{\sigma\in\mathrm{Col}(D)}\operatorname{sgn}(\sigma)\,e_{\tau_D\circ\sigma}\in\mathrm{Alt}(D)$, and the carrier $V_D\subseteq\mathrm{Alt}(D)$ is the $U(q)$-subrepresentation spanned by the vectors $g^{\otimes\mathrm{cells}(D)}h_D$, $g\in U(q)$. For a finite index set $\Omega$, $M_\Omega$ denotes the complex matrices with rows and columns indexed by $\Omega$, and $A\succeq0$ means that $A$ is positive semidefinite.
--
--   The file defines the following objects.
--
--   1. **Weight element.** $N_D=|D|\,q+1$, $\zeta_D=e^{2\pi i/N_D}$ (a primitive $N_D$-th root of unity) and
--   $$
--   w_D=\operatorname{diag}\bigl(1,\zeta_D,\zeta_D^{2},\dots,\zeta_D^{q-1}\bigr)\in U(q).
--   $$
--   The operator $w_D^{\otimes\mathrm{cells}(D)}$ multiplies $e_x$ by $\zeta_D^{\sum_c x_c}$, and since $\sum_c x_c\le|D|(q-1)<N_D$, distinct values of $\sum_c x_c$ give distinct eigenvalues.
--
--   2. **Content.** For a finite set $\iota$, a finite alphabet $\Sigma$, a word $x\in\Sigma^\iota$ and a letter $j\in\Sigma$, the content $c_j(x)=\#\{i\in\iota:\ x_i=j\}$ is the number of occurrences of $j$ in $x$.
--
--   3. **Highest monomial.** For $t=(t_0,\dots,t_{q-1})\in\mathbb{R}^q$,
--   $$
--   m_D(t)=\prod_{c\in\mathrm{cells}(D)}t_{\tau_D(c)}=\prod_{i<q}t_i^{\,r_i(D)}.
--   $$
--
--   4. **Sorted spectrum.** For a Hermitian $A\in M_q$: its real eigenvalues $\gamma_0(A)\ge\gamma_1(A)\ge\dots\ge\gamma_{q-1}(A)$, listed with multiplicity in nonincreasing order; an orthonormal basis $u_0,\dots,u_{q-1}$ of $\mathbb{C}^q$ with $Au_k=\gamma_k(A)\,u_k$; and the unitary change-of-basis matrix $U_A\in U(q)$ with entries $(U_A)_{ik}=(u_k)_i$, whose columns are these eigenvectors, so that $A=U_A\operatorname{diag}(\gamma(A))\,U_A^{*}$.
--
--   5. **Carrier embedding and Hermitian action.** $\iota_D:V_D\to T_D$ is the isometric inclusion, its range is regarded as a $U(q)$-subrepresentation of $T_D$, and $\hat h_D\in V_D$ is the highest vector $h_D$ regarded as an element of the carrier. For a Hermitian $a\in M_q$, $\mathcal H_D(a):V_D\to V_D$ is the restriction of $a^{\otimes\mathrm{cells}(D)}$ to the carrier, that is, the unique linear map with
--   $$
--   \iota_D\circ\mathcal H_D(a)=a^{\otimes\mathrm{cells}(D)}\circ\iota_D .
--   $$
--   It is well defined because every $U(q)$-invariant subspace of a tensor power $T_\iota$ is also invariant under $a^{\otimes\iota}$ for Hermitian $a$, a fact established in the file.
--
--   6. **Slice maps.** For finite-dimensional complex inner product spaces $E,F$ and linear functionals $\phi\in E^{*}$, $\psi\in F^{*}$, the right slice $E\otimes F\to E$ is the linear map $x\otimes y\mapsto\psi(y)\,x$ and the left slice $E\otimes F\to F$ is $x\otimes y\mapsto\phi(x)\,y$.
--
--   7. **Pair tensor space.** For finite sets $\iota,\kappa$, $P_{\iota,\kappa}=T_\iota\otimes T_\kappa$ with the orthonormal product basis $e_x\otimes e_y$, $(x,y)\in[q]^\iota\times[q]^\kappa$. It carries the representation $(g_0,g_1)\mapsto g_0^{\otimes\iota}\otimes g_1^{\otimes\kappa}$ of $U(q)\times U(q)$ and the multiplicative map $M_q\times M_q\to\mathrm{End}(P_{\iota,\kappa})$, $(A_0,A_1)\mapsto A_0^{\otimes\iota}\otimes A_1^{\otimes\kappa}$. The signed content of a basis index $(x,y)$ at $(j,s)\in S_q$ is $c_{(j,0)}(x,y)=c_j(x)$ and $c_{(j,1)}(x,y)=c_j(y)$, and a function $a:S_q\to\mathbb{C}$ gives the diagonal pair $\bigl(\operatorname{diag}(a(j,0))_{j\in[q]},\ \operatorname{diag}(a(j,1))_{j\in[q]}\bigr)\in M_q\times M_q$.
--
--   8. **Signed carrier.** For Young diagrams $\lambda$ (even part) and $\mu$ (odd part), each with at most $q$ rows, $V_{\lambda,\mu}=V_\lambda\otimes V_\mu$ carries the representation $(g_0,g_1)\mapsto g_0^{\otimes\mathrm{cells}(\lambda)}|_{V_\lambda}\otimes g_1^{\otimes\mathrm{cells}(\mu)}|_{V_\mu}$ of $U(q)\times U(q)$, and the file records that this representation is irreducible. Further, $\iota_{\lambda,\mu}=\iota_\lambda\otimes\iota_\mu:V_{\lambda,\mu}\to P_{\mathrm{cells}(\lambda),\mathrm{cells}(\mu)}$ is the isometric embedding, $\mathcal H_{\lambda,\mu}(A_0,A_1)=\mathcal H_\lambda(A_0)\otimes\mathcal H_\mu(A_1)$ for Hermitian $A_0,A_1\in M_q$, and $\hat h_\lambda\otimes\hat h_\mu$ is the highest vector of $V_{\lambda,\mu}$.
--
--   9. **Even densities.** A pair $(A_0,A_1)\in M_q\times M_q$ is an even density if $A_0\succeq0$, $A_1\succeq0$ and $\operatorname{tr}A_0+\operatorname{tr}A_1=1$. Its matrix is the block-diagonal matrix $A_0\oplus A_1\in M_{S_q}$, $(A_0\oplus A_1)_{(i,s),(j,t)}=\delta_{st}\,(A_s)_{ij}$, which is positive semidefinite with trace $1$ and is thereby packaged as a density matrix on $S_q$ (item 14). For a nonempty finite family $(A^{(j)})_{j\in J}$ of even densities, the mean is the componentwise average $\frac{1}{|J|}\sum_{j\in J}A^{(j)}$, again an even density. A pair $(g_0,g_1)\in U(q)\times U(q)$ acts on pairs of matrices by conjugation, $(A_0,A_1)\mapsto(g_0A_0g_0^{*},\,g_1A_1g_1^{*})$.
--
--   10. **Big LU cell.** For $n\in\mathbb{N}$ let $M_n$ be the complex $n\times n$ matrices indexed by $[n]$. For $\alpha\in\mathbb{C}$, $b,c\in\mathbb{C}^n$ and $B\in M_n$, the bordered matrix is
--   $$
--   \begin{pmatrix}\alpha&b^{\top}\\ c&B\end{pmatrix}\in M_{n+1}.
--   $$
--   A matrix $L\in M_n$ is lower unipotent if $L_{ij}=0$ for $i<j$ and $L_{ii}=1$ for all $i$, and the big cell $\mathcal B_n\subseteq M_n$ is the set of products $LU$ with $L$ lower unipotent and $U$ upper triangular.
--
--   11. **Polynomial coordinates of the lower unipotent orbit.** $\mathcal L_q=\{(i,j)\in[q]^2:\ j<i\}$ indexes the strictly lower triangular positions, so $|\mathcal L_q|=q(q-1)/2$. In the polynomial ring $\mathbb{C}[X_z: z\in\mathcal L_q]$ the generic lower unipotent matrix $\Lambda$ has entries $\Lambda_{ij}=X_{(i,j)}$ for $j<i$, $\Lambda_{ii}=1$, and $\Lambda_{ij}=0$ for $j>i$. For $x\in[q]^{\mathrm{cells}(D)}$ the lower coordinate
--   $$
--   F_x=\sum_{y\in[q]^{\mathrm{cells}(D)}}\Bigl(\prod_{c\in\mathrm{cells}(D)}\Lambda_{x_cy_c}\Bigr)\,h_D(y)
--   $$
--   is the $x$-coordinate of $\Lambda^{\otimes\mathrm{cells}(D)}h_D$; it has total degree at most $|D|$ and is therefore also regarded as an element of the space of polynomials of degree at most $|D|$ in each variable. For $L\in M_q$, the point $\pi(L)=(L_{ij})_{(i,j)\in\mathcal L_q}\in\mathbb{C}^{\mathcal L_q}$ records its strictly lower entries. Two general devices accompany these: for a finite set $\sigma$ and $p\in\mathbb{N}$, the bijection between exponent vectors $f\in\mathbb{N}^\sigma$ with $f_i\le p$ for all $i$ and functions $\sigma\to\{0,1,\dots,p\}$; and, for a finite family $(P_x)_{x\in X}$ in the space $\mathcal R_p(\sigma)$ of polynomials in the variables $\sigma$ of degree at most $p$ in each variable, the linear map $\mathcal R_p(\sigma)^{*}\to\mathbb{C}^X$, $\phi\mapsto(\phi(P_x))_{x\in X}$.
--
--   12. **Haar twirl.** For a compact topological group $G$ with its Borel $\sigma$-algebra, $\mu_G$ is the Haar measure normalised by $\mu_G(G)=1$, a left-invariant probability measure. For a monoid homomorphism $\rho:G\to\mathcal A$ into a complete normed real algebra $\mathcal A$ and $a\in\mathcal A$, the conjugates are $g\mapsto\rho(g)\,a\,\rho(g^{-1})$ and the twirl is the Bochner integral
--   $$
--   \mathcal T_\rho(a)=\int_G\rho(g)\,a\,\rho(g^{-1})\,d\mu_G(g).
--   $$
--   A representation of $G$ on a finite-dimensional complex inner product space $E$ is also viewed as a homomorphism into the algebra $\mathcal L(E)$ of continuous linear operators, and the trace is viewed as a continuous linear functional on $\mathcal L(E)$. The unitary group of a nonempty finite index set is compact, and $U(q)\times U(q)$ is given its Borel $\sigma$-algebra and, for $q\ge1$, is compact.
--
--   13. **Matrix functions and Kronecker products.** For a finite index set $\Omega$ and a Hermitian $a\in M_\Omega$ with spectral decomposition $a=\sum_{\gamma}\gamma\,E_\gamma$ over its distinct eigenvalues,
--   $$
--   \sqrt{a}=\sum_{\gamma}\sqrt{\max(\gamma,0)}\,E_\gamma,\qquad a_{+}^{-1/2}=\sum_{\gamma>0}\gamma^{-1/2}E_\gamma,\qquad \operatorname{supp}(a)=\sum_{\gamma\ne0}E_\gamma ,
--   $$
--   so that for $a\succeq0$ these are the positive square root, the inverse square root on the range, and the support projection. For a finite family $(a_i)_{i\in\iota}$ in $M_\Omega$, the Kronecker product $\bigotimes_{i\in\iota}a_i\in M_{\Omega^\iota}$ has entries $\prod_{i\in\iota}(a_i)_{x_iy_i}$.
--
--   14. **Density matrices and averages.** A density matrix on $\Omega$ is a matrix $\rho\in M_\Omega$ with $\rho\succeq0$ and $\operatorname{tr}\rho=1$; for a finite family $(\rho_j)_{j\in C}$ of density matrices the average is $\frac{1}{|C|}\sum_{j\in C}\rho_j$.
--
--   These objects support the one-sided type-angle bound. There $U(q)\times U(q)$ acts on $(\mathbb{C}^{S_q})^{\otimes\tau}$ through $(g_0,g_1)\mapsto(g_0\oplus g_1)^{\otimes\tau}$, and a type label $(\lambda,\mu)$ determines the orthogonal projection onto the $V_{\lambda,\mu}$-isotypic component. The weight element and the slice maps are used to show that $V_D$ and $V_{\lambda,\mu}$ are irreducible; Hermitian actions, sorted spectra, highest monomials, even densities and the Haar twirl are used to dominate a type projection by $e^{H}\dim V_{\lambda,\mu}$ times a convex combination of tensor powers $(A_0\oplus A_1)^{\otimes\tau}$ of even densities, where $H=N\log N-\sum_i n_i\log n_i$ for the $2q$ row lengths $n_i$ of $\lambda$ and $\mu$ and $N=\sum_i n_i$; the big cell and the polynomial coordinates give the dimension bound $\dim V_D\le(|D|+1)^{q(q-1)/2}$; and square roots, supports, Kronecker products and averaged density matrices enter the trace inequalities that compare row and column projections over a board of cells.
--
--   **Formalization Note** In order of the items above, the Lean objects are `weightOrder`, `weightRoot`, `weightElement`; `TensorRep.content`; `highestMonomial`; `SortedSpectrum.values`, `basis`, `changeBasis` (eigenvalues and eigenvector basis from Mathlib's spectral theorem for the symmetric operator `toEuclideanLin A`, whose eigenvalues are sorted in nonincreasing order); `PolynomialCarrier.inclusion`, `image`, `hermitianAction`, `highestVector`; `ExternalTensor.rightSlice`, `leftSlice`; `SignedTensor.PairRaw`, `pairRep`, `pairAction`, `pairBasis`, `pairContent`, `diagPair`; the instance `SignedCarrier.irreducible` together with `SignedCarrier.inclusion`, `hermitianAction`, `highestVector`; `SignedTensor.IsEvenDensity`, the subtype `EvenDensity q` with `matrix`, `toDensity` and `mean` (built from `SignedTensor.evenAverage`), and `SignedTensor.conjugateDensity`; `DenseLU.Mat`, `border`, `LowerUnipotent`, `bigCell`; `PolyDimension.boundedExponentEquiv` (on finitely supported exponent vectors), `LowerIndex`, `lowerEntry`, `valueTranspose` (on Mathlib's `restrictDegree`), and `lowerCoordinate`, `lowerCoordinateBounded`, `lowerParameters`; `CompactTwirl.compactHaar` (the Haar measure normalised on the compact set `univ`, with probability-measure and left-invariance instances), `conjugate`, `twirl`, `continuousAction`, `operatorTrace`, the lemma `unitaryGroup_compactSpace` and the measurable, Borel and compact instances on `SignedTensor.Group q`; `MatrixAnalysis.root`, `invRoot`, `support` (continuous functional calculus `cfc`), `TensorMatrix.tensor`, the structure `MatrixAnalysis.Density` and `MatrixAnalysis.average`. The parity bit is a `Bool`, with `false` for the even part and `true` for the odd part. Lean conventions enter as follows: `cfc` returns $0$ for a matrix that is not self-adjoint, and $\sqrt{x}=0$ for $x<0$ and $0^{-1}=0$ yield the formulas of item 13; an average over an empty index type is $0$ (the mean of even densities assumes a nonempty family); and the twirl, being a Bochner integral, is $0$ for a non-integrable integrand. The file also contains the lemmas these definitions rely on: irreducibility of a cyclic subrepresentation generated by a vector that spans an eigenspace of one group element, column sorting in Young diagrams, one-dimensionality of the top $w_D$-eigenspace of $\mathrm{Alt}(D)$ and irreducibility of $V_D$, commutation of $U(q)$-intertwiners between tensor powers with $a^{\otimes\iota}$ for Hermitian $a$, irreducibility of external tensor products of irreducible unitary representations, positivity and trace of block-diagonal matrices, closure of even densities under averaging, compactness of unitary groups, and a tensor-product induction principle kept for Lean 4.33 compatibility.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Core.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/Core.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SpinAngle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SpinAngle

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace SpinAngle.Specht

variable {G : Type*} [contextInstance10_21 : Group G]
variable {E : Type*} [contextInstance11_21 : NormedAddCommGroup E] [contextInstance11_44 : InnerProductSpace ℂ E]

lemma self_mem_cyclic (ρ : Representation ℂ G E) (e : E) : e ∈ cyclic ρ e := by
  exact Submodule.subset_span ⟨1, by simp⟩

variable [contextInstance32_9 : FiniteDimensional ℂ E]

lemma starProjection_rep (ρ : Representation ℂ G E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (U : Subrepresentation ρ) (g : G) (v : E) :
    U.toSubmodule.starProjection (ρ g v) = ρ g (U.toSubmodule.starProjection v) := by
  apply U.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact U.apply_mem_toSubmodule g (U.toSubmodule.starProjection_apply_mem v)
  · intro w hw
    have hw' := U.apply_mem_toSubmodule g⁻¹ hw
    have he : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← map_sub]
    conv_lhs => rhs; rw [← he]
    rw [hunit]
    exact U.toSubmodule.starProjection_inner_eq_zero v _ hw'

theorem simple_eigen_submodule_alternative (ρ : Representation ℂ G E) (e : E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g₀ : G) (c : ℂ) (heig : ρ g₀ e = c • e)
    (hsimple : ∀ v : E, ρ g₀ v = c • v → v ∈ Submodule.span ℂ {e})
    (U : Subrepresentation ρ) :
    cyclic ρ e ≤ U ∨ ∀ u ∈ U, ∀ v ∈ cyclic ρ e, ⟪v, u⟫_ℂ = 0 := by
  classical
  by_cases he : e ∈ U
  · left
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact U.apply_mem_toSubmodule g he)
  · right
    have hp : U.toSubmodule.starProjection e = 0 := by
      have hpeig : ρ g₀ (U.toSubmodule.starProjection e) =
          c • U.toSubmodule.starProjection e := by
        rw [← starProjection_rep ρ hunit U g₀ e, heig, map_smul]
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hsimple _ hpeig)
      by_cases ha0 : a = 0
      · simpa [ha0] using ha.symm
      · apply False.elim
        apply he
        have hm := U.toSubmodule.starProjection_apply_mem e
        rw [← ha] at hm
        have hh := U.toSubmodule.smul_mem a⁻¹ hm
        change e ∈ U.toSubmodule
        simpa [smul_smul, ha0] using hh
    have heorth (u : E) (hu : u ∈ U) : ⟪e, u⟫_ℂ = 0 := by
      have hh := U.toSubmodule.starProjection_inner_eq_zero e u hu
      simpa [hp] using hh
    intro u hu v hv
    have horth (g : G) : ⟪ρ g e, u⟫_ℂ = 0 := by
      have hgu : ρ g⁻¹ u ∈ U := U.apply_mem_toSubmodule g⁻¹ hu
      have hi := hunit g e (ρ g⁻¹ u)
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using hi.trans (heorth _ hgu)
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨g, rfl⟩ := hv; exact horth g
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul a x hx ih => simp [ih]

theorem cyclic_irreducible_of_simple_eigen (ρ : Representation ℂ G E) (e : E) (he : e ≠ 0)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g₀ : G) (c : ℂ) (heig : ρ g₀ e = c • e)
    (hsimple : ∀ v : E, ρ g₀ v = c • v → v ∈ Submodule.span ℂ {e}) :
    Representation.IsIrreducible (cyclic ρ e).toRepresentation := by
  let S := cyclic ρ e
  let eS : S.toSubmodule := ⟨e, self_mem_cyclic ρ e⟩
  have heS : eS ≠ 0 := by intro hh; apply he; exact congrArg Subtype.val hh
  have htb : (⊤ : Subrepresentation S.toRepresentation) ≠ ⊥ := by
    intro hh
    have hel : eS ∈ (⊤ : Subrepresentation S.toRepresentation) := by trivial
    rw [hh] at hel
    exact heS hel
  let : Nontrivial (Subrepresentation S.toRepresentation) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨S.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  rcases simple_eigen_submodule_alternative ρ e hunit g₀ c heig hsimple U' with h | h
  · right
    apply top_unique
    intro u _
    obtain ⟨v, hv, heq⟩ := h u.property
    have hvu : v = u := Subtype.ext heq
    exact hvu ▸ hv
  · left
    apply bot_unique
    intro u hu
    have hum : (u : E) ∈ U' := ⟨u, hu, rfl⟩
    have hh := h _ hum _ u.property
    have hz : (u : E) = 0 := inner_self_eq_zero.mp hh
    exact Subtype.ext hz
end SpinAngle.Specht

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance135_23 : Fintype ι] [contextInstance135_35 : DecidableEq ι] [contextInstance135_51 : Fintype n] [contextInstance135_63 : DecidableEq n]

lemma tensor_star
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (a : ι → Matrix n n ℂ) :
    tensor (fun i => star (a i)) = star (tensor a) := by
  ext x y
  simp [tensor, Matrix.star_apply]

lemma tensor_diagonal
    {ι : Type*} {n : Type*}
    [contextInstance135_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance135_63 : DecidableEq n] (a : ι → n → ℂ) :
    tensor (fun i => Matrix.diagonal (a i)) = Matrix.diagonal (fun x => ∏ i, a i (x i)) := by
  ext x y
  classical
  by_cases h : x = y
  · subst y
    simp [tensor]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [tensor, Matrix.diagonal_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma tensor_mem_unitary (a : ι → Matrix.unitaryGroup n ℂ) :
    tensor (fun i => (a i : Matrix n n ℂ)) ∈ Matrix.unitaryGroup (ι → n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', ← tensor_star, ← tensor_mul]
  convert tensor_one (ι := ι) (n := n) using 1
  congr 1
  funext i
  exact (a i).property.1

lemma toEuclideanLin_unitary (a : Matrix n n ℂ) (ha : a ∈ Matrix.unitaryGroup n ℂ)
    (v w : EuclideanSpace ℂ n) :
    ⟪Matrix.toEuclideanLin a v, Matrix.toEuclideanLin a w⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪v, (Matrix.toEuclideanLin (star a) * Matrix.toEuclideanLin a) w⟫_ℂ = _
  rw [← toEuclideanLin_mul (ι := n), ha.1, toEuclideanLin_one (ι := n)]
  rfl

lemma rep_unitary (g : Matrix.unitaryGroup n ℂ)
    (v w : EuclideanSpace ℂ (ι → n)) : ⟪rep g v, rep g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  toEuclideanLin_unitary _ (tensor_mem_unitary (fun _ : ι => g)) v w

lemma action_diagonal (a : n → ℂ) (v : EuclideanSpace ℂ (ι → n)) (x : ι → n) :
    action (Matrix.diagonal a) v x = (∏ i, a (x i)) * v x := by
  change (Matrix.toEuclideanLin (tensor (fun _ : ι => Matrix.diagonal a)) v) x = _
  rw [tensor_diagonal]
  change (Matrix.diagonal (fun x : ι → n => ∏ i, a (x i)) *ᵥ WithLp.ofLp v) x = _
  exact Matrix.mulVec_diagonal _ _ _

end SpinAngle.TensorRep

namespace SpinAngle.Specht
open scoped Classical
variable {G : Type*} [contextInstance243_21 : Group G]
namespace PermutationSpace
open scoped Classical

variable {X : Type*} [contextInstance247_21 : Fintype X] [contextInstance247_33 : MulAction G X]

omit [Fintype X] in
@[simp] lemma rep_apply (g : G) (v : EuclideanSpace ℂ X) (x : X) :
    rep g v x = v (g⁻¹ • x) := rfl

variable {H : Type*} [contextInstance278_21 : Group H] [contextInstance278_31 : Fintype H]

omit [Fintype X] in
lemma alternator_coeff (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) (x : X) :
    alternator ι χ v x = ∑ h, χ h * v ((ι h)⁻¹ • x) := by
  simp [alternator_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype X] in
lemma polytabloid_base [DecidableEq X] (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hfree : ∀ h : H, ι h • b = b → h = 1) :
    alternator ι χ (EuclideanSpace.single b (1 : ℂ)) b = 1 := by
  classical
  rw [alternator_coeff, Finset.sum_eq_single 1]
  · simp
  · intro h _ hh
    have hn : (ι h)⁻¹ • b ≠ b := by
      intro he
      have hi : h⁻¹ = 1 := hfree h⁻¹ (by simpa using he)
      exact hh (inv_eq_one.mp hi)
    simp [hn]
  · simp

end PermutationSpace
variable {α : Type*} [contextInstance389_21 : Fintype α]

@[simp] lemma complexSign_conj (g : Equiv.Perm α) : conj (complexSign g) = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_swap (x y : α) (h : x ≠ y) : complexSign (Equiv.swap x y) = -1 := by
  simp [complexSign, Equiv.Perm.sign_swap h]

end SpinAngle.Specht

namespace SpinAngle.Young

lemma fin_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  have aux : ∀ k (hk : k < n), k ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hl := hf (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ from by simp)
      have hi := ih hk'
      omega
  exact aux i.val i.isLt

lemma card_column (D : YoungDiagram) (j : ℕ) :
    (Finset.univ.filter fun x : Cells D => x.val.2 = j).card = D.colLen j := by
  classical
  let e : {x : Cells D // x.val.2 = j} ≃ Fin (D.colLen j) := {
    toFun := fun x => ⟨x.val.val.1, YoungDiagram.mem_iff_lt_colLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun i => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.symm
    right_inv := by intro i; rfl }
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem column_sort_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, x.val.1 ≤ r (σ x) := by
  classical
  let S (j : ℕ) : Finset ℕ := (Finset.univ.filter fun x : Cells D => x.val.2 = j).image r
  have hc (j : ℕ) : (S j).card = D.colLen j := by
    change ((Finset.univ.filter fun x : Cells D => x.val.2 = j).image r).card = _
    rw [Finset.card_image_iff.mpr (show Set.InjOn r ↑(Finset.univ.filter fun x : Cells D => x.val.2 = j) from by
      intro x hx y hy hxy
      exact hinj x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy)]
    exact card_column D j
  let F (j : ℕ) := (S j).orderEmbOfFin (hc j)
  have hpre (x : Cells D) : ∃ y : Cells D, y.val.2 = x.val.2 ∧
      r y = F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ := by
    have hm := (S x.val.2).orderEmbOfFin_mem (hc _) ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩
  choose f hcol hr using hpre
  have hf : Function.Injective f := by
    intro x y he
    have hj : x.val.2 = y.val.2 := (hcol x).symm.trans ((congrArg (fun z : Cells D => z.val.2) he).trans (hcol y))
    have hi : x.val.1 = y.val.1 := by
      have hval : F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ =
          F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ := by
        rw [← hr x, ← hr y, he]
      have hy : y.val.1 < D.colLen x.val.2 := by rw [hj]; exact YoungDiagram.mem_iff_lt_colLen.mp y.property
      have hid : F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ = F x.val.2 ⟨y.val.1, hy⟩ := by
        have aux (j k i : ℕ) (hk : j = k) (hi : i < D.colLen j) (hi' : i < D.colLen k) :
            F j ⟨i, hi⟩ = F k ⟨i, hi'⟩ := by subst k; rfl
        exact aux _ _ _ hj.symm _ _
      rw [hid] at hval
      exact congrArg Fin.val ((F x.val.2).injective hval)
    exact Subtype.ext (Prod.ext hi hj)
  let σ : Equiv.Perm (Cells D) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨σ, hcol, ?_⟩
  have hle (x : Cells D) : x.val.1 ≤ r (σ x) := by
    change x.val.1 ≤ r (f x)
    rw [hr]
    exact fin_le_strictMono _ (F x.val.2).strictMono ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
  exact hle

theorem column_sort (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    (hsum : ∑ x : Cells D, r x = ∑ x : Cells D, x.val.1) :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, r (σ x) = x.val.1 := by
  obtain ⟨σ, hc, hle⟩ := column_sort_le D r hinj
  refine ⟨σ, hc, ?_⟩
  have heq : ∑ x : Cells D, x.val.1 = ∑ x : Cells D, r (σ x) := by
    rw [Equiv.sum_comp σ r, hsum]
  have hh := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun x _ => hle x)).mp heq
  intro x
  exact (hh x (Finset.mem_univ x)).symm

end SpinAngle.Young

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι n : Type*} [contextInstance532_23 : Fintype ι] [contextInstance532_35 : DecidableEq ι] [contextInstance532_51 : Fintype n] [contextInstance532_63 : DecidableEq n]

lemma site_apply
    {ι : Type*} {n : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (g : Equiv.Perm ι) (v : EuclideanSpace ℂ (ι → n)) (x : ι → n) :
    PermutationSpace.rep g v x = v (x ∘ g) := rfl

variable (D : YoungDiagram) (q : ℕ)
variable (hq : D.colLen 0 ≤ q)

lemma rowColor_column_free
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q) (g : columnGroup D)
    (hg : g.val • rowColor D q hq = rowColor D q hq) : g = 1 := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrFun hg (g.val x)
    have hh' := congrArg Fin.val hh
    change (g.val x).val.1 = x.val.1
    change ((g.val x |> g.val.symm)).val.1 = (g.val x).val.1 at hh'
    simp only [Equiv.symm_apply_apply] at hh'
    exact hh'.symm
  · exact g.property x

lemma highest_base : highest D q hq (rowColor D q hq) = 1 := by
  classical
  unfold highest
  exact PermutationSpace.polytabloid_base (columnGroup D).subtype
    (complexSign.comp (columnGroup D).subtype) (rowColor D q hq)
    (rowColor_column_free (ι := Cells D) D q hq)

lemma highest_ne_zero : highest D q hq ≠ 0 := by
  intro he
  have hh := congrArg (fun v : TensorSpace D q => v (rowColor D q hq)) he
  simp [highest_base] at hh

end SpinAngle.PolynomialCarrier

namespace SpinAngle.Specht.PermutationSpace
open scoped Classical
variable {G H X : Type*} [contextInstance635_25 : Group G] [contextInstance635_35 : Group H] [contextInstance635_45 : Fintype H] [contextInstance635_57 : Fintype X] [contextInstance635_69 : MulAction G X]
end SpinAngle.Specht.PermutationSpace

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma alternating_collision (v : TensorSpace D q) (hv : v ∈ alternating D q)
    (x : Cells D → Fin q) (i j : Cells D) (hij : i ≠ j)
    (hc : i.val.2 = j.val.2) (hx : x i = x j) : v x = 0 := by
  classical
  let : DecidableEq (Cells D) := Classical.decEq _
  let g : columnGroup D := ⟨Equiv.swap i j, by
    intro k
    by_cases hki : k = i
    · subst k; simp [hc]
    by_cases hkj : k = j
    · subst k; simp [hc]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]⟩
  have hperm : x ∘ (g : Equiv.Perm (Cells D)) = x := by
    funext k
    change x (Equiv.swap i j k) = x k
    by_cases hki : k = i
    · subst k; simp [hx]
    by_cases hkj : k = j
    · subst k; simp [hx]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := congrArg (fun w : TensorSpace D q => w x) (hv g)
  simp only [site_apply, hperm, PiLp.smul_apply, smul_eq_mul] at hh
  have hg : complexSign g.val = -1 := by
    simpa only [g] using complexSign_swap i j hij
  rw [hg, neg_one_mul] at hh
  linear_combination (1/2 : ℂ) * hh

lemma alternating_injective (v : TensorSpace D q) (hv : v ∈ alternating D q)
    (x : Cells D → Fin q) (hx : v x ≠ 0) :
    ∀ i j : Cells D, i.val.2 = j.val.2 → (x i).val = (x j).val → i = j := by
  intro i j hc he
  by_contra hij
  exact hx (alternating_collision D q v hv x i j hij hc (Fin.ext he))

lemma alternating_minimal_weight (v : TensorSpace D q) (hv : v ∈ alternating D q)
    (x : Cells D → Fin q) (hw : ∑ i, (x i).val = ∑ i : Cells D, i.val.1) :
    v x = v (rowColor D q hq) * highest D q hq x := by
  by_cases hx : v x = 0
  · by_cases he : highest D q hq x = 0
    · rw [hx, he, mul_zero]
    · obtain ⟨σ, hc, hr⟩ := column_sort D (fun i => (x i).val)
        (alternating_injective D q (highest D q hq) (highest_mem D q hq) x he) hw
      let g : columnGroup D := ⟨σ, hc⟩
      have hcolor : x ∘ σ = rowColor D q hq := by funext i; exact Fin.ext (hr i)
      have hh := congrArg (fun w : TensorSpace D q => w x) (hv g)
      simp only [site_apply, PiLp.smul_apply, smul_eq_mul] at hh
      change v (x ∘ σ) = complexSign σ * v x at hh
      rw [hcolor, hx, mul_zero] at hh
      rw [hx, hh, zero_mul]
  · obtain ⟨σ, hc, hr⟩ := column_sort D (fun i => (x i).val)
      (alternating_injective D q v hv x hx) hw
    let g : columnGroup D := ⟨σ, hc⟩
    have hcolor : x ∘ σ = rowColor D q hq := by funext i; exact Fin.ext (hr i)
    have hh := congrArg (fun w : TensorSpace D q => w x) (hv g)
    have he := congrArg (fun w : TensorSpace D q => w x) (highest_mem D q hq g)
    simp only [site_apply, PiLp.smul_apply, smul_eq_mul] at hh he
    change v (x ∘ σ) = complexSign σ * v x at hh
    change highest D q hq (x ∘ σ) = complexSign σ * highest D q hq x at he
    rw [hcolor] at hh he
    rw [highest_base] at he
    rw [hh]
    calc
      v x = v x * 1 := (mul_one _).symm
      _ = v x * (complexSign σ * highest D q hq x) := by rw [← he]
      _ = complexSign σ * v x * highest D q hq x := by ring

end SpinAngle.PolynomialCarrier

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι : Type*} [contextInstance741_21 : Fintype ι] [contextInstance741_33 : DecidableEq ι] {q : ℕ}

lemma diagonal_single (a : Fin q → ℂ) (b : ι → Fin q) :
    TensorRep.action (Matrix.diagonal a) (EuclideanSpace.single b (1 : ℂ)) =
      (∏ i, a (b i)) • EuclideanSpace.single b (1 : ℂ) := by
  ext x
  rw [TensorRep.action_diagonal]
  simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : x = b
  · subst x; rfl
  · simp [h]

lemma diagonal_unitary {z : ℂ} (hz : star z * z = 1) :
    Matrix.diagonal (fun i : Fin q => z ^ i.val) ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  have hd : star (Matrix.diagonal (fun i : Fin q => z ^ i.val)) =
      Matrix.diagonal (fun i : Fin q => star (z ^ i.val)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.star_apply]
    · simp [Matrix.star_apply, h, Ne.symm h]
  rw [Matrix.mem_unitaryGroup_iff', hd, Matrix.diagonal_mul_diagonal]
  simp only [star_pow, ← mul_pow, hz, one_pow]
  exact Matrix.diagonal_one

variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

def weightOrder : ℕ := Fintype.card (Cells D) * q + 1

def weightRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / weightOrder D q)

lemma weightRoot_primitive : IsPrimitiveRoot (weightRoot D q) (weightOrder D q) :=
  Complex.isPrimitiveRoot_exp _ (by unfold weightOrder; omega)

lemma weightRoot_unitary : star (weightRoot D q) * weightRoot D q = 1 := by
  have hn := Complex.norm_eq_one_of_pow_eq_one
    (weightRoot_primitive D q).pow_eq_one (show weightOrder D q ≠ 0 by unfold weightOrder; omega)
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  norm_num

def weightElement : Matrix.unitaryGroup (Fin q) ℂ :=
  ⟨Matrix.diagonal (fun i => weightRoot D q ^ i.val), diagonal_unitary (weightRoot_unitary D q)⟩

lemma weight_sum_lt (x : Cells D → Fin q) : ∑ i, (x i).val < weightOrder D q := by
  have hh : (∑ i, (x i).val) ≤ ∑ _i : Cells D, q :=
    Finset.sum_le_sum fun i _ => (x i).isLt.le
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
  unfold weightOrder
  omega

lemma weight_action (v : TensorSpace D q) (x : Cells D → Fin q) :
    TensorRep.rep (weightElement D q) v x = weightRoot D q ^ (∑ i, (x i).val) * v x := by
  change TensorRep.action (Matrix.diagonal (fun i : Fin q => weightRoot D q ^ i.val)) v x = _
  rw [TensorRep.action_diagonal, Finset.prod_pow_eq_pow_sum]

lemma highest_diagonal (a : Fin q → ℂ) :
    TensorRep.action (Matrix.diagonal a) (highest D q hq) =
      (∏ i, a (rowColor D q hq i)) • highest D q hq := by
  unfold highest
  rw [PermutationSpace.alternator_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [map_smul, action_site_commute, diagonal_single, map_smul]
  exact smul_comm _ _ _

lemma highest_weight_eigen :
    TensorRep.rep (weightElement D q) (highest D q hq) =
      weightRoot D q ^ (∑ i : Cells D, i.val.1) • highest D q hq := by
  change TensorRep.action (Matrix.diagonal _) _ = _
  rw [highest_diagonal]
  congr 1
  exact Finset.prod_pow_eq_pow_sum _ _ _

include hq in
lemma weight_eigen_support (v : TensorSpace D q)
    (hv : TensorRep.rep (weightElement D q) v =
      weightRoot D q ^ (∑ i : Cells D, i.val.1) • v)
    (x : Cells D → Fin q) (hx : v x ≠ 0) :
    ∑ i, (x i).val = ∑ i : Cells D, i.val.1 := by
  have hh := congrArg (fun w : TensorSpace D q => w x) hv
  rw [weight_action] at hh
  simp only [PiLp.smul_apply, smul_eq_mul] at hh
  have hp := mul_right_cancel₀ hx hh
  apply (weightRoot_primitive D q).pow_inj (weight_sum_lt D q x) _ hp
  exact weight_sum_lt D q (rowColor D q hq)

theorem weight_eigenspace_one_dimensional (v : TensorSpace D q)
    (hv : v ∈ alternating D q)
    (heig : TensorRep.rep (weightElement D q) v =
      weightRoot D q ^ (∑ i : Cells D, i.val.1) • v) :
    v = v (rowColor D q hq) • highest D q hq := by
  ext x
  change v x = v (rowColor D q hq) * highest D q hq x
  by_cases hw : ∑ i, (x i).val = ∑ i : Cells D, i.val.1
  · exact alternating_minimal_weight D q hq v hv x hw
  · have hv0 : v x = 0 := by
      by_contra hn
      exact hw (weight_eigen_support D q hq v heig x hn)
    have he0 : highest D q hq x = 0 := by
      by_contra hn
      exact hw (weight_eigen_support D q hq _ (highest_weight_eigen D q hq) x hn)
    rw [hv0, he0, mul_zero]

theorem ordinary_irreducible : Representation.IsIrreducible (ordinary D q hq).toRepresentation := by
  refine cyclic_irreducible_of_simple_eigen _ _ ?_ ?_ (weightElement D q)
    (weightRoot D q ^ (∑ i : Cells D, i.val.1)) ?_ ?_
  · intro he
    exact highest_ne_zero D q hq (congrArg Subtype.val he)
  · intro g x y
    exact TensorRep.rep_unitary g (x : TensorSpace D q) (y : TensorSpace D q)
  · exact Subtype.ext (highest_weight_eigen D q hq)
  · intro v hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v.val (rowColor D q hq), ?_⟩
    apply Subtype.ext
    exact (weight_eigenspace_one_dimensional D q hq v.val v.property (congrArg Subtype.val hv)).symm

end SpinAngle.PolynomialCarrier

namespace SpinAngle.TensorRep
open scoped Classical
variable {ι κ n : Type*} [contextInstance868_25 : Fintype ι] [contextInstance868_37 : DecidableEq ι] [contextInstance868_53 : Fintype κ] [contextInstance868_65 : DecidableEq κ]
  [contextInstance869_2 : Fintype n] [contextInstance869_14 : DecidableEq n]

lemma diagonal_unitary_of_star_mul (a : n → ℂ) (ha : ∀ i, star (a i) * a i = 1) :
    Matrix.diagonal a ∈ Matrix.unitaryGroup n ℂ := by
  have hd : star (Matrix.diagonal a) = Matrix.diagonal (fun i => star (a i)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.star_apply]
    · simp [Matrix.star_apply, h, Ne.symm h]
  rw [Matrix.mem_unitaryGroup_iff', hd, Matrix.diagonal_mul_diagonal]
  simp only [ha]
  exact Matrix.diagonal_one

lemma diagonal_single [DecidableEq (ι → n)] (a : n → ℂ) (b : ι → n) :
    action (Matrix.diagonal a) (EuclideanSpace.single b (1 : ℂ)) =
      (∏ i, a (b i)) • EuclideanSpace.single b (1 : ℂ) := by
  ext x
  rw [action_diagonal]
  simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : x = b
  · subst x; rfl
  · simp [h]

def content (x : ι → n) (j : n) : ℕ := (Finset.univ.filter fun i => x i = j).card

lemma product_content
    {ι : Type*} {n : Type*}
    [contextInstance868_25 : Fintype ι]
    [DecidableEq ι]
    [contextInstance869_2 : Fintype n]
    [contextInstance869_14 : DecidableEq n] (a : n → ℂ) (x : ι → n) :
    ∏ i, a (x i) = ∏ j, a j ^ content x j := by
  rw [← Finset.prod_fiberwise' Finset.univ x a]
  simp only [Finset.prod_const, content]

lemma phase_product
    {ι : Type*} {n : Type*}
    [contextInstance868_25 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance869_14 : DecidableEq n] (z : ℂ) (j : n) (x : ι → n) :
    ∏ i, (if x i = j then z else 1) = z ^ content x j := by
  rw [← Finset.prod_filter]
  simp [content]

lemma content_le_card
    {ι : Type*} {n : Type*}
    [contextInstance868_25 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [contextInstance869_14 : DecidableEq n] (x : ι → n) (j : n) : content x j ≤ Fintype.card ι :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma intertwiner_content_zero
    (L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (κ → n))
    (hL : ∀ (g : Matrix.unitaryGroup n ℂ) v, L (rep g v) = rep g (L v))
    (x : ι → n) (y : κ → n) (j : n) (hxy : content x j ≠ content y j) :
    L (EuclideanSpace.single x (1 : ℂ)) y = 0 := by
  let N := Fintype.card ι + Fintype.card κ + 1
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hz : IsPrimitiveRoot z N := Complex.isPrimitiveRoot_exp _ (by dsimp [N]; omega)
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one (by dsimp [N]; omega)
  have hzu : star z * z = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]
    norm_num
  let g : Matrix.unitaryGroup n ℂ := ⟨Matrix.diagonal (fun k => if k = j then z else 1),
    diagonal_unitary_of_star_mul _ (fun k => by split_ifs; exact hzu; simp)⟩
  have hh := congrArg (fun v : EuclideanSpace ℂ (κ → n) => v y)
    (hL g (EuclideanSpace.single x (1 : ℂ)))
  change L (action (Matrix.diagonal _) _) y = action (Matrix.diagonal _) _ y at hh
  rw [diagonal_single, map_smul, action_diagonal] at hh
  simp only [PiLp.smul_apply, smul_eq_mul, phase_product] at hh
  by_contra hn
  apply hxy
  exact hz.pow_inj (by have := content_le_card x j; dsimp [N]; omega)
    (by have := content_le_card y j; dsimp [N]; omega) (mul_right_cancel₀ hn hh)

lemma intertwiner_diagonal
    (L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (κ → n))
    (hL : ∀ (g : Matrix.unitaryGroup n ℂ) v, L (rep g v) = rep g (L v))
    (a : n → ℂ) (v : EuclideanSpace ℂ (ι → n)) :
    L (action (Matrix.diagonal a) v) = action (Matrix.diagonal a) (L v) := by
  have hsingle (x : ι → n) :
      L (action (Matrix.diagonal a) (EuclideanSpace.single x (1 : ℂ))) =
        action (Matrix.diagonal a) (L (EuclideanSpace.single x (1 : ℂ))) := by
    ext y
    rw [diagonal_single, map_smul, action_diagonal]
    simp only [PiLp.smul_apply, smul_eq_mul]
    by_cases he : ∀ j, content x j = content y j
    · rw [product_content a x, product_content a y]
      congr 1
      exact Finset.prod_congr rfl fun j _ => congrArg (fun k => a j ^ k) (he j)
    · push Not at he
      obtain ⟨j, hj⟩ := he
      rw [intertwiner_content_zero L hL x y j hj, mul_zero, mul_zero]
  have hexp := (EuclideanSpace.basisFun (ι → n) ℂ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
  rw [← hexp, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul, map_smul, map_smul, map_smul, hsingle]

lemma intertwiner_hermitian
    (L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (κ → n))
    (hL : ∀ (g : Matrix.unitaryGroup n ℂ) v, L (rep g v) = rep g (L v))
    (a : Matrix n n ℂ) (ha : a.IsHermitian) (v : EuclideanSpace ℂ (ι → n)) :
    L (action a v) = action a (L v) := by
  rw [ha.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, map_mul, Module.End.mul_apply]
  change L (rep ha.eigenvectorUnitary (action (Matrix.diagonal _) (rep (star ha.eigenvectorUnitary) v))) = _
  rw [hL, intertwiner_diagonal L hL, hL]
  rfl

end SpinAngle.TensorRep

namespace SpinAngle.TensorRep
open SpinAngle.Specht
variable {ι n : Type*} [contextInstance980_23 : Fintype ι] [contextInstance980_35 : DecidableEq ι] [contextInstance980_51 : Fintype n] [contextInstance980_63 : DecidableEq n]

lemma apply_mem_hermitian (U : Subrepresentation (rep (ι := ι) (n := n)))
    (a : Matrix n n ℂ) (ha : a.IsHermitian)
    (v : EuclideanSpace ℂ (ι → n)) (hv : v ∈ U) : action a v ∈ U := by
  let L : EuclideanSpace ℂ (ι → n) →ₗ[ℂ] EuclideanSpace ℂ (ι → n) :=
    U.toSubmodule.starProjection.toLinearMap
  have hu : ∀ (g : Matrix.unitaryGroup n ℂ) (x y : EuclideanSpace ℂ (ι → n)),
      ⟪rep g x, rep g y⟫_ℂ = ⟪x, y⟫_ℂ := rep_unitary
  have hL : ∀ (g : Matrix.unitaryGroup n ℂ) (w : EuclideanSpace ℂ (ι → n)),
      L (rep g w) = rep g (L w) := by
    intro g w
    exact starProjection_rep (rep (ι := ι) (n := n)) hu U g w
  have hlv : L v = v := U.toSubmodule.starProjection_eq_self_iff.mpr hv
  have hh := intertwiner_hermitian L hL a ha v
  rw [hlv] at hh
  rw [← hh]
  exact U.toSubmodule.starProjection_apply_mem _

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

def highestMonomial (t : Fin q → ℝ) : ℝ := ∏ i : Cells D, t (rowColor D q hq i)

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped Matrix ComplexOrder
namespace SpinAngle.SortedSpectrum
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)

def values : Fin q → ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues (by simp)

def basis : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q)) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis (by simp)

def changeBasis : Matrix.unitaryGroup (Fin q) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix (basis A hA).toBasis,
    (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary (basis A hA)⟩

@[simp] lemma changeBasis_apply (i j : Fin q) : changeBasis A hA i j = basis A hA j i := rfl

end SpinAngle.SortedSpectrum

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix InnerProductSpace
open SpinAngle.Specht SpinAngle.Young Module
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

def inclusion : Carrier D q hq →ₗᵢ[ℂ] TensorSpace D q :=
  (alternating D q).toSubmodule.subtypeₗᵢ.comp (ordinary D q hq).toSubmodule.subtypeₗᵢ

@[simp] lemma inclusion_apply (v : Carrier D q hq) : inclusion D q hq v = v.val.val := rfl

def image : Subrepresentation (TensorRep.rep (ι := Cells D) (n := Fin q)) where
  toSubmodule := LinearMap.range (inclusion D q hq).toLinearMap
  apply_mem_toSubmodule := by
    rintro g v ⟨x,rfl⟩
    exact ⟨(ordinary D q hq).toRepresentation g x,rfl⟩

lemma inclusion_image (v : Carrier D q hq) : inclusion D q hq v ∈ image D q hq := ⟨v,rfl⟩

def hermitianAction (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    Carrier D q hq →ₗ[ℂ] Carrier D q hq :=
  (LinearEquiv.ofInjective (inclusion D q hq).toLinearMap (inclusion D q hq).injective).symm.toLinearMap.comp
    ((TensorRep.action a).comp (inclusion D q hq).toLinearMap |>.codRestrict
      (image D q hq).toSubmodule (fun v => TensorRep.apply_mem_hermitian _ a ha _ (inclusion_image D q hq v)))

@[simp] lemma inclusion_hermitianAction (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian)
    (v : Carrier D q hq) :
    inclusion D q hq (hermitianAction D q hq a ha v) = TensorRep.action a (inclusion D q hq v) := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective (inclusion D q hq).toLinearMap
    (inclusion D q hq).injective).apply_symm_apply _)

lemma ordinary_rep_unitary (g : Matrix.unitaryGroup (Fin q) ℂ) (v w : Carrier D q hq) :
    ⟪(ordinary D q hq).toRepresentation g v, (ordinary D q hq).toRepresentation g w⟫_ℂ = ⟪v,w⟫_ℂ :=
  TensorRep.rep_unitary g v.val.val w.val.val

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace BigOperators
namespace SpinAngle.ExternalTensor
open Module
variable {E F : Type*} [contextInstance1195_23 : NormedAddCommGroup E] [contextInstance1195_46 : InnerProductSpace ℂ E]
  [contextInstance1196_2 : NormedAddCommGroup F] [contextInstance1196_25 : InnerProductSpace ℂ F]
  [contextInstance1197_2 : FiniteDimensional ℂ E] [contextInstance1197_26 : FiniteDimensional ℂ F]
variable {G H : Type*} [contextInstance1198_23 : Group G] [contextInstance1198_33 : Group H]

@[simp] lemma rep_tmul
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    {G : Type*} {H : Type*}
    [contextInstance1198_23 : Group G]
    [contextInstance1198_33 : Group H] (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (g : G × H) (x : E) (y : F) :
    rep ρ σ g (x ⊗ₜ[ℂ] y) = ρ g.1 x ⊗ₜ σ g.2 y := rfl

def rightSlice (β : Module.Dual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap.comp (TensorProduct.map LinearMap.id β)

def leftSlice (α : Module.Dual ℂ E) : E ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap.comp (TensorProduct.map α LinearMap.id)

@[simp] lemma rightSlice_tmul
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (β : Module.Dual ℂ F) (x : E) (y : F) :
    rightSlice β (x ⊗ₜ[ℂ] y) = β y • x := rfl
@[simp] lemma leftSlice_tmul
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (α : Module.Dual ℂ E) (x : E) (y : F) :
    leftSlice α (x ⊗ₜ[ℂ] y) = α x • y := rfl

lemma slice_commute
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (α : Module.Dual ℂ E) (β : Module.Dual ℂ F) (v : E ⊗[ℂ] F) :
    α (rightSlice β v) = β (leftSlice α v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

lemma slice_map_left
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (β : Module.Dual ℂ F) (A : E →ₗ[ℂ] E) (v : E ⊗[ℂ] F) :
    rightSlice β (TensorProduct.map A LinearMap.id v) = A (rightSlice β v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

lemma eq_sum_slices
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] {ι : Type*} [Fintype ι] (b : Basis ι ℂ F) (v : E ⊗[ℂ] F) :
    v = ∑ i, rightSlice (b.coord i) v ⊗ₜ[ℂ] b i := by
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [rightSlice_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sum, Basis.coord_apply, Basis.sum_repr]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, ← hx, ← hy]

lemma rightSlice_ext {v w : E ⊗[ℂ] F}
    (h : ∀ β : Module.Dual ℂ F, rightSlice β v = rightSlice β w) : v = w := by
  classical
  let b := Module.finBasis ℂ F
  rw [eq_sum_slices b v, eq_sum_slices b w]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun x : E => x ⊗ₜ[ℂ] b i) (h _)

lemma scalar_of_commute (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (A : E →ₗ[ℂ] E) (hA : ∀ g x, A (ρ g x) = ρ g (A x)) :
    ∃ z : ℂ, A = z • LinearMap.id := by
  let f := A.intertwiningMap_of_isIntertwiningMap ρ ρ hA
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective f
  refine ⟨z, ?_⟩
  ext x
  exact (congrArg (fun L : ρ.IntertwiningMap ρ => L x) hz).symm

lemma left_commutant (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (d : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)
    (hd : ∀ g v, d (TensorProduct.map (ρ g) LinearMap.id v) =
      TensorProduct.map (ρ g) LinearMap.id (d v)) :
    ∃ B : F →ₗ[ℂ] F, d = TensorProduct.map LinearMap.id B := by
  classical
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  obtain ⟨α, hα⟩ := Module.Projective.exists_dual_eq_one ℂ hx₀
  let B : F →ₗ[ℂ] F := (leftSlice α).comp (d.comp (TensorProduct.mk ℂ E F x₀))
  refine ⟨B, ?_⟩
  ext x y
  change d (x ⊗ₜ[ℂ] y) = TensorProduct.map LinearMap.id B (x ⊗ₜ[ℂ] y)
  apply rightSlice_ext
  intro β
  let A : E →ₗ[ℂ] E := (rightSlice β).comp (d.comp ((TensorProduct.mk ℂ E F).flip y))
  have hA (g : G) (v : E) : A (ρ g v) = ρ g (A v) := by
    change rightSlice β (d (ρ g v ⊗ₜ[ℂ] y)) = ρ g (rightSlice β (d (v ⊗ₜ[ℂ] y)))
    rw [← slice_map_left, ← hd]
    rfl
  obtain ⟨z,hz⟩ := scalar_of_commute ρ A hA
  have hzv (v : E) : rightSlice β (d (v ⊗ₜ[ℂ] y)) = z • v :=
    congrArg (fun f : E →ₗ[ℂ] E => f v) hz
  have hzB : β (B y) = z := by
    change β (leftSlice α (d (x₀ ⊗ₜ[ℂ] y))) = z
    rw [← slice_commute, hzv, map_smul, hα, smul_eq_mul, mul_one]
  change rightSlice β (d (x ⊗ₜ[ℂ] y)) = β (B y) • x
  rw [hzv, hzB]

lemma commutant_scalar (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (d : (rep ρ σ).IntertwiningMap (rep ρ σ)) :
    ∃ z : ℂ, d.toLinearMap = z • LinearMap.id := by
  obtain ⟨B,hB⟩ := left_commutant ρ d.toLinearMap (by
    intro g v
    simpa [rep, Representation.tprod_apply, Module.End.one_eq_id] using Representation.IntertwiningMap.isIntertwining _ _ d (g,1) v)
  have hσ (h : H) (y : F) : B (σ h y) = σ h (B y) := by
    let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    obtain ⟨x,hx⟩ := exists_ne (0 : E)
    obtain ⟨α,hα⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    have hh := Representation.IntertwiningMap.isIntertwining _ _ d (1,h) (x ⊗ₜ[ℂ] y)
    change d.toLinearMap (rep ρ σ (1,h) (x ⊗ₜ y)) =
      rep ρ σ (1,h) (d.toLinearMap (x ⊗ₜ y)) at hh
    rw [hB] at hh
    simp only [rep_tmul, map_one, Module.End.one_apply, TensorProduct.map_tmul,
      LinearMap.id_apply] at hh
    have := congrArg (leftSlice α) hh
    simpa [hα] using this
  obtain ⟨z,hz⟩ := scalar_of_commute σ B hσ
  refine ⟨z, ?_⟩
  rw [hB, hz]
  ext x y
  simp

lemma unitary
    {E : Type*} {F : Type*}
    [contextInstance1195_23 : NormedAddCommGroup E]
    [contextInstance1195_46 : InnerProductSpace ℂ E]
    [contextInstance1196_2 : NormedAddCommGroup F]
    [contextInstance1196_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    {G : Type*} {H : Type*}
    [contextInstance1198_23 : Group G]
    [contextInstance1198_33 : Group H] (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (hσ : ∀ h x y, ⟪σ h x, σ h y⟫_ℂ = ⟪x,y⟫_ℂ)
    (g : G × H) (v w : E ⊗[ℂ] F) :
    ⟪rep ρ σ g v, rep ρ σ g w⟫_ℂ = ⟪v,w⟫_ℂ := by
  let a : E →ₗᵢ[ℂ] E := (ρ g.1).isometryOfInner (hρ g.1)
  let b : F →ₗᵢ[ℂ] F := (σ g.2).isometryOfInner (hσ g.2)
  exact TensorProduct.inner_map_map a b v w

lemma projection_commute (τ : Representation ℂ G E)
    (hτ : ∀ g x y, ⟪τ g x, τ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (U : Subrepresentation τ) (g : G) (v : E) :
    U.toSubmodule.starProjection (τ g v) = τ g (U.toSubmodule.starProjection v) := by
  apply U.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact U.apply_mem_toSubmodule g (U.toSubmodule.starProjection_apply_mem v)
  · intro w hw
    have hw' := U.apply_mem_toSubmodule g⁻¹ hw
    have he : τ g (τ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← map_sub]
    conv_lhs => rhs; rw [← he]
    rw [hτ]
    exact U.toSubmodule.starProjection_inner_eq_zero v _ hw'

theorem irreducible (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hρ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (hσ : ∀ h x y, ⟪σ h x, σ h y⟫_ℂ = ⟪x,y⟫_ℂ) :
    (rep ρ σ).IsIrreducible := by
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let : Nontrivial F := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) σ.asModule
  obtain ⟨x,hx⟩ := exists_ne (0 : E)
  obtain ⟨y,hy⟩ := exists_ne (0 : F)
  have hxy : x ⊗ₜ[ℂ] y ≠ 0 := by
    intro h
    have := congrArg norm h
    simp only [TensorProduct.norm_tmul, norm_zero] at this
    exact (mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)) this
  have htb : (⊤ : Subrepresentation (rep ρ σ)) ≠ ⊥ := by
    intro h
    have hh : x ⊗ₜ[ℂ] y ∈ (⊤ : Subrepresentation (rep ρ σ)) := by trivial
    rw [h] at hh
    exact hxy hh
  let : Nontrivial (Subrepresentation (rep ρ σ)) := ⟨⟨⊤,⊥,htb⟩⟩
  refine ⟨fun U => ?_⟩
  let d : (rep ρ σ).IntertwiningMap (rep ρ σ) :=
    U.toSubmodule.starProjection.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (projection_commute _ (unitary ρ σ hρ hσ) U)
  obtain ⟨z,hz⟩ := commutant_scalar ρ σ d
  have hproj (v : E ⊗[ℂ] F) : U.toSubmodule.starProjection v = z • v :=
    congrArg (fun f : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F => f v) hz
  by_cases hz0 : z = 0
  · left
    apply bot_unique
    intro v hv
    change v = 0
    have hh := hproj v
    rw [U.toSubmodule.starProjection_eq_self_iff.mpr hv, hz0, zero_smul] at hh
    exact hh
  · right
    apply top_unique
    intro v _
    have hv := U.toSubmodule.starProjection_apply_mem (z⁻¹ • v)
    rw [hproj, smul_smul, mul_inv_cancel₀ hz0, one_smul] at hv
    exact hv

end SpinAngle.ExternalTensor

noncomputable section
open scoped BigOperators ComplexConjugate
namespace SpinAngle.TorusNaturality
open Module
variable {n X Y E F : Type*} [contextInstance1400_29 : Fintype n] [contextInstance1400_41 : Fintype X] [contextInstance1400_53 : Fintype Y]
  [contextInstance1401_2 : AddCommGroup E] [contextInstance1401_19 : Module ℂ E] [contextInstance1401_32 : AddCommGroup F] [contextInstance1401_49 : Module ℂ F]
variable (b : Basis X ℂ E) (c : Basis Y ℂ F)
  (w : X → n → ℕ) (v : Y → n → ℕ)
  (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
  (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
  (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y)

end SpinAngle.TorusNaturality

namespace SpinAngle.SignedTensor
open scoped Classical Matrix TensorProduct InnerProductSpace
open Module
variable {q : ℕ}
variable {ι κ τ : Type*} [contextInstance1517_25 : Fintype ι] [contextInstance1517_37 : DecidableEq ι] [contextInstance1517_53 : Fintype κ] [contextInstance1517_65 : DecidableEq κ]
  [contextInstance1518_2 : Fintype τ] [contextInstance1518_14 : DecidableEq τ]

abbrev PairRaw := EuclideanSpace ℂ (ι → Fin q) ⊗[ℂ] EuclideanSpace ℂ (κ → Fin q)

def pairRep : Representation ℂ (Group q) (PairRaw (q := q) (ι := ι) (κ := κ)) :=
  ExternalTensor.rep TensorRep.rep TensorRep.rep

def pairAction : (Mat q × Mat q) →* Module.End ℂ (PairRaw (q := q) (ι := ι) (κ := κ)) where
  toFun a := TensorProduct.map (TensorRep.action a.1) (TensorRep.action a.2)
  map_one' := by
    ext x y
    change TensorProduct.map _ _ (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] y
    simp only [Prod.fst_one, Prod.snd_one, map_one, TensorProduct.map_tmul,
      Module.End.one_apply]
  map_mul' a b := by
    ext x y
    change TensorProduct.map _ _ (x ⊗ₜ[ℂ] y) =
      TensorProduct.map _ _ (TensorProduct.map _ _ (x ⊗ₜ[ℂ] y))
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, TensorProduct.map_tmul,
      Module.End.mul_apply]

@[simp] lemma pairAction_tmul (a : Mat q × Mat q)
    (x : EuclideanSpace ℂ (ι → Fin q)) (y : EuclideanSpace ℂ (κ → Fin q)) :
    pairAction a (x ⊗ₜ[ℂ] y) = TensorRep.action a.1 x ⊗ₜ TensorRep.action a.2 y := rfl

def pairBasis : OrthonormalBasis ((ι → Fin q) × (κ → Fin q)) ℂ (PairRaw (q := q) (ι := ι) (κ := κ)) :=
  (EuclideanSpace.basisFun _ ℂ).tensorProduct (EuclideanSpace.basisFun _ ℂ)

def pairContent (x : (ι → Fin q) × (κ → Fin q)) (j : Spin q) : ℕ :=
  cond j.2 (TensorRep.content x.2 j.1) (TensorRep.content x.1 j.1)

def diagPair (a : Spin q → ℂ) : Mat q × Mat q :=
  (Matrix.diagonal (fun j => a (j,false)), Matrix.diagonal (fun j => a (j,true)))

end SpinAngle.SignedTensor

noncomputable section
open scoped InnerProductSpace
namespace SpinAngle.UnitaryNaturality
variable {G : Type*} [contextInstance1640_21 : Group G]
variable {E F : Type*} [contextInstance1641_23 : NormedAddCommGroup E] [contextInstance1641_46 : InnerProductSpace ℂ E]
  [contextInstance1642_2 : NormedAddCommGroup F] [contextInstance1642_25 : InnerProductSpace ℂ F]
  [contextInstance1643_2 : FiniteDimensional ℂ E] [contextInstance1643_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
  (hσ : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

instance irreducible : (rep a b q ha hb).IsIrreducible := by
  let := ordinary_irreducible a q ha
  let := ordinary_irreducible b q hb
  exact ExternalTensor.irreducible _ _ (ordinary_rep_unitary a q ha) (ordinary_rep_unitary b q hb)

def inclusion : Carrier a b q ha hb →ₗᵢ[ℂ]
    PairRaw (q := q) (ι := Cells a) (κ := Cells b) :=
  TensorProduct.mapIsometry (E := PolynomialCarrier.Carrier a q ha) (F := PolynomialCarrier.Carrier b q hb)
    (PolynomialCarrier.inclusion a q ha) (PolynomialCarrier.inclusion b q hb)

def hermitianAction (A : Mat q × Mat q) (hA : A.1.IsHermitian) (hB : A.2.IsHermitian) :
    Carrier a b q ha hb →ₗ[ℂ] Carrier a b q ha hb :=
  TensorProduct.map (PolynomialCarrier.hermitianAction a q ha A.1 hA)
    (PolynomialCarrier.hermitianAction b q hb A.2 hB)

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)
end SpinAngle.PolynomialCarrier

namespace SpinAngle.ExternalTensor
open scoped TensorProduct
variable {G H : Type*} [contextInstance1802_23 : Group G] [contextInstance1802_33 : Group H] [contextInstance1802_43 : TopologicalSpace G] [contextInstance1802_64 : TopologicalSpace H]
variable {E F : Type*} [contextInstance1803_23 : NormedAddCommGroup E] [contextInstance1803_46 : InnerProductSpace ℂ E]
  [contextInstance1804_2 : NormedAddCommGroup F] [contextInstance1804_25 : InnerProductSpace ℂ F]
  [contextInstance1805_2 : FiniteDimensional ℂ E] [contextInstance1805_26 : FiniteDimensional ℂ F]
end SpinAngle.ExternalTensor

namespace SpinAngle.SignedTensor
variable {q : ℕ} {τ : Type*} [contextInstance1828_29 : Fintype τ] [contextInstance1828_41 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance1859_23 : Fintype ι] [contextInstance1859_35 : DecidableEq ι] [contextInstance1859_51 : Fintype n] [contextInstance1859_63 : DecidableEq n]
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical InnerProductSpace
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

def highestVector : Carrier D q hq :=
  ⟨⟨highest D q hq,highest_mem D q hq⟩, self_mem_cyclic _ _⟩

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
namespace SpinAngle.TensorPositive
variable {E F : Type*} [contextInstance1947_23 : NormedAddCommGroup E] [contextInstance1947_46 : InnerProductSpace ℂ E]
  [contextInstance1948_2 : NormedAddCommGroup F] [contextInstance1948_25 : InnerProductSpace ℂ F]
  [contextInstance1949_2 : FiniteDimensional ℂ E] [contextInstance1949_26 : FiniteDimensional ℂ F]

end SpinAngle.TensorPositive

noncomputable section
open scoped BigOperators
namespace SpinAngle.EntropyMonomial
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

end SpinAngle.EntropyMonomial

noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators
namespace SpinAngle.PositiveTrace
variable {E : Type*} [contextInstance2090_21 : NormedAddCommGroup E] [contextInstance2090_44 : InnerProductSpace ℂ E]
  [contextInstance2091_2 : FiniteDimensional ℂ E]

end SpinAngle.PositiveTrace

noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
namespace SpinAngle.Isotypic
variable {G : Type*} [contextInstance2131_21 : Group G]
variable {E F : Type*} [contextInstance2132_23 : NormedAddCommGroup E] [contextInstance2132_46 : InnerProductSpace ℂ E]
  [contextInstance2133_2 : NormedAddCommGroup F] [contextInstance2133_25 : InnerProductSpace ℂ F]
  [contextInstance2134_2 : FiniteDimensional ℂ E] [contextInstance2134_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)

end SpinAngle.Isotypic

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

def IsEvenDensity (A : Mat q × Mat q) : Prop :=
  A.1.PosSemidef ∧ A.2.PosSemidef ∧ Matrix.trace A.1 + Matrix.trace A.2 = 1

lemma block_posSemidef (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef) :
    (block A).PosSemidef := by
  let R : Mat q × Mat q := (CFC.sqrt A.1, CFC.sqrt A.2)
  have he : block A = star (block R) * block R := by
    rw [← block_star, ← map_mul]
    congr 1
    apply Prod.ext
    · change A.1 = star (CFC.sqrt A.1) * CFC.sqrt A.1
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A.1)).star_eq,
        CFC.sqrt_mul_sqrt_self A.1 hA.nonneg]
    · change A.2 = star (CFC.sqrt A.2) * CFC.sqrt A.2
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A.2)).star_eq,
        CFC.sqrt_mul_sqrt_self A.2 hB.nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

end SpinAngle.SignedCarrier

namespace SpinAngle.EntropyMonomial
open scoped BigOperators
variable {ι : Type*} [contextInstance2379_21 : Fintype ι] [contextInstance2379_33 : Nonempty ι]

end SpinAngle.EntropyMonomial

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance2407_21 : Fintype τ] [contextInstance2407_33 : DecidableEq τ]

def highestVector : Carrier a b q ha hb :=
  PolynomialCarrier.highestVector a q ha ⊗ₜ[ℂ] PolynomialCarrier.highestVector b q hb

end SpinAngle.SignedCarrier

noncomputable section
open scoped BigOperators
namespace SpinAngle.DenseLU

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def border {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) : Mat (n+1) :=
  fun i => Fin.cases (Fin.cases a b) (fun i => Fin.cases (c i) (D i)) i

@[simp] lemma border_zero_zero {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) :
    border a b c D 0 0 = a := rfl
@[simp] lemma border_zero_succ {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) (j : Fin n) :
    border a b c D 0 j.succ = b j := rfl
@[simp] lemma border_succ_zero {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) (i : Fin n) :
    border a b c D i.succ 0 = c i := rfl
@[simp] lemma border_succ_succ {n : ℕ} (a : ℂ) (b c : Fin n → ℂ) (D : Mat n) (i j : Fin n) :
    border a b c D i.succ j.succ = D i j := rfl

def LowerUnipotent {n : ℕ} (L : Mat n) : Prop :=
  L.IsLowerTriangular ∧ ∀ i, L i i = 1

def bigCell (n : ℕ) : Set (Mat n) :=
  {A | ∃ L U, LowerUnipotent L ∧ U.IsUpperTriangular ∧ A = L * U}

end SpinAngle.DenseLU

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier
noncomputable section
open scoped BigOperators
namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable (σ : Type*) [contextInstance2689_21 : Fintype σ] [contextInstance2689_33 : DecidableEq σ] (p : ℕ)

def boundedExponentEquiv : {f : σ →₀ ℕ // ∀ i, f i ≤ p} ≃ (σ → Fin (p+1)) where
  toFun f i := ⟨f.val i, Nat.lt_succ_of_le (f.property i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val), by
    intro i; exact Nat.le_of_lt_succ (f i).isLt⟩
  left_inv f := by apply Subtype.ext; ext i; rfl
  right_inv f := by funext i; apply Fin.ext; rfl

abbrev LowerIndex (q : ℕ) := (i : Fin q) × Fin i.val

variable {q : ℕ}
def lowerEntry (i j : Fin q) : MvPolynomial (LowerIndex q) ℂ :=
  if h : j < i then X ⟨i, ⟨j.val, h⟩⟩ else if i = j then 1 else 0

lemma lowerEntry_degree (i j : Fin q) : (lowerEntry i j).totalDegree ≤ 1 := by
  unfold lowerEntry
  split_ifs <;> simp

lemma totalDegree_sum_le
    (σ : Type*)
    [Fintype σ]
    [DecidableEq σ]
    (p : ℕ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ p) : (∑ i ∈ s, f i).totalDegree ≤ p :=
  (MvPolynomial.totalDegree_finsetSum s f).trans (Finset.sup_le hf)

end SpinAngle.PolyDimension

namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable {σ X : Type*} [contextInstance2737_23 : Fintype σ] [contextInstance2737_35 : DecidableEq σ] [contextInstance2737_51 : Fintype X] (p : ℕ)

def valueTranspose (P : X → restrictDegree σ ℂ p) :
    Module.Dual ℂ (restrictDegree σ ℂ p) →ₗ[ℂ] EuclideanSpace ℂ X where
  toFun φ := WithLp.toLp 2 (fun x => φ (P x))
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

end SpinAngle.PolyDimension

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young PolyDimension MvPolynomial
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

def lowerCoordinate (x : Cells D → Fin q) : MvPolynomial (LowerIndex q) ℂ :=
  ∑ y : Cells D → Fin q, (∏ i : Cells D, lowerEntry (x i) (y i)) * C (highest D q hq y)

lemma lowerCoordinate_degree (x : Cells D → Fin q) :
    (lowerCoordinate D q hq x).totalDegree ≤ Fintype.card (Cells D) := by
  apply PolyDimension.totalDegree_sum_le
  intro y _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, add_zero]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun i _ => lowerEntry_degree (x i) (y i)).trans_eq (by simp)

def lowerCoordinateBounded (x : Cells D → Fin q) :
    restrictDegree (LowerIndex q) ℂ (Fintype.card (Cells D)) :=
  ⟨lowerCoordinate D q hq x,
    restrictTotalDegree_le_restrictDegree _ _ _
      ((mem_restrictTotalDegree _ _ _).mpr (lowerCoordinate_degree D q hq x))⟩

def lowerParameters (L : Matrix (Fin q) (Fin q) ℂ) (z : LowerIndex q) : ℂ :=
  L z.1 ⟨z.2.val, z.2.isLt.trans z.1.isLt⟩

end SpinAngle.PolynomialCarrier

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
namespace SpinAngle.CompactTwirl

variable {G : Type*} [contextInstance2861_21 : Group G] [contextInstance2861_31 : TopologicalSpace G] [contextInstance2861_52 : IsTopologicalGroup G]
  [contextInstance2862_2 : CompactSpace G] [contextInstance2862_19 : MeasurableSpace G] [contextInstance2862_39 : BorelSpace G]

def compactHaar : Measure G :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

instance : IsProbabilityMeasure (compactHaar (G := G)) where
  measure_univ := Measure.haarMeasure_self

instance : (compactHaar (G := G)).IsMulLeftInvariant :=
  inferInstanceAs (Measure.IsMulLeftInvariant (Measure.haarMeasure _))

variable {A : Type*} [contextInstance2877_21 : NormedRing A] [contextInstance2877_36 : NormedAlgebra ℝ A] [contextInstance2877_56 : CompleteSpace A]

def conjugate (ρ : G →* A) (a : A) (g : G) : A := ρ g * a * ρ g⁻¹

def twirl (ρ : G →* A) (a : A) : A := ∫ g, conjugate ρ a g ∂compactHaar

section Positivity
variable [contextInstance2919_9 : PartialOrder A] [contextInstance2919_26 : IsOrderedAddMonoid A] [contextInstance2919_49 : StarRing A] [contextInstance2919_62 : StarOrderedRing A]
  [contextInstance2920_2 : ClosedIciTopology A] [contextInstance2920_24 : IsOrderedModule ℝ A]

end Positivity

end SpinAngle.CompactTwirl

namespace SpinAngle
open scoped Matrix.Norms.L2Operator

lemma unitaryGroup_compactSpace (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    CompactSpace (Matrix.unitaryGroup n ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset isClosed_unitary
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_coe_unitary (⟨a, ha⟩ : unitary (Matrix n n ℂ))).le

end SpinAngle

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance2949_21 : Group G] [contextInstance2949_31 : TopologicalSpace G] [contextInstance2949_52 : IsTopologicalGroup G]
  [contextInstance2950_2 : CompactSpace G] [contextInstance2950_19 : MeasurableSpace G] [contextInstance2950_39 : BorelSpace G]
variable {E : Type*} [contextInstance2951_21 : NormedAddCommGroup E] [contextInstance2951_44 : InnerProductSpace ℂ E]
  [contextInstance2952_2 : FiniteDimensional ℂ E]

def continuousAction (ρ : Representation ℂ G E) : G →* (E →L[ℂ] E) :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).toMonoidHom.comp ρ

@[simp] lemma continuousAction_apply
    {G : Type*}
    [contextInstance2949_21 : Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance2951_21 : NormedAddCommGroup E]
    [contextInstance2951_44 : InnerProductSpace ℂ E]
    [contextInstance2952_2 : FiniteDimensional ℂ E] (ρ : Representation ℂ G E) (g : G) (v : E) :
    continuousAction ρ g v = ρ g v := rfl

def operatorTrace : (E →L[ℂ] E) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ E).comp
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm.toLinearMap).toContinuousLinearMap

@[simp] lemma operatorTrace_apply
    {G : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance2951_21 : NormedAddCommGroup E]
    [contextInstance2951_44 : InnerProductSpace ℂ E]
    [contextInstance2952_2 : FiniteDimensional ℂ E] (a : E →L[ℂ] E) :
    operatorTrace a = LinearMap.trace ℂ E a.toLinearMap := rfl

end SpinAngle.CompactTwirl

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3008_21 : Group G] [contextInstance3008_31 : TopologicalSpace G] [contextInstance3008_52 : IsTopologicalGroup G]
  [contextInstance3009_2 : CompactSpace G] [contextInstance3009_19 : MeasurableSpace G] [contextInstance3009_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3010_23 : NormedAddCommGroup E] [contextInstance3010_46 : InnerProductSpace ℂ E]
  [contextInstance3011_2 : NormedAddCommGroup F] [contextInstance3011_25 : InnerProductSpace ℂ F]
  [contextInstance3012_2 : FiniteDimensional ℂ E] [contextInstance3012_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3043_21 : CStarAlgebra A] [contextInstance3043_38 : PartialOrder A] [contextInstance3043_55 : StarOrderedRing A]
  [contextInstance3044_2 : NonnegSpectrumClass ℝ A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3062_21 : Group G] [contextInstance3062_31 : TopologicalSpace G] [contextInstance3062_52 : IsTopologicalGroup G]
  [contextInstance3063_2 : CompactSpace G] [contextInstance3063_19 : MeasurableSpace G] [contextInstance3063_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3064_23 : NormedAddCommGroup E] [contextInstance3064_46 : InnerProductSpace ℂ E]
  [contextInstance3065_2 : NormedAddCommGroup F] [contextInstance3065_25 : InnerProductSpace ℂ F]
  [contextInstance3066_2 : FiniteDimensional ℂ E] [contextInstance3066_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

noncomputable section
open scoped BigOperators
open Set
namespace SpinAngle.CompactMixture
variable {E : Type*} [contextInstance3119_21 : NormedAddCommGroup E] [contextInstance3119_44 : NormedSpace ℝ E] [contextInstance3119_62 : FiniteDimensional ℝ E]

end SpinAngle.CompactMixture

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance3168_21 : Group G] [contextInstance3168_31 : TopologicalSpace G] [contextInstance3168_52 : IsTopologicalGroup G]
  [contextInstance3169_2 : CompactSpace G] [contextInstance3169_19 : MeasurableSpace G] [contextInstance3169_39 : BorelSpace G]
variable {E : Type*} [contextInstance3170_21 : NormedAddCommGroup E] [contextInstance3170_44 : InnerProductSpace ℂ E]
  [contextInstance3171_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

def conjugateDensity (g : Group q) (A : Mat q × Mat q) : Mat q × Mat q :=
  (g.1.val * A.1 * star g.1.val, g.2.val * A.2 * star g.2.val)

variable {τ : Type*} [contextInstance3254_21 : Fintype τ] [contextInstance3254_33 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
instance groupMeasurableSpace : MeasurableSpace (Group q) := borel _
instance groupBorelSpace : BorelSpace (Group q) := ⟨rfl⟩
variable [contextInstance3273_9 : Nonempty (Fin q)]
instance groupCompactSpace : CompactSpace (Group q) := by
  let := unitaryGroup_compactSpace (Fin q)
  infer_instance
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3283_21 : Fintype τ] [contextInstance3283_33 : DecidableEq τ]

variable [contextInstance3288_9 : Nonempty (Fin q)]
end SpinAngle.SignedCarrier

noncomputable section
namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3309_21 : CStarAlgebra A] [contextInstance3309_38 : PartialOrder A] [contextInstance3309_55 : StarOrderedRing A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3325_21 : Fintype n] [contextInstance3325_33 : DecidableEq n]
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3337_21 : Fintype τ] [contextInstance3337_33 : DecidableEq τ] [contextInstance3337_49 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3364_21 : Fintype n] [contextInstance3364_33 : DecidableEq n]
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3392_21 : Fintype τ] [contextInstance3392_33 : DecidableEq τ]

variable [contextInstance3441_9 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
lemma block_add (A B : Mat q × Mat q) : block (A+B) = block A + block B := by
  ext i j
  rcases i with ⟨i,bi⟩; rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp [block, Matrix.blockDiagonal_apply]

lemma block_real_smul (r : ℝ) (A : Mat q × Mat q) : block (r • A) = r • block A := by
  ext i j
  rcases i with ⟨i,bi⟩; rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp [block, Matrix.blockDiagonal_apply]

lemma block_zero : block (0 : Mat q × Mat q) = 0 := by
  ext i j
  rcases i with ⟨i,bi⟩; rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp [block, Matrix.blockDiagonal_apply]

lemma block_sum {ι : Type*} (s : Finset ι) (A : ι → Mat q × Mat q) :
    block (∑ i ∈ s, A i) = ∑ i ∈ s, block (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [block_zero]
  | insert i s hi ih => simp only [Finset.sum_insert hi, block_add, ih]

lemma block_trace (A : Mat q × Mat q) : (block A).trace = A.1.trace + A.2.trace := by
  change (Matrix.blockDiagonal (fun b : Bool => cond b A.2 A.1)).trace = _
  rw [Matrix.trace_blockDiagonal]
  simp [add_comm]

variable {J : Type*} [contextInstance3487_21 : Fintype J]

def evenAverage (A : J → Mat q × Mat q) : Mat q × Mat q :=
  (Fintype.card J : ℝ)⁻¹ • ∑ j, A j

lemma evenAverage_isEvenDensity [Nonempty J] (A : J → Mat q × Mat q)
    (hA : ∀ j, IsEvenDensity (A j)) : IsEvenDensity (evenAverage A) := by
  have hpos : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  have he (A : Mat q × Mat q) : A.1.trace + A.2.trace = (block A).trace := (block_trace A).symm
  refine ⟨?_,?_,?_⟩
  · apply Matrix.nonneg_iff_posSemidef.mp
    simp only [evenAverage, Prod.smul_fst, Prod.fst_sum]
    exact smul_nonneg (inv_nonneg.mpr hpos.le) (Finset.sum_nonneg fun j _ => (hA j).1.nonneg)
  · apply Matrix.nonneg_iff_posSemidef.mp
    simp only [evenAverage, Prod.smul_snd, Prod.snd_sum]
    exact smul_nonneg (inv_nonneg.mpr hpos.le) (Finset.sum_nonneg fun j _ => (hA j).2.1.nonneg)
  · rw [he]
    unfold evenAverage
    rw [block_real_smul, block_sum, Matrix.trace_smul, Matrix.trace_sum]
    simp only [block_trace, (hA _).2.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    norm_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hpos.ne')
end SpinAngle.SignedTensor

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpinAngle.MatrixAnalysis
variable {n : Type*} [contextInstance3521_21 : Fintype n] [contextInstance3521_33 : DecidableEq n]
def root (a : Mat n) : Mat n := cfc Real.sqrt a

def invRoot (a : Mat n) : Mat n := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) a

def support (a : Mat n) : Mat n := cfc (fun x : ℝ => if x = 0 then 0 else 1) a

end SpinAngle.MatrixAnalysis

namespace SpinAngle.TensorMatrix
open SpinAngle.MatrixAnalysis
variable {ι n : Type*} [contextInstance3707_23 : Fintype ι] [contextInstance3707_35 : DecidableEq ι] [contextInstance3707_51 : Fintype n] [contextInstance3707_63 : DecidableEq n]

def tensor (a : ι → Mat n) : Mat (ι → n) := fun x y => ∏ i, a i (x i) (y i)

end SpinAngle.TensorMatrix

noncomputable section
open scoped BigOperators
namespace SpinAngle

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]

end SpinAngle

namespace SpinAngle.MatrixAnalysis
variable {n C : Type*} [contextInstance3931_23 : Fintype n] [contextInstance3931_35 : DecidableEq n] [contextInstance3931_51 : Fintype C] [contextInstance3931_63 : DecidableEq C]

structure Density (n : Type*) [Fintype n] [DecidableEq n] where
  matrix : Mat n
  nonneg : 0 ≤ matrix
  trace_eq_one : matrix.trace = 1

instance : Coe (Density n) (Mat n) := ⟨Density.matrix⟩

def average (r : C → Density n) : Mat n :=
  (Fintype.card C : ℝ)⁻¹ • ∑ j, (r j).matrix

end SpinAngle.MatrixAnalysis

namespace SpinAngle
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]

end SpinAngle

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SpinAngle.DependentTensor
variable {ι : Type*} [contextInstance4012_21 : Fintype ι] [contextInstance4012_33 : DecidableEq ι]
variable {ν : ι → Type*} [contextInstance4013_25 : ∀ i, Fintype (ν i)] [contextInstance4013_46 : ∀ i, DecidableEq (ν i)]

end SpinAngle.DependentTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4107_25 : Fintype τ] [contextInstance4107_37 : DecidableEq τ] [contextInstance4107_53 : Fintype J] [contextInstance4107_65 : DecidableEq J]
  [contextInstance4108_2 : Fintype n] [contextInstance4108_14 : DecidableEq n]
variable (f : τ → J)

end SpinAngle.BlockTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4180_25 : Fintype τ] [contextInstance4180_37 : DecidableEq τ] [contextInstance4180_53 : Fintype J] [contextInstance4180_65 : DecidableEq J]
  [contextInstance4181_2 : Fintype n] [contextInstance4181_14 : DecidableEq n]
variable (f : τ → J)

end SpinAngle.BlockTensor

namespace SpinAngle.TensorMatrix
open MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance4214_23 : Fintype ι] [contextInstance4214_35 : DecidableEq ι] [contextInstance4214_51 : Fintype n] [contextInstance4214_63 : DecidableEq n]

end SpinAngle.TensorMatrix

namespace SpinAngle
open scoped BigOperators
variable {R C : Type*} [contextInstance4250_23 : Fintype R] [contextInstance4250_35 : DecidableEq R] [contextInstance4250_51 : Fintype C] [contextInstance4250_63 : DecidableEq C]

end SpinAngle

namespace SpinAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young

namespace TypeLabel
variable {q : ℕ}
end TypeLabel

abbrev EvenDensity (q : ℕ) := {A : SignedTensor.Mat q × SignedTensor.Mat q // SignedTensor.IsEvenDensity A}
namespace EvenDensity
variable {q : ℕ}
def matrix (A : EvenDensity q) : Matrix (SignedTensor.Spin q) (SignedTensor.Spin q) ℂ :=
  SignedTensor.block A.val
lemma nonneg (A : EvenDensity q) : 0 ≤ A.matrix :=
  (SignedTensor.block_posSemidef A.val A.property.1 A.property.2.1).nonneg
lemma trace_eq_one (A : EvenDensity q) : A.matrix.trace = 1 := by
  rw [matrix, SignedTensor.block_trace]
  exact A.property.2.2

def toDensity (A : EvenDensity q) : MatrixAnalysis.Density (SignedTensor.Spin q) :=
  ⟨A.matrix,A.nonneg,A.trace_eq_one⟩

variable {J : Type*} [contextInstance4345_21 : Fintype J] [contextInstance4345_33 : Nonempty J]
def mean (A : J → EvenDensity q) : EvenDensity q :=
  ⟨SignedTensor.evenAverage (fun j => (A j).val),
    SignedTensor.evenAverage_isEvenDensity _ (fun j => (A j).property)⟩
end EvenDensity

namespace TypeLabel
variable {q : ℕ}
variable {τ : Type*} [contextInstance4358_21 : Fintype τ] [contextInstance4358_33 : DecidableEq τ]
variable [contextInstance4367_9 : Nonempty (Fin q)]
end TypeLabel

namespace TypeBlocks
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]

variable [contextInstance4410_9 : Nonempty (Fin q)]

end TypeBlocks
end SpinAngle

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI


