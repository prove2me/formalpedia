-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
-- name    : OAI_Analysis_DirectCrouzeix_HilbertSchmidt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:25:40.472215+00:00
-- url     : https://prove2.me/theorems/b803bd74-5103-4464-8dc1-bb0a647030a1
-- title:
--   Entry vector of a matrix and the bilinear entrywise pairing
-- statement:
--   Let $I$ and $J$ be finite index sets and consider complex matrices $M=(M_{ij})$ with rows indexed by $I$ and columns indexed by $J$. Write $M^{*}$ for the conjugate transpose, $\|M\|_{\mathrm{HS}}^{2}=\operatorname{Re}\operatorname{tr}(M^{*}M)$ for the squared Hilbert–Schmidt norm, and $\ell^{2}(I\times J)$ for the Euclidean space of complex vectors indexed by pairs $(i,j)\in I\times J$, with inner product $\langle x,y\rangle=\sum_{p}\overline{x_p}\,y_p$. The module contains:
--
--   1. **Entrywise formula for the Hilbert–Schmidt norm.** For every such matrix $M$,
--   $$
--   \|M\|_{\mathrm{HS}}^{2}=\sum_{i\in I}\sum_{j\in J}|M_{ij}|^{2}.
--   $$
--
--   2. **Entry vector.** The vector $\operatorname{vec}(M)\in\ell^{2}(I\times J)$ with coordinates $\operatorname{vec}(M)_{(i,j)}=M_{ij}$. By item 1, $\|\operatorname{vec}(M)\|^{2}=\|M\|_{\mathrm{HS}}^{2}$.
--
--   3. **Entrywise pairing.** For two matrices $M$ and $C$ of the same shape,
--   $$
--   [M,C]=\sum_{i\in I}\sum_{j\in J}M_{ij}\,C_{ij}=\operatorname{tr}\big(M^{\mathsf T}C\big).
--   $$
--   This pairing is bilinear (no complex conjugation is applied), and $[M,C]=\langle\operatorname{vec}(\overline{M}),\operatorname{vec}(C)\rangle$, where $\overline{M}$ is the entrywise complex conjugate of $M$.
--
--   The entry vector identifies $\ell^{2}(I\times J)$ with matrices carrying the Hilbert–Schmidt norm, so that vectors of a Kronecker-product space $\mathbb{C}^{n}\otimes\mathbb{C}^{m}$ can be handled as $n\times m$ matrices. The pairing expresses matrix entries of Kronecker products: for $X,Y\in\mathbb{C}^{n\times m}$, $A\in M_n(\mathbb{C})$ and $C\in M_m(\mathbb{C})$ one has $\langle\operatorname{vec}(Y),(A\otimes C)\operatorname{vec}(X)\rangle=[\,Y^{*}AX,\ C\,]$, and the Cauchy–Schwarz inequality gives $|[M,C]|^{2}\le\|M\|_{\mathrm{HS}}^{2}\,\|C\|_{\mathrm{HS}}^{2}$ (both proved separately).
--
--   **Formalization Note** `hsVector M` is `WithLp.toLp 2 (fun p => M p.1 p.2)` in `EuclideanSpace ℂ (ι × κ)`, `entryPair M C` is the double sum `∑ i, ∑ j, M i j * C i j`, and item 1 is the theorem `hsSq_eq_sum_norm_sq`; the index types are arbitrary finite types.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HilbertSchmidt.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HilbertSchmidt.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus

namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_eq_sum_norm_sq {ι : Type u_8} {κ : Type u_9} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

def hsVector {ι : Type u_10} {κ : Type u_11} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    EuclideanSpace ℂ (ι × κ) := WithLp.toLp 2 (fun p => M p.1 p.2)

def entryPair {ι : Type u_18} {κ : Type u_19} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ℂ := ∑ i, ∑ j, M i j * C i j

end DirectCrouzeix

end

end OAI


