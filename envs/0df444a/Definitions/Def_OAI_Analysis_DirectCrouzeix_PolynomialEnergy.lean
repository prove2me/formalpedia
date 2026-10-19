-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
-- name    : OAI_Analysis_DirectCrouzeix_PolynomialEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:34:02.635819+00:00
-- url     : https://prove2.me/theorems/d8d45f3f-66b7-4099-a1f5-2f2ed09ee3b4
-- title:
--   Polynomials with matrix coefficients: scalar evaluation, Faber combinations and boundary energy
-- statement:
--   Fix $m\in\mathbb{N}$ and write $M_m(\mathbb{C})$ for the complex $m\times m$ matrices, $I_m$ for the identity matrix, $\|M\|_{\mathrm{HS}}^{2}=\sum_{i,j}|M_{ij}|^{2}$ for the squared Hilbert–Schmidt norm, and $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ for the circle with its normalized Haar measure $dt$ (total mass $1$). The module defines:
--
--   1. **Matrix polynomials.** $M_m(\mathbb{C})[X]$, the ring of polynomials $G=\sum_kC_kX^{k}$ in an indeterminate $X$ that commutes with all coefficients $C_k\in M_m(\mathbb{C})$.
--
--   2. **Evaluation at a complex number.** For $z\in\mathbb{C}$, the ring homomorphism $M_m(\mathbb{C})[X]\to M_m(\mathbb{C})$ given by substituting the central matrix $zI_m$ for $X$:
--   $$
--   G(z)=\sum_{k}z^{k}C_k\qquad\text{for } G=\sum_kC_kX^{k}.
--   $$
--   The rules $C(z)=C$ for a constant polynomial $C$ and $X(z)=zI_m$ are recorded as simplification lemmas.
--
--   3. **Scalar polynomials as matrix polynomials.** A polynomial $p=\sum_ka_kX^{k}\in\mathbb{C}[X]$ is sent to $p\,I_m=\sum_k(a_kI_m)X^{k}\in M_m(\mathbb{C})[X]$.
--
--   4. **Faber combination.** Given a sequence $(b_k)_{k\in\mathbb{N}}$ of scalar polynomials, $N\in\mathbb{N}$ and matrices $C_0,\dots,C_{N-1}\in M_m(\mathbb{C})$,
--   $$
--   \mathcal F_b(C)=\sum_{k=0}^{N-1}C_k\,\big(b_k(X)\,I_m\big)\in M_m(\mathbb{C})[X],
--   $$
--   whose value at $z$ is $\sum_{k}b_k(z)\,C_k$.
--
--   5. **Boundary energy.** For a function $h:\mathbb{T}\to\mathbb{C}$ and $G\in M_m(\mathbb{C})[X]$,
--   $$
--   \mathcal E_h(G)=\int_{\mathbb{T}}\big\|G(h(t))\big\|_{\mathrm{HS}}^{2}\,dt .
--   $$
--
--   In the intended use $h$ parametrizes the boundary of a domain containing the numerical range of a matrix and the $b_k$ are the Faber polynomials of that domain. The energy is monotone under multiplication by contractions: if $h$ is continuous and $\|F(h(t))\|\le1$ in operator norm for all $t$, then $\mathcal E_h(FG)\le\mathcal E_h(G)$ and $\mathcal E_h(GF)\le\mathcal E_h(G)$. Through the tensor functional calculus, the Faber combination corresponds to $\sum_kb_k(A)\otimes C_k$ for an $n\times n$ matrix $A$ (both facts proved separately), which links scalar Faber expansions to the matrix-coefficient bound.
--
--   **Formalization Note** `MatrixPolynomial m` is `Polynomial (Matrix (Fin m) (Fin m) ℂ)`; `matrixPolynomialValue z` is `Polynomial.eval₂RingHom' (RingHom.id _) (z • 1) _`, with simplification lemmas `matrixPolynomialValue_C` and `matrixPolynomialValue_X`; `scalarMatrixPolynomial p` is `p.map (algebraMap ℂ _)`; `faberPolynomial b C` puts the matrix `C k` to the left of the scalar polynomial (the order is immaterial since scalar matrices are central). `polynomialEnergy h G` is a Bochner integral for `AddCircle.haarAddCircle`, equal to $0$ by convention when the integrand is not integrable; this does not occur for continuous $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

abbrev MatrixPolynomial (m : ℕ) := Polynomial (Matrix (Fin m) (Fin m) ℂ)

def matrixPolynomialValue {m : ℕ} (z : ℂ) :
    MatrixPolynomial m →+* Matrix (Fin m) (Fin m) ℂ :=
  Polynomial.eval₂RingHom' (RingHom.id _) (z • 1) (by
    intro C
    change C * (z • 1) = (z • 1) * C
    simp [])

@[simp] theorem matrixPolynomialValue_C {m : ℕ} (z : ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) : matrixPolynomialValue z (Polynomial.C C) = C := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem matrixPolynomialValue_X {m : ℕ} (z : ℂ) :
    matrixPolynomialValue (m := m) z Polynomial.X = z • 1 := by
  exact Polynomial.eval₂_X _ _

def scalarMatrixPolynomial {m : ℕ} (p : Polynomial ℂ) : MatrixPolynomial m :=
  p.map (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ))

def faberPolynomial {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) : MatrixPolynomial m :=
  ∑ k : Fin N, Polynomial.C (C k) * scalarMatrixPolynomial (b k)

def polynomialEnergy {m : ℕ} (h : BoundaryCircle → ℂ) (G : MatrixPolynomial m) : ℝ :=
  ∫ t, hsSq (matrixPolynomialValue (h t) G) ∂circleMeasure

end DirectCrouzeix

end

end OAI


