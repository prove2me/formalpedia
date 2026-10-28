-- Prove2me | Definitions.Def_SimpleSSA_Monotone_Basic
-- name    : SimpleSSA_Monotone_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:27.575566+00:00
-- url     : https://prove2.me/theorems/997e7edc-59bd-47aa-9537-eedcb0012f88
-- title:
--   pp. 1–5 — entropy and relative entropy (3) in nats, Tr_C, I/d, Hilbert–Schmidt vectorization, the relative modular operator Δ, and the map 𝒰 with its adjoint
-- statement:
--   This module fixes the objects of Nielsen and Petz, *A simple proof of the strong subadditivity inequality*, for finite quantum systems. A system $A$ is a finite set of basis labels, an operator on $A$ is a complex $A\times A$ matrix, and $M(A)$ denotes the space of such matrices. Operators on a composite system $AB$ are matrices indexed by pairs $(a,b)$ (system $A$ first), and on $ABC$ by triples $(a,(b,c))$.
--
--   1. **Von Neumann entropy (p. 1).** $S(\rho) \equiv -\operatorname{tr}(\rho\ln\rho)$, with the natural logarithm.
--   2. **Relative entropy (3), p. 2.**
--   $$S(\rho\|\sigma) \equiv \operatorname{tr}(\rho\ln\rho - \rho\ln\sigma).$$
--   3. **Maximally mixed state.** $I_A/d_A$, where $d_A$ is the dimension of $A$.
--   4. **Partial trace over $C$.** $\rho_{AB} = \operatorname{tr}_C\rho_{ABC}$, with entries $(\rho_{AB})_{(a,b),(a',b')} = \sum_c (\rho_{ABC})_{(a,(b,c)),(a',(b',c))}$.
--   5. **Hilbert–Schmidt structure (p. 4).** $\langle X,Y\rangle \equiv \operatorname{tr}(X^\dagger Y)$ on $M(A)$. A matrix $X$ is identified with the vector $\operatorname{vec}X = (X_{ij})_{(i,j)}$ (row-major order), so that $\langle X,Y\rangle$ is the standard inner product of $\operatorname{vec}X$ and $\operatorname{vec}Y$, and a linear map on $M(A)$ is identified with its matrix on $\mathbb C^{A\times A}$.
--   6. **Relative modular operator (pp. 3–4).** For $\rho,\sigma$ fixed, $\mathcal L(X) \equiv \sigma X$, $\mathcal R(X) \equiv X\rho^{-1}$ and $\Delta \equiv \mathcal L\mathcal R$, i.e. $\Delta(X) = \sigma X\rho^{-1}$. In the row-major identification $\Delta$ is the Kronecker matrix $\sigma\otimes(\rho^{-1})^{T}$.
--   7. **Square roots.** $\rho^{1/2}$ and $\rho^{-1/2}$ by the functional calculus (apply $x\mapsto\sqrt x$, resp. $x\mapsto 1/\sqrt x$, to the eigenvalues).
--   8. **The map $\mathcal U$ (p. 5).** For an operator $\rho_{AB}$ with $\rho_A = \operatorname{tr}_B\rho_{AB}$,
--   $$\mathcal U(X) \equiv (X\rho_A^{-1/2}\otimes I_B)\,\rho_{AB}^{1/2},\qquad X\in M(A),$$
--   its matrix from $\mathbb C^{A\times A}$ to $\mathbb C^{(A\times B)\times(A\times B)}$ (column $(a,a')$ is $\operatorname{vec}\,\mathcal U(E_{aa'})$, $E_{aa'}$ the matrix unit), and the operation stated on p. 5 as its adjoint,
--   $$\mathcal U^\dagger(Y) = \operatorname{tr}_B\big(Y\rho_{AB}^{1/2}(\rho_A^{-1/2}\otimes I_B)\big),\qquad Y\in M(AB).$$
--
--   These are the objects in which the paper's identities (5), (7), the properties of $\mathcal U$, and the inequalities (4), (6) are stated.
--
--   **Formalization Note** Logarithms are natural and are taken by the continuous functional calculus (`matrixLog` = `cfc Real.log`, so $\ln 0 = 0$ on a kernel, which gives the usual $0\ln 0 = 0$ in $S(\rho)$). The relative entropy is real-valued: it is the paper's value whenever the support of $\rho$ lies in the support of $\sigma$, and every theorem of the mission applies it only to such pairs (invertible $\sigma$, or the pair of (5)). The logarithm of $\Delta$ used in (7) is the functional-calculus logarithm of the matrix $\sigma\otimes(\rho^{-1})^T$, i.e. the paper's p. 4 definition, not the formula $\ln\mathcal L+\ln\mathcal R$. The matrix inverse $\rho^{-1}$ is Mathlib's, which is $0$ for singular $\rho$; theorems using $\Delta$ assume invertibility. The partial traces $\operatorname{tr}_B$, $\operatorname{tr}_A$ and the density-matrix predicate are the published `WildeQIT_partialTrace` and `QAlgorithms_Defs_Information` layers; `matrixLog` and the functional calculus are the published Tropp layer.
-- source:
--   Nielsen & Petz, A simple proof of the strong subadditivity inequality, arXiv:quant-ph/0408130v3, pp. 1–5: S(ρ) p. 1; (3) p. 2; I/d (5)–(6) p. 2; ℒ, ℛ, Δ pp. 3–4; ⟨X,Y⟩ and ln of maps p. 4; 𝒰 and 𝒰† p. 5

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch8_entropy
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Defs_Information

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

noncomputable section

namespace SimpleSSA.Monotone

open TroppMatrixConcentration

variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- p. 1: the von Neumann entropy `S(ρ) ≡ −tr(ρ ln ρ)`, natural logarithm. `matrixLog` is
`cfc Real.log`, so `ln 0 = 0` on the kernel of `ρ` and `ρ ln ρ` carries the convention `0 ln 0 = 0`. -/
def entropy (ρ : Matrix A A ℂ) : ℝ :=
  -(Matrix.trace (ρ * matrixLog ρ)).re

/-- (3), p. 2: the relative entropy `S(ρ‖σ) ≡ tr(ρ ln ρ − ρ ln σ)`, natural logarithm, real part.
It is the paper's value whenever `supp ρ ⊆ supp σ` (for instance `σ` invertible); every theorem
of the mission applies it only to such pairs. -/
def relEntropy (ρ σ : Matrix A A ℂ) : ℝ :=
  (Matrix.trace (ρ * matrixLog ρ - ρ * matrixLog σ)).re

/-- pp. 2, (5)–(6): the maximally mixed state `I/d` on a finite system of dimension `d`. -/
def maximallyMixed (A : Type) [Fintype A] [DecidableEq A] : Matrix A A ℂ :=
  ((Fintype.card A : ℂ)⁻¹) • (1 : Matrix A A ℂ)

/-- p. 1: the partial trace over `C` of an operator on `A ⊗ B ⊗ C`, ordered `A × (B × C)`
(`ρ_AB = Tr_C ρ_ABC`). -/
def traceOutC (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => ∑ c, ρ (p.1, (p.2, c)) (q.1, (q.2, c))

/-- Row-major vectorization `M(A) ≅ ℂ^{A×A}`, `X ↦ (X i j)_{(i,j)}`. Linear maps on matrices
are represented by their matrices on `ℂ^{A×A}` in this basis. -/
def vecHS (X : Matrix A A ℂ) : A × A → ℂ :=
  fun p => X p.1 p.2

/-- p. 4: the Hilbert–Schmidt inner product `⟨X, Y⟩ ≡ tr(X†Y)`. -/
def hsInner (X Y : Matrix A A ℂ) : ℂ :=
  Matrix.trace (Xᴴ * Y)

/-- The linear map on matrices with matrix `M` (in the row-major basis of `vecHS`), applied to `X`. -/
def applyHS (M : Matrix (A × A) (A × A) ℂ) (X : Matrix A A ℂ) : Matrix A A ℂ :=
  Matrix.of fun i j => (M *ᵥ vecHS X) (i, j)

/-- pp. 3–4: the relative modular operator `Δ = ℒℛ`, `Δ(X) = σ X ρ⁻¹`, as a matrix on `ℂ^{A×A}`
in the row-major basis: the Kronecker product `σ ⊗ (ρ⁻¹)ᵀ`. -/
def modularOp (ρ σ : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ :=
  σ ⊗ₖ (ρ⁻¹)ᵀ

/-- p. 3: `ρ^{1/2}` by the functional calculus. -/
def sqrtM (ρ : Matrix A A ℂ) : Matrix A A ℂ :=
  ch8_matrixFunction Real.sqrt ρ

/-- p. 3: `ρ^{−1/2}` by the functional calculus, `x ↦ (√x)⁻¹` on the spectrum. -/
def invSqrtM (ρ : Matrix A A ℂ) : Matrix A A ℂ :=
  ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) ρ

/-- p. 5: the map `𝒰 : M(A) → M(AB)`, `𝒰(X) ≡ (X ρ_A^{−1/2} ⊗ I_B) ρ_AB^{1/2}`, where
`ρ_A = Tr_B ρ_AB`. -/
def petzMap (ρ : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  ((X * invSqrtM (WildeQIT.partialTraceRight ρ)) ⊗ₖ (1 : Matrix B B ℂ)) * sqrtM ρ

/-- The matrix of `𝒰` from `ℂ^{A×A}` to `ℂ^{(A×B)×(A×B)}` in the row-major bases: its column
`(a, a')` is `vec 𝒰(E_{aa'})`, `E_{aa'}` the matrix unit. -/
def petzMatrix (ρ : Matrix (A × B) (A × B) ℂ) : Matrix ((A × B) × (A × B)) (A × A) ℂ :=
  Matrix.of fun p q => petzMap ρ (Matrix.single q.1 q.2 1) p.1 p.2

/-- p. 5: the stated adjoint `𝒰†(Y) = tr_B(Y ρ_AB^{1/2} (ρ_A^{−1/2} ⊗ I_B))`. -/
def petzAdjoint (ρ : Matrix (A × B) (A × B) ℂ) (Y : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  WildeQIT.partialTraceRight
    (Y * sqrtM ρ * (invSqrtM (WildeQIT.partialTraceRight ρ) ⊗ₖ (1 : Matrix B B ℂ)))

end SimpleSSA.Monotone


