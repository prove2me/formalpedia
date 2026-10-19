-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_OuterApproximation
-- name    : OAI_Analysis_DirectCrouzeix_OuterApproximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:24:14.984343+00:00
-- url     : https://prove2.me/theorems/6b627530-8c37-49c2-a15b-2ecc1b195937
-- title:
--   Coefficient form and scalar homogeneity of the scalar and tensor evaluations of matrix polynomials
-- statement:
--   Let $M_m(\mathbb{C})$ be the complex $m\times m$ matrices and $M_m(\mathbb{C})[\lambda]$ the polynomials $F=\sum_jF_j\lambda^j$ with coefficients $F_j\in M_m(\mathbb{C})$, the indeterminate $\lambda$ commuting with all coefficients. Two evaluations of such polynomials are used:
--
--   - the **scalar evaluation** at $z\in\mathbb{C}$, $F(z)=\sum_jz^jF_j\in M_m(\mathbb{C})$, obtained by substituting $\lambda=zI_m$;
--   - the **tensor evaluation** at $A\in M_n(\mathbb{C})$, $F[A]=\sum_jA^j\otimes F_j\in M_{nm}(\mathbb{C})$, obtained by sending each coefficient $F_j$ to $I_n\otimes F_j$ and $\lambda$ to $A\otimes I_m$; here $\otimes$ is the Kronecker product, with rows and columns indexed by pairs and $(A\otimes C)_{(i,j),(k,l)}=A_{ik}C_{jl}$.
--
--   For a family $B=(B_0,\dots,B_d)$ in $M_m(\mathbb{C})$ let $Q_B=\sum_{k=0}^dB_k\lambda^k\in M_m(\mathbb{C})[\lambda]$ be its coefficient polynomial and $p_B(z)=\sum_{k=0}^dz^kB_k$ its matrix-valued polynomial function. This file records three identities, used as simplification rules:
--
--   1. the scalar evaluation of $Q_B$ at $z$ is $p_B(z)$, for every $z\in\mathbb{C}$;
--   2. $(sF)(z)=s\,F(z)$ for all $s,z\in\mathbb{C}$ and $F\in M_m(\mathbb{C})[\lambda]$;
--   3. $(sF)[A]=s\,F[A]$ for all $s\in\mathbb{C}$, $A\in M_n(\mathbb{C})$ and $F\in M_m(\mathbb{C})[\lambda]$.
--
--   In formulas,
--   $$Q_B(z)=\sum_{k=0}^dz^kB_k,\qquad(sF)(z)=s\,F(z),\qquad(sF)[A]=s\,F[A].$$
--
--   These identities connect the coefficient form of the matrix-valued Crouzeix inequality, which involves $\sum_kA^k\otimes B_k$ and $\sup_z\|\sum_kz^kB_k\|$, with the ring of matrix polynomials, on which both evaluations are ring homomorphisms, and they let scalar normalizing factors be moved through both evaluations.
--
--   **Formalization Note** The three statements are the simp lemmas `matrixPolynomialValue_coefficientPolynomial`, `matrixPolynomialValue_smul` and `tensorPolynomial_smul`. Scalar evaluation is `matrixPolynomialValue z`, tensor evaluation is `tensorPolynomial A`, $Q_B$ is `coefficientPolynomial B` and $p_B(z)$ is `polynomialValue B z`; the file introduces no new definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/OuterApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/OuterApproximation.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Convexity

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix

@[simp] theorem matrixPolynomialValue_coefficientPolynomial {m d : ℕ}
    (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) (z : ℂ) :
    matrixPolynomialValue z (coefficientPolynomial B) = polynomialValue B z := by
  simp only [coefficientPolynomial,map_sum,map_mul,map_pow,matrixPolynomialValue_C,
    matrixPolynomialValue_X,smul_pow,one_pow,Matrix.mul_smul,Matrix.mul_one,polynomialValue]

@[simp] theorem matrixPolynomialValue_smul {m : ℕ} (F : MatrixPolynomial m) (s z : ℂ) :
    matrixPolynomialValue z (s • F) = s • matrixPolynomialValue z F := by
  rw [← smul_one_smul (Matrix (Fin m) (Fin m) ℂ) s F,Polynomial.smul_eq_C_mul,
    map_mul,matrixPolynomialValue_C,Matrix.smul_mul,Matrix.one_mul]

@[simp] theorem tensorPolynomial_smul {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F : MatrixPolynomial m) (s : ℂ) :
    tensorPolynomial A (s • F) = s • tensorPolynomial A F := by
  rw [← smul_one_smul (Matrix (Fin m) (Fin m) ℂ) s F,Polynomial.smul_eq_C_mul,
    map_mul,tensorPolynomial_C,Matrix.kronecker_smul,Matrix.one_kronecker_one,
    Matrix.smul_mul,Matrix.one_mul]

end DirectCrouzeix

namespace DirectCrouzeix

open Set Filter Metric

end DirectCrouzeix

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


