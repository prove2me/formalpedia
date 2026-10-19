-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
-- name    : OAI_Probability_EntangledGames_HilbertSchmidt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:54:46.38517+00:00
-- url     : https://prove2.me/theorems/7e8d3433-0d71-482f-bb2f-f040b9448407
-- title:
--   Squared Hilbert–Schmidt norm and the Hermitian dilation of a rectangular matrix
-- statement:
--   Let $m,n$ be finite index sets and $M\in\mathbb{C}^{m\times n}$ a complex matrix with conjugate transpose $M^*$.
--
--   1. **Squared Hilbert–Schmidt norm.**
--   $$\|M\|_2^2=\sum_{i\in m}\sum_{j\in n}|M_{ij}|^2 ,$$
--   the square of the Frobenius (Hilbert–Schmidt) norm; it equals $\operatorname{tr}(M^*M)$.
--   2. **Hermitian dilation.** The square block matrix indexed by the disjoint union $m\sqcup n$,
--   $$\mathcal D(M)=\begin{pmatrix}0&M\\M^*&0\end{pmatrix}.$$
--
--   The squared Hilbert–Schmidt norm is the error measure used throughout the analysis of approximate strategies: distances between filters, states and their binned approximations are measured in $\|\cdot\|_2^2$. The dilation $\mathcal D(M)$ is Hermitian, and its absolute value is block diagonal with blocks $(MM^*)^{1/2}$ and $(M^*M)^{1/2}$; it therefore transfers perturbation inequalities for Hermitian matrices to rectangular ones, for instance to compare the right absolute values $(M^*M)^{1/2}$ and $(N^*N)^{1/2}$ of two matrices of the same shape.
--
--   **Formalization Note** The definitions are `hsSq M`, the sum of `Complex.normSq` of the entries, and `dilation M := Matrix.fromBlocks 0 M Mᴴ 0`, indexed by the sum type `m ⊕ n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/HilbertSchmidt.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/HilbertSchmidt.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport

namespace OAI

universe u_m u_n u_p u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

def hsSq (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

def dilation (M : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 M Mᴴ 0

end ThresholdParallelRepetition.QuantumSampling

end

end OAI


