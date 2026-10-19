-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_BlockStates
-- name    : OAI_Probability_EntangledGames_BlockStates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:15:45.895926+00:00
-- url     : https://prove2.me/theorems/7f154228-c554-47d2-bce5-4d0aa317a2d0
-- title:
--   Block-diagonal and direct-sum POVMs, normalized states and weighted block states
-- statement:
--   This file introduces constructions that combine several bipartite states or measurements into one; they are used to assemble single-round strategies from pieces.
--
--   A bipartite pure state is encoded by a coefficient matrix $C\in\mathbb{C}^{m\times n}$ (with $m,n$ finite index sets), standing for $\psi_C=\sum_{i,j}C_{ij}\,e_i\otimes e_j\in\mathbb{C}^m\otimes\mathbb{C}^n$; its squared Hilbert–Schmidt norm is $\|C\|_2^2=\sum_{i,j}|C_{ij}|^2$, and $\mathrm{Pr}_C(M,N)=\operatorname{Re}\langle\psi_C,(M\otimes N)\psi_C\rangle$ is the Born-rule value of a pair of effects. A POVM on $\mathbb{C}^m$ with outcomes in a finite set $A$ is a family $(P_a)_{a\in A}$ of positive semidefinite matrices with $\sum_aP_a=\mathbf 1$.
--
--   1. **Block POVM.** For a finite label set $R$ and POVMs $P^{(r)}$ on $\mathbb{C}^m$ with outcomes in $A$ ($r\in R$), the POVM $\bigoplus_rP^{(r)}$ on $\mathbb{C}^m\otimes\mathbb{C}^R$ (index set $m\times R$) has the block-diagonal effects
--   $$\Big(\bigoplus_{r\in R}P^{(r)}\Big)_a=\sum_{r\in R}P^{(r)}_a\otimes e_re_r^*,$$
--   that is, it reads the classical label $r$ and then measures $P^{(r)}$.
--   2. **Normalization with a fallback.** For $C,D\in\mathbb{C}^{m\times n}$, $\operatorname{unitize}(C,D)=C/\|C\|_2$ if $C\neq0$, and $\operatorname{unitize}(0,D)=D$.
--   3. **Square embedding of a state.** $\operatorname{sq}(C)=\begin{pmatrix}0&C\\0&0\end{pmatrix}$ is the $(m\oplus n)\times(m\oplus n)$ coefficient matrix of the same state with both parties' spaces enlarged to $\mathbb{C}^m\oplus\mathbb{C}^n$: Alice's part lies in the first summand and Bob's part in the second.
--   4. **Direct-sum POVM.** For POVMs $P$ on $\mathbb{C}^m$ and $Q$ on $\mathbb{C}^n$ with the same outcome set $A$, $P\oplus Q$ is the POVM on $\mathbb{C}^m\oplus\mathbb{C}^n$ with effects $\begin{pmatrix}P_a&0\\0&Q_a\end{pmatrix}$.
--   5. **Weighted block state.** For weights $w\colon R\to\mathbb{R}$ and matrices $C_r\in\mathbb{C}^{m\times n}$, $\operatorname{blk}(w,C)$ is the block-diagonal $(m\times R)\times(n\times R)$ matrix
--   $$\operatorname{blk}(w,C)_{(i,r),(j,s)}=\begin{cases}\sqrt{w_r}\,(C_r)_{ij}&\text{if }r=s,\\0&\text{if }r\neq s,\end{cases}$$
--   the coefficient matrix of $\sum_r\sqrt{w_r}\,\psi_{C_r}\otimes e_r\otimes e_r$, in which both parties hold a copy of the label $r$. For $w\ge0$ one has $\|\operatorname{blk}(w,C)\|_2^2=\sum_rw_r\|C_r\|_2^2$.
--
--   Two auxiliary facts are proved: a block-diagonal matrix with positive semidefinite blocks is positive semidefinite, and so is $\begin{pmatrix}M&0\\0&N\end{pmatrix}$ for positive semidefinite $M$ and $N$; they show that the block and direct-sum constructions are POVMs.
--
--   With these constructions, a family of strategies $(C_r,P^{(r)},Q^{(r)})_{r\in R}$ used with weights $w_r\ge0$ becomes a single strategy with state $\operatorname{blk}(w,C)$ and measurements $\bigoplus_rP^{(r)}$ and $\bigoplus_rQ^{(r)}$, whose Born-rule values are $\sum_rw_r\,\mathrm{Pr}_{C_r}(P^{(r)}_a,Q^{(r)}_b)$. The map $\operatorname{unitize}$ turns any nonzero coefficient matrix into a unit state. The square embedding and direct sums put the state and both players' measurements on spaces of the same shape: $\mathrm{Pr}_{\operatorname{sq}(C)}(M_1\oplus M_2,N_1\oplus N_2)=\mathrm{Pr}_C(M_1,N_2)$, so Alice's effects act through their first diagonal block and Bob's through their second.
--
--   **Formalization Note** The definitions are `POVM.blocks`, `unitize`, `squareState`, `POVM.sum` and `weightedBlock`; the auxiliary lemmas are `posSemidef_blockDiagonal` and `posSemidef_fromBlocks_diag`. `unitize` tests whether $\|C\|_2^2=0$, and `weightedBlock` uses `Real.sqrt`, which is $0$ on negative weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/BlockStates.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/BlockStates.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain

namespace OAI

universe u_m u_n u_R u_A u_B u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Blocks
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
variable [DecidableEq m]
lemma posSemidef_blockDiagonal (A : R → Matrix m m ℂ) (hA : ∀ r, (A r).PosSemidef) :
    (Matrix.blockDiagonal A).PosSemidef := by
  let B := Matrix.blockDiagonal (fun r => CFC.sqrt (A r))
  have he : Bᴴ*B = Matrix.blockDiagonal A := by
    simp only [B, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A r))).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ (hA r).nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self B

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq n]
def POVM.blocks (P : R → POVM m A) : POVM (m×R) A where
  effect a := Matrix.blockDiagonal (fun r => (P r).effect a)
  pos a := posSemidef_blockDiagonal _ (fun r => (P r).pos a)
  total := by
    change (∑ a, (Matrix.blockDiagonalAddMonoidHom m m R ℂ) (fun r => (P r).effect a)) = _
    rw [← map_sum]
    have he : (∑ a, fun r => (P r).effect a) = 1 := by
      funext r; simpa only [Finset.sum_apply, Pi.one_apply] using (P r).total
    rw [he]
    exact Matrix.blockDiagonal_one

end Blocks

section Normalization
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
def unitize (C D : Matrix m n ℂ) : Matrix m n ℂ :=
  if hsSq C = 0 then D else (Real.sqrt (hsSq C))⁻¹ • C

end Normalization

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A] [Fintype B]
end Payoff
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma posSemidef_fromBlocks_diag {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  let T := Matrix.fromBlocks (CFC.sqrt A) (0 : Matrix m n ℂ) 0 (CFC.sqrt B)
  have he : Tᴴ*T = Matrix.fromBlocks A 0 0 B := by
    simp only [T, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self T

def squareState (C : Matrix m n ℂ) : Matrix (m⊕n) (m⊕n) ℂ := Matrix.fromBlocks 0 C 0 0

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B]
def POVM.sum (P : POVM m A) (Q : POVM n A) : POVM (m⊕n) A where
  effect a := Matrix.fromBlocks (P.effect a) 0 0 (Q.effect a)
  pos a := posSemidef_fromBlocks_diag (P.pos a) (Q.pos a)
  total := by
    have he : (∑ a, Matrix.fromBlocks (P.effect a) (0 : Matrix m n ℂ) 0 (Q.effect a)) =
        Matrix.fromBlocks (∑ a, P.effect a) 0 0 (∑ a, Q.effect a) := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.sum_apply]
    rw [he, P.total, Q.total, Matrix.fromBlocks_one]

end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law
section Stack
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
def weightedBlock (w : R → ℝ) (C : R → Matrix m n ℂ) : Matrix (m×R) (n×R) ℂ :=
  Matrix.blockDiagonal (fun r => Real.sqrt (w r) • C r)
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
end Stack

end ThresholdParallelRepetition.QuantumSampling

end

end OAI


