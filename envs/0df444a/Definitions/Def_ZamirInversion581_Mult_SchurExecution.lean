-- Prove2me | Definitions.Def_ZamirInversion581_Mult_SchurExecution
-- name    : ZamirInversion581_Mult_SchurExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:20.677489+00:00
-- url     : https://prove2.me/theorems/0488509d-f021-44cf-a411-5fa4df762f38
-- title:
--   The complementary Schur complement procedure: blocks, the event $E$, $\beta_n$, $\gamma_n$ and ideal-call failure
-- statement:
--   Fix $n\times n$ matrices $B,C,R,A,A'$ over a field $F$, and write
--
--   $$
--   S=A-BRC,\qquad S'=A'-B(I-R)C,\qquad M=\begin{pmatrix}A&B\\C&R^{-1}\end{pmatrix},\qquad M'=\begin{pmatrix}A'&B\\C&(I-R)^{-1}\end{pmatrix}.
--   $$
--
--   1. $E$ is the event that $R$, $I-R$, $S$, $S'$ are all invertible.
--   2. $\beta_n=\Pr_R[R,I-R\in\mathrm{GL}_n(F)]$ for uniform $R$, and $\gamma_n=\prod_{i=1}^n(1-q^{-i})$ with $q=|F|$.
--   3. For an oracle $I$, the failure probability $\varphi$ of a call on $Y$ is $1-\Pr[I(Y)=Y^{-1}]$. Given the inputs, the probability that $E$ holds and one of the six ideal calls, on $R$, $I-R$, $M$, $M'$, $S^{-1}$, $S'^{-1}$, is incorrect is
--
--   $$
--   \mathbb 1_E\Bigl(1-\prod_{i=1}^6(1-\varphi_i)\Bigr),
--   $$
--
--   because each call has fresh independent coins.
--
--   These objects are shared by the identity, the event probability and Lemma 2.2.
--
--   **Formalization Note** $2n\times2n$ matrices are indexed by $\mathrm{Fin}(2n)$, with the blocks in the order that reads row by row in the machine. Lean's $A^{-1}=0$ on singular $A$ never matters here: the ideal failure is defined to be $0$ off $E$, and on $E$ every inverse above is a true inverse.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.6–8, §2.1, complementary Schur complements and Lemma 2.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-!
# The objects of the complementary Schur complement procedure

Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, §2.1, pp.6–8.

Lean's `A⁻¹` is `0` on a singular matrix. Every inverse below is used only under the event `E`, in
which `R`, `I − R`, `S`, `S′` are invertible: `idealFailureOnE` is `0` off `E`, and `ideal_identity`
assumes the invertibility.
-/

variable {F : Type*} {n : ℕ}

/-- The `2n × 2n` block matrix `(A B; C D)`, indexed so that it reads row-major in the machine. -/
def blockMat [Zero F] (A B C D : Matrix (Fin n) (Fin n) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F :=
  Matrix.reindex (finSumFinEquiv.trans (finCongr (two_mul n).symm))
    (finSumFinEquiv.trans (finCongr (two_mul n).symm)) (Matrix.fromBlocks A B C D)

/-- The upper-left `n × n` block of a `2n × 2n` matrix. -/
def upperLeft (M : Matrix (Fin (2 * n)) (Fin (2 * n)) F) : Matrix (Fin n) (Fin n) F :=
  M.submatrix (Fin.castLE (by omega)) (Fin.castLE (by omega))

variable [Field F]

/-- `S = A − B R C`. -/
def schurS (B C R A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F := A - B * R * C

/-- `S′ = A′ − B (I − R) C`. -/
def schurS' (B C R A' : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  A' - B * (1 - R) * C

/-- The event `E`: `R`, `I − R`, `S`, `S′` are all invertible. -/
def EventE (B C R A A' : Matrix (Fin n) (Fin n) F) : Prop :=
  IsUnit R ∧ IsUnit (1 - R) ∧ IsUnit (schurS B C R A) ∧ IsUnit (schurS' B C R A')

/-- `M = (A B; C D)` with `D = R⁻¹`. -/
noncomputable def idealM (B C R A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) F := blockMat A B C R⁻¹

/-- `M′ = (A′ B; C D′)` with `D′ = (I − R)⁻¹`. -/
noncomputable def idealM' (B C R A' : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) F := blockMat A' B C (1 - R)⁻¹

variable [Fintype F] [DecidableEq F]

/-- `β_n = Pr_R[R, I − R ∈ GL_n(F)]` for `R` uniform on `n × n` matrices. -/
noncomputable def betaN (n : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  unifProb fun R : Matrix (Fin n) (Fin n) F => IsUnit R ∧ IsUnit (1 - R)

/-- `γ_n = ∏_{i=1}^n (1 − q^{−i})`, with `q = |F|`. -/
noncomputable def gammaN (n : ℕ) (F : Type*) [Fintype F] : ℝ :=
  ∏ i ∈ Finset.range n, (1 - ((Fintype.card F : ℝ) ^ (i + 1))⁻¹)

/-- The probability that a call of `I` on the `m × m` matrix `Y` returns `Y⁻¹`. Its complement is the
failure probability `φ` of that call. -/
noncomputable def callCorrect (I : InversionOracle F) (m : ℕ) (Y : Matrix (Fin m) (Fin m) F) : ℝ :=
  (I m Y Y⁻¹).toReal

open Classical in
/-- The conditional probability, given the inputs, that `E` holds and one of the six inversion calls
of the ideal execution is incorrect. The six inputs are `R`, `I − R`, `M`, `M′`, `H = S⁻¹` and
`H′ = S′⁻¹`, with fresh independent coins in each call, so that the failure probability is
`1 − ∏ᵢ (1 − φᵢ)`. It is `0` off `E`. -/
noncomputable def idealFailureOnE (I : InversionOracle F) (B C R A A' : Matrix (Fin n) (Fin n) F) :
    ℝ :=
  if EventE B C R A A' then
    1 - callCorrect I n R * callCorrect I n (1 - R) *
        callCorrect I (2 * n) (idealM B C R A) * callCorrect I (2 * n) (idealM' B C R A') *
        callCorrect I n (schurS B C R A)⁻¹ * callCorrect I n (schurS' B C R A')⁻¹
  else 0

end ZamirInversion581.Mult


