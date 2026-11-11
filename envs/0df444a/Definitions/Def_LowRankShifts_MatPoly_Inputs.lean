-- Prove2me | Definitions.Def_LowRankShifts_MatPoly_Inputs
-- name    : LowRankShifts_MatPoly_Inputs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:57:19.322598+00:00
-- url     : https://prove2.me/theorems/0a3eb6ed-97dc-40f5-99d0-c065292f49e2
-- title:
--   Input layouts, matrix oracles and the success probability of an oracle for a matrix polynomial
-- statement:
--   These are the conventions by which the reductions of the paper receive their inputs on the machine `LowRankShifts_MatPoly_Machine`.
--
--   - A matrix is stored row-major; a tuple $M=(M_1,\dots,M_\ell)$ of matrices is a list of field blocks, one per matrix.
--   - A polynomial given as an input (Theorem 2.5, Lemma 2.8, Corollary 2.9) is its coefficient list, as one field block, and its words, as integer data in the index memory: for each monomial in order, the word length followed by the variable index and the transpose flag ($1$ transposed, $0$ not) of each letter.
--   - Reductions with a success-probability parameter $\alpha$ (Theorems 3.4, 3.5) receive $M$ and the two integers $n$ and $K=\lceil 1/\alpha\rceil$ (`thresholdInput`). The self-corrector of Corollary 2.12 receives $M$ and $n$ (`tupleInput`); that of Lemma 2.11 receives $x\in F^\ell$ and the degree bound $d$ (`vectorInput`). The verifier of Theorem 2.5 receives $A_1,\dots,A_\ell$, $C$ and the coefficients of $P$, the words of $P$, and $n,k,\ell,s$ (`verifierInput`); Lemma 2.8 receives $A_1..A_\ell,U_1..U_\ell,V_1..V_\ell$ and $P$ with $n,r,\ell,s$ (`shiftInput`), Corollary 2.9 the same with one $U$ (`sharedShiftInput`).
--   - A (possibly randomized) **matrix oracle** $D:(F^{n\times n})^\ell\to\mathrm{PMF}(F^{n\times n})$ is presented to the machine as the vector oracle `matOracle D` of dimensions $\ell n^2$ and $n^2$ through the same row-major layout.
--   - The **success probability** of $D$ for $P$ is
--   $$\mathrm{succ}_P(D)=\Pr_{A\sim(F^{n\times n})^\ell}[D(A)=P(A)]=\mathbb E_{A}\big[D(A)(\{P(A)\})\big],$$
--   over a uniform tuple $A$ and the randomness of $D$.
--
--   **Formalization Note.** Uniform averages are `unifMean` from the published `ZamirInversion581_Mult_Uniform`. Giving the start address of every input block lets a program reach a matrix of the tuple without index multiplication.
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), pp. 10–19 (PDF 13–22): inputs of Theorem 2.5, Lemma 2.8, Corollary 2.9, Lemma 2.11, Corollary 2.12, Theorems 3.4, 3.5

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-!
# Inputs, outputs and oracles of the reductions

Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, *Worst-Case to Average-Case Reductions
for Linear Algebra: Optimal, Simple, and General*, STOC 2027 submission, §2.3–§3.2 (pp. 10–21).

* Matrices are stored row-major (`matList`); a tuple of matrices is a list of field blocks, one per
  matrix (`tupleBlocks`). `initConfig` lays the blocks out consecutively from field address `0` and
  writes the start address of every block into the index memory, so a matrix of the input is
  reached through its start address.
* A polynomial given as an input is two blocks of data: its coefficients, as one field block
  (`coeffBlock`), and its words, in the index memory after the block starts (`wordCode`): for each
  monomial in list order, the word length followed by, for each letter, its variable index and its
  transpose flag (`1` transposed, `0` not).
* A matrix oracle `D : (F^{n×n})^ℓ → PMF (F^{n×n})` is presented to the machine as the vector
  oracle `matOracle D` of dimensions `ℓ·n²` and `n²`, through the same row-major layout: a query
  reads the `ℓ` matrices row-major and block after block; the answer is written row-major.
* `succProb P D = Pr_{A ∼ (F^{n×n})^ℓ}[D(A) = P(A)]` is the success probability of an oracle, over a
  uniform tuple `A` and the oracle's randomness.
-/

variable {F : Type*} [Field F]

/-- A tuple of `n × m` matrices as a list of field blocks, one row-major block per matrix. -/
def tupleBlocks {ℓ n m : ℕ} (A : Fin ℓ → Matrix (Fin n) (Fin m) F) : List (List F) :=
  List.ofFn fun k => matList (A k)

/-- The coefficients of `P`, in list order. -/
def coeffBlock {ℓ : ℕ} (P : MatPolynomial F ℓ) : List F := P.map Prod.fst

/-- The words of `P` as index data: for each monomial, the word length followed by the variable
index and the transpose flag (`1` transposed, `0` not) of each letter. -/
def wordCode {ℓ : ℕ} (P : MatPolynomial F ℓ) : List ℤ :=
  P.flatMap fun m => (m.2.length : ℤ) :: m.2.flatMap fun x => [(x.1 : ℤ), if x.2 then 1 else 0]

/-- A tuple of `n × n` matrices as one vector of length `ℓ·n²`: block `k`, row `i`, column `j`
at position `(j + n·i) + n²·k`. -/
def flatTuple {ℓ n : ℕ} (A : Fin ℓ → Matrix (Fin n) (Fin n) F) : Fin (ℓ * (n * n)) → F :=
  fun t => A (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).2

/-- The inverse of `flatTuple`. -/
def unflatTuple {ℓ n : ℕ} (v : Fin (ℓ * (n * n)) → F) : Fin ℓ → Matrix (Fin n) (Fin n) F :=
  fun k i j => v (finProdFinEquiv (k, finProdFinEquiv (i, j)))

/-- An `n × n` matrix as a vector of length `n²`, row-major: entry `(i, j)` at position
`j + n·i`. -/
def flatMat {n : ℕ} (X : Matrix (Fin n) (Fin n) F) : Fin (n * n) → F :=
  fun t => X (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

/-- A (possibly randomized, memoryless) matrix oracle `D : (F^{n×n})^ℓ → F^{n×n}`, presented as a
vector oracle through the row-major layout. -/
noncomputable def matOracle {ℓ n : ℕ}
    (D : (Fin ℓ → Matrix (Fin n) (Fin n) F) → PMF (Matrix (Fin n) (Fin n) F)) :
    VecOracle F (ℓ * (n * n)) (n * n) :=
  fun v => (D (unflatTuple v)).map flatMat

/-- `Pr_{A ∼ (F^{n×n})^ℓ}[D(A) = P(A)]`: the success probability of the oracle `D` for `P`, over a
uniform tuple `A` and the randomness of `D`. -/
noncomputable def succProb [Fintype F] [DecidableEq F] {ℓ n : ℕ} (P : MatPolynomial F ℓ)
    (D : (Fin ℓ → Matrix (Fin n) (Fin n) F) → PMF (Matrix (Fin n) (Fin n) F)) : ℝ :=
  ZamirInversion581.Mult.unifMean fun A => (D A (eval P A)).toReal

/-- The input of a reduction with a success-probability parameter (Theorems 3.4 and 3.5): the
matrices `M_1, …, M_ℓ`; the index registers hold `n` and `K = ⌈1/α⌉`. -/
noncomputable def thresholdInput {ℓ n : ℕ} (α : ℝ) (M : Fin ℓ → Matrix (Fin n) (Fin n) F) :
    Config F :=
  initConfig [(n : ℤ), (⌈1 / α⌉₊ : ℤ)] (tupleBlocks M) []

/-- The input of the self-corrector of Corollary 2.12: the matrices `M_1, …, M_ℓ`; the index
register holds `n`. -/
def tupleInput {ℓ n : ℕ} (M : Fin ℓ → Matrix (Fin n) (Fin n) F) : Config F :=
  initConfig [(n : ℤ)] (tupleBlocks M) []

/-- The input of the self-corrector of Lemma 2.11: the vector `x`; the index register holds the
degree bound `d`. -/
def vectorInput {ℓ : ℕ} (d : ℕ) (x : Fin ℓ → F) : Config F :=
  initConfig [(d : ℤ)] [List.ofFn x] []

/-- The input of the verifier of Theorem 2.5: the matrices `A_1, …, A_ℓ`, then `C`, then the
coefficients of `P`; the words of `P` in the index memory; the index registers hold
`n, k, ℓ, s`. -/
def verifierInput {ℓ n : ℕ} (P : MatPolynomial F ℓ) (k : ℕ)
    (A : Fin ℓ → Matrix (Fin n) (Fin n) F) (C : Matrix (Fin n) (Fin n) F) : Config F :=
  initConfig [(n : ℤ), (k : ℤ), (ℓ : ℤ), (size P : ℤ)]
    (tupleBlocks A ++ [matList C, coeffBlock P]) (wordCode P)

/-- The input of Lemma 2.8: the matrices `A_1, …, A_ℓ`, `U_1, …, U_ℓ`, `V_1, …, V_ℓ`, then the
coefficients of `P`; the words of `P` in the index memory; the index registers hold `n, r, ℓ, s`. -/
def shiftInput {ℓ n r : ℕ} (P : MatPolynomial F ℓ) (A : Fin ℓ → Matrix (Fin n) (Fin n) F)
    (U V : Fin ℓ → Matrix (Fin n) (Fin r) F) : Config F :=
  initConfig [(n : ℤ), (r : ℤ), (ℓ : ℤ), (size P : ℤ)]
    (tupleBlocks A ++ tupleBlocks U ++ tupleBlocks V ++ [coeffBlock P]) (wordCode P)

/-- The input of Corollary 2.9: the matrices `A_1, …, A_ℓ`, `U`, `V_1, …, V_ℓ`, then the
coefficients of `P`; the words of `P` in the index memory; the index registers hold `n, r, ℓ, s`. -/
def sharedShiftInput {ℓ n r : ℕ} (P : MatPolynomial F ℓ) (A : Fin ℓ → Matrix (Fin n) (Fin n) F)
    (U : Matrix (Fin n) (Fin r) F) (V : Fin ℓ → Matrix (Fin n) (Fin r) F) : Config F :=
  initConfig [(n : ℤ), (r : ℤ), (ℓ : ℤ), (size P : ℤ)]
    (tupleBlocks A ++ [matList U] ++ tupleBlocks V ++ [coeffBlock P]) (wordCode P)

end LowRankShifts.MatPoly


