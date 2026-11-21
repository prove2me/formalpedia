-- Prove2me | Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD
-- name    : InfoLossLAR_RegevSearch_SharedPoolBDD
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T23:25:04.598225+00:00
-- url     : https://prove2.me/theorems/a37a4918-a13f-4803-b542-09348df2faa9
-- title:
--   Bounded-distance decoding with a Gaussian sample pool
-- statement:
--   The decoder receives an integer basis $B$, a positive rational width $R$, a unary precision $k$, one pool of integer coefficient vectors, and a rational query $x$. For a dual lattice point $u$ within distance $\sigma(n)/(2R)$ of $x$, the required readout is the signed integer vector $B^\top u$. The nearby point and its coordinates specify the success event. The circuit receives only the query and public data together with the sample pool.
--
--   The pool has $P(n)$ independent draws from the coefficient law for $B,R$. For each fixed query, average its measurement failure probability over this pool. The basic contract bounds this average by $e(n)+1/(k+1)$ above the public Gaussian smoothing threshold. The coherent-use budget evaluates the same average at precision $[16(t+1)(k+1)]^2$ for a polynomial call bound $t$. It bounds $4t$ times the square root of that average by a negligible residual plus $1/[4(k+1)]$. Both contracts use the same decoding routine for every promised basis, width and query.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Lemmas 3.3, 3.4 and 3.11, pp. 19–20 and 23–24, and Lemma 3.14, pp. 26–27 (2009 full version). This interface specializes the pool and radius to the platform family and records its signed-coordinate encoding and explicit precision budget.

import Definitions.Def_InfoLossLAR_RegevSearch

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSearch
open QAlgorithms.Complexity InfoLossLAR.WorstCase.RegevSketch RegevLWE.GaussConv
open scoped BigOperators Classical

/-- A decoder receives the public basis, Gaussian width, unary accuracy budget, one
fixed pool of integer coefficient vectors, and the rational query. -/
def poolBDDInput {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (pool : Fin m → Fin n → ℤ) (x : Fin n → ℚ) : Str :=
  encPair (encMat encI B) (encPair (encQ R) (encPair (unary k)
    (encPair (encVec (encVec encI) pool) (encVec encQ x))))

/-- Failure on one fixed query, averaging the Born probability over independent ideal
Gaussian coefficient vectors in the one shared input pool. -/
noncomputable def poolBDDFailure (C : MFamily) {n : ℕ} (m : ℕ)
    (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ) (x : Fin n → ℚ) (z : Fin n → ℤ) : ℝ :=
  ∑' pool : Fin m → Fin n → ℤ, (∏ j, coefficientMass B (R : ℝ) (pool j)) *
    outputProb C (poolBDDInput B R k pool x) (fun out => ¬ encVec encI z <+: out)

/-- For each fixed query in the decoding radius, the decoder recovers the signed
coordinates `z = Bᵀu` of the nearby dual point `u`. The failure probability averages
one ideal Gaussian pool and the quantum measurement on that pool. The pool size is a
public polynomial in the dimension, shared by all queries and all accuracy budgets. -/
def SharedPoolBDD (C : MFamily) (poolSize : Polynomial ℕ) (error : ℕ → ℝ)
    (cutoff : ℕ) (S : Set ℕ) : Prop :=
  ∀ n ∈ S, cutoff ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
    ∀ R : ℚ, 0 < R →
      Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ) →
    ∀ (k : ℕ) (x u : Fin n → ℚ) (z : Fin n → ℤ),
      (∀ j, ∑ i, (B i j : ℚ) * u i = (z j : ℚ)) →
      (R : ℝ)^2 * (∑ i, (((x i - u i : ℚ) : ℝ))^2) < (famσ n : ℝ)^2 / 4 →
      poolBDDFailure C (poolSize.eval n) B R k x z ≤ error n + 1 / ((k : ℝ) + 1)


/-- Unary accuracy for each decoder call in a coherent computation with a public
bound on the number of invocations. -/
def poolBDDPrecision (calls budget : ℕ) : ℕ := (16 * (calls+1) * (budget+1))^2

/-- A square-root failure budget for a polynomial number of coherent decoder uses.
The query for each use is fixed before averaging the reference sample pool. -/
def CoherentPoolBDDBudget (C : MFamily) (poolSize : Polynomial ℕ) (cutoff : ℕ)
    (S : Set ℕ) : Prop :=
  ∀ calls : Polynomial ℕ, ∃ residual : ℕ → ℝ, Negligible residual ∧
    ∀ n ∈ S, cutoff ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
    ∀ R : ℚ, 0 < R →
      Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ) →
    ∀ (budget : ℕ) (x u : Fin n → ℚ) (z : Fin n → ℤ),
      (∀ j, ∑ i, (B i j : ℚ) * u i = (z j : ℚ)) →
      (R : ℝ)^2 * (∑ i, (((x i-u i : ℚ) : ℝ))^2) < (famσ n : ℝ)^2 / 4 →
      4 * ((calls.eval n : ℕ) : ℝ) * Real.sqrt (poolBDDFailure C (poolSize.eval n) B R
        (poolBDDPrecision (calls.eval n) budget) x z) ≤
          residual n + 1 / (4 * ((budget : ℝ)+1))

end InfoLossLAR.WorstCase.RegevSearch


