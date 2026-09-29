-- Prove2me | Definitions.Def_matrix_completion_svd
-- name    : matrix_completion_svd
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T20:41:46.796425+00:00
-- url     : https://prove2.me/theorems/7ff7527a-092f-466a-aeeb-948c0275b507
-- statement:
--   This definition module provides finite-dimensional SVD data, the sign matrix, tangent/normal geometric predicates, and the coherence assumptions A0 and A1.
--
--   $$
--   M=U\Sigma V^\top,\qquad
--   \operatorname{sgn}(M)=UV^\top,\qquad
--   T=\{UX^\top+YV^\top\}.
--   $$
--
--   Module overview: SVD data and coherence assumptions from Candes-Recht Theorem 1.3.
--
--   Documented declarations:
--   1. Explicit rank-$r$ SVD data for a matrix. We carry the singular vectors as plain coordinate functions so the theorem statement does not depend on extracting an SVD from Mathlib.
--   2. Sign matrix $E = \sum_{k} u_{k} v_{k}^\top$ associated to an SVD.
--   3. Coherence of the span of an orthonormal family, in the coordinate form used by Definition 1.2.
--   4. Assumption A0: both column and row spaces have coherence at most $\mu_{0}$.
--   5. Assumption A1: the sign matrix has uniformly bounded entries.
--   6. The crude A1 parameter forced by A0 via Cauchy-Schwarz in the paper.
--
--   Role in the mission. Key declarations include SVD, signMatrix, coherence, A0, A1, defaultA1Parameter. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_basic

/-!
SVD data and coherence assumptions from Candes-Recht Theorem 1.3.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Explicit rank-`r` SVD data for a matrix.  We carry the singular vectors as
plain coordinate functions so the theorem statement does not depend on extracting
an SVD from Mathlib. -/
structure SVD {n1 n2 : Nat} (M : RealMatrix n1 n2) (r : Nat) where
  sigma : Fin r → Real
  u : Fin r → (Fin n1 → Real)
  v : Fin r → (Fin n2 → Real)
  sigma_pos : ∀ k, 0 < sigma k
  u_orthonormal : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0
  v_orthonormal : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0
  decomp : M = ∑ k, sigma k • Matrix.vecMulVec (u k) (v k)

/-- Sign matrix `E = sum_k u_k v_k^T` associated to an SVD. -/
noncomputable def signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) : RealMatrix n1 n2 :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.v k)

/-- Coherence of the span of an orthonormal family, in the coordinate form used
by Definition 1.2. -/
noncomputable def coherence (N r : Nat) (u : Fin r → (Fin N → Real)) : Real :=
  (N : Real) / r * ⨆ i : Fin N, ∑ k, (u k i) ^ 2

/-- Assumption A0: both column and row spaces have coherence at most `mu0`. -/
def A0 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (mu0 : Real) : Prop :=
  coherence n1 r S.u ≤ mu0 ∧ coherence n2 r S.v ≤ mu0

/-- Assumption A1: the sign matrix has uniformly bounded entries. -/
def A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (mu1 : Real) : Prop :=
  ∀ i j,
    |signMatrix S i j| ≤
      mu1 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))

/-- The crude A1 parameter forced by A0 via Cauchy-Schwarz in the paper. -/
noncomputable def defaultA1Parameter (mu0 : Real) (r : Nat) : Real :=
  mu0 * Real.sqrt (r : Real)

end MatrixCompletion


