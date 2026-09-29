-- Prove2me | Definitions.Def_matrix_completion_basic
-- name    : matrix_completion_basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T20:41:31.745246+00:00
-- url     : https://prove2.me/theorems/b3ad9246-4bd8-4d51-a960-33630adc8208
-- statement:
--   This definition module provides the fixed-cardinality observation model, the nuclear-norm objective, agreement on observed entries, unique minimizers, and the recovery probability used in the final theorem.
--
--   $$
--   \operatorname{successProb}(m,M)
--   =\mathbb P_{\Omega:\ |\Omega|=m}
--   \bigl(M\text{ is the unique nuclear-norm minimizer subject to }P_\Omega X=P_\Omega M\bigr).
--   $$
--
--   Module overview: Basic objects for exact matrix completion by nuclear-norm minimization. This file is intentionally statement-level infrastructure: it contains only the optimization objective, the fixed-cardinality observation model, and the success predicate for the convex program.
--
--   Documented declarations:
--   1. Real matrices with concrete finite row and column types.
--   2. Nuclear norm $\lVert X\rVert_\,$, defined as the sum of the singular values of the associated Euclidean linear map.
--   3. $X$ agrees with $M$ on the observed entry set.
--   4. $M$ is the unique feasible minimizer of the nuclear-norm completion program.
--   5. Uniform probability, over all size-$m$ observation sets, that the completion program recovers $M$ uniquely.
--
--   Role in the mission. Key declarations include RealMatrix, nuclearNorm, AgreesOn, IsUniqueMinimizer, successProb. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

/-!
Basic objects for exact matrix completion by nuclear-norm minimization.

This file is intentionally statement-level infrastructure: it contains only the
optimization objective, the fixed-cardinality observation model, and the success
predicate for the convex program.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Finset

/-- Real matrices with concrete finite row and column types. -/
abbrev RealMatrix (n1 n2 : Nat) := Matrix (Fin n1) (Fin n2) Real

/-- Nuclear norm `||X||_*`, defined as the sum of the singular values of the
associated Euclidean linear map. -/
noncomputable def nuclearNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  (Matrix.toEuclideanLin X).singularValues.sum (fun _ x => x)

/-- `X` agrees with `M` on the observed entry set. -/
def AgreesOn {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (X M : RealMatrix n1 n2) : Prop :=
  ∀ p ∈ Omega, X p.1 p.2 = M p.1 p.2

/-- `M` is the unique feasible minimizer of the nuclear-norm completion program. -/
def IsUniqueMinimizer {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (M : RealMatrix n1 n2) : Prop :=
  ∀ X : RealMatrix n1 n2,
    AgreesOn Omega X M → X ≠ M → nuclearNorm M < nuclearNorm X

/-- Uniform probability, over all size-`m` observation sets, that the completion
program recovers `M` uniquely. -/
noncomputable def successProb {n1 n2 : Nat} (m : Nat) (M : RealMatrix n1 n2) :
    Real :=
  let sampleSpace := Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))
  ((sampleSpace.filter (fun Omega => IsUniqueMinimizer Omega M)).card : Real) /
    sampleSpace.card

end MatrixCompletion


