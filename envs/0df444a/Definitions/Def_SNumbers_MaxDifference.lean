-- Prove2me | Definitions.Def_SNumbers_MaxDifference
-- name    : SNumbers_MaxDifference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:21:50.016486+00:00
-- url     : https://prove2.me/theorems/856981cb-8a8c-414a-8c47-d55e7b2445eb
-- title:
--   Max Difference
-- statement:
--   Definitions and structural lemmas for Max Difference, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open ContinuousLinearMap
open scoped Pointwise
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
def detSet (S : X →L[𝕜] Y) (k : ℕ) : Set ℝ :=
  {r | ∃ (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      r = ‖LinearMap.det (B.comp (S.comp A) :
          EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖}
noncomputable def detNumber (S : X →L[𝕜] Y) (k : ℕ) : ℝ :=
  sSup (detSet S k)
section Border
variable {k : ℕ}
noncomputable def borderDom (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
    (lam mu : ℝ) : EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] X :=
  (lam : 𝕜) • (A.comp (projFin (p := 2) (Nat.le_succ k))) +
    (mu : 𝕜) • ((innerSL 𝕜 (EuclideanSpace.single (Fin.last k) (1 : 𝕜))).smulRight x)
noncomputable def borderCod (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (b : Y →L[𝕜] 𝕜) (lam mu : ℝ) : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)) :=
  (lam : 𝕜) • ((padFin (p := 2)).comp B) +
    (mu : 𝕜) • (b.smulRight (EuclideanSpace.single (Fin.last k) (1 : 𝕜)))
variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)
end Border
end SNumbers


