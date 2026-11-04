-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
-- name    : Submission_ThreeSum_LightMomentDeterminant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:16.120871+00:00
-- url     : https://prove2.me/theorems/3599bfb6-253f-4997-b733-dda49fb705ba
-- title:
--   Light Moment Determinant
-- statement:
--   Definitions and structural lemmas for Light Moment Determinant, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
noncomputable def sumCircuits (es : List Circuit) : Circuit := es.foldr Circuit.add (.literal 0)
noncomputable def prodCircuits (es : List Circuit) : Circuit := es.foldr Circuit.mul (.literal 1)
noncomputable def determinant (d : ℕ) (entry : Fin d → Fin d → Circuit) : Circuit :=
  sumCircuits ((Finset.univ : Finset (Equiv.Perm (Fin d))).toList.map (fun σ =>
    .mul (.literal (Equiv.Perm.sign σ : ℤ))
      (prodCircuits ((Finset.univ : Finset (Fin d)).toList.map (fun i => entry (σ i) i)))))
noncomputable def leading (d : ℕ) : Circuit :=
  determinant d (fun i j => .atom (i.val+j.val+1))
noncomputable def modified (d : ℕ) : Circuit :=
  determinant d (fun i j =>
    .add (.sub (.atom (i.val+j.val+3))
      (.mul (.mul (.literal 2) (.atom 0)) (.atom (i.val+j.val+2))))
      (.mul (.mul (.atom 0) (.atom 0)) (.atom (i.val+j.val+1))))
noncomputable def body (atoms : ℕ → Expr) : ℕ → Stmt
  | 0 => .set 0 (k 0)
  | h+1 => .ite (.eq ((leading (h+1)).compile atoms) (k 0)) (body atoms h)
      (.ite (.eq ((modified (h+1)).compile atoms) (k 0))
        (.set 0 (k 1)) (.set 0 (k 0)))
noncomputable def time (atoms : ℕ → Expr) : ℕ → ℕ
  | 0 => 2
  | h+1 => ((leading (h+1)).compile atoms).cost+3+time atoms h+
      ((modified (h+1)).compile atoms).cost+7
noncomputable def wordBound (U : ℤ) : ℕ → ℤ
  | 0 => 1
  | h+1 => max (wordBound U h) (max ((leading (h+1)).bound U) ((modified (h+1)).bound U))
noncomputable def wordCoefficient : ℕ → ℤ
  | 0 => 1
  | h+1 => wordCoefficient h+(leading (h+1)).coefficient+(modified (h+1)).coefficient
noncomputable def wordDegree : ℕ → ℕ
  | 0 => 0
  | h+1 => wordDegree h+(leading (h+1)).degree+(modified (h+1)).degree
end ThreeSum.LightMomentDeterminant


