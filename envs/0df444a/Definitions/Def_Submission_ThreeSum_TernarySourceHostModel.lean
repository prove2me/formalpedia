-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
-- name    : Submission_ThreeSum_TernarySourceHostModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:18:20.406798+00:00
-- url     : https://prove2.me/theorems/5fdedbda-6f58-441c-a8e6-b65912af4e2d
-- title:
--   Ternary Source Host Model
-- statement:
--   Definitions and structural lemmas for Ternary Source Host Model, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}
def records (M NL NR : ℕ) (input dictionary : ℕ → ℤ) : Finset (ℕ × ℕ) :=
  ((range NL).product (range NR)).filter (fun pair => (M : ℤ)∣input pair.1-dictionary pair.2)
def channel (S : Finset (ℕ × ℕ)) (group : ℕ → ℕ) (g : ℕ) : Finset (ℕ × ℕ) :=
  S.filter (fun pair => group pair.2=g)
def physical (S : Finset (ℕ × ℕ)) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (g : ℕ) (R : TritWord N) : ℤ :=
  TernaryWeightedPhysicalSources.histogram (channel S group g)
    (fun pair => enumeration (key pair.2)) (fun pair => weight pair.1) R
end ThreeSum.TernarySourceHostModel


