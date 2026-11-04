-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionBackendLayout
-- name    : Submission_ThreeSum_LightExtensionBackendLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:53:45.203193+00:00
-- url     : https://prove2.me/theorems/bc8851ed-b802-40c4-ba2e-8f810ce532ce
-- title:
--   Light Extension Backend Layout
-- statement:
--   Definitions and structural lemmas for Light Extension Backend Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendLayout.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
set_option autoImplicit false
namespace ThreeSum.LightExtensionBackendLayout
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
def target (base d : ℕ) := base+2*d+1
def ctx (base d : ℕ) := target base d+2*d
def table (base d : ℕ) := ctx base d+10
def logical (base d q : ℕ) := table base d+q*q
def physical (base d q J : ℕ) := logical base d q+q*q*(J+2)
def a (base d q J : ℕ) := physical base d q J+q*q*(J+2)
def b (base d q J : ℕ) := a base d q J+d
def h (base d q J : ℕ) := b base d q J+d
def r (base d q J : ℕ) := h base d q J+d
def prod (base d q J : ℕ) := r base d q J+2*d
def sum (base d q J : ℕ) := prod base d q J+2*d
def factor (base d p q J : ℕ) : LightExtensionFactorPredicate.Layout where
  p := p
  dim := d
  degree := 0
  powers := base
  target := target base d
  left := a base d q J
  right := a base d q J+2*d
def params (d p q J : ℕ) := d+p+q+J+2
def reserve (d p q J : ℕ) := 100000000*(params d p q J)^6
def args (base d p q J : ℕ) : List ℤ :=
  [p,d,q,base,target base d,ctx base d,a base d q J,a base d q J+2*d,
    ctx base d,table base d,logical base d q,physical base d q J,
    a base d q J,b base d q J,h base d q J,r base d q J,prod base d q J,sum base d q J,J]
variable {lim : Limits}
end ThreeSum.LightExtensionBackendLayout


