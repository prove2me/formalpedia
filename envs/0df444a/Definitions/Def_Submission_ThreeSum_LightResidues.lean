-- Prove2me | Definitions.Def_Submission_ThreeSum_LightResidues
-- name    : Submission_ThreeSum_LightResidues
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:02.237313+00:00
-- url     : https://prove2.me/theorems/69a78e7c-2ad5-4ddf-b112-0ba8c9a46f76
-- title:
--   Light Residues
-- statement:
--   Definitions and structural lemmas for Light Residues, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidues.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def residue (p : ℕ) (c x : ℤ) : ℕ := ((c * x) % (p : ℤ)).toNat
def residuesBody (pEmod : ℕ) : Stmt :=
  .for 6 (v 2) (
    .call pEmod [v 5 *' M (v 0 +' v 6), v 3, v 4] 7 ;;
    .store (v 1 +' v 6) (v 7))
def residueBudget (U : ℕ) : ℕ := 43 * (Nat.log 2 (U + 1) + 1) + 34
def residuesTime (n U : ℕ) : ℕ := n * (residueBudget U + 30) + 6
def Inv (μ : ℕ → ℤ) (src dst n p work : ℕ) (c : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, n, p, work, c, i, r], μ'⟩ ∧
    (∀ j < i, μ' (dst + j) = (residue p c (μ (src + j)) : ℤ)) ∧
    KeptBut μ μ' work dst n
end ThreeSum.LightResidues


