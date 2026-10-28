-- Prove2me | Definitions.Def_Sensitivity213303_ProfileClosures
-- name    : Sensitivity213303_ProfileClosures
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:33:54.098444+00:00
-- url     : https://prove2.me/theorems/b0fa8f5d-4a80-437b-a121-983a5e6d79f9
-- title:
--   Five conditional sensitivity profiles for nested Boolean families
-- statement:
--   For Boolean functions F_i indexed by an ordered set, nestedness means F_j(x)=true implies F_i(x)=true whenever i≤j. Write U_j(x) for the coordinates whose flip makes F_j true and D_i(x) for those whose flip makes F_i false. A(i,j) bounds |U_j| when F_i is false; B(i,j) bounds |D_i| when F_j is true. M(i,j,k) bounds |D_i| when F_j is true and F_k false; P(i,j,k) bounds |U_k| when F_i is true and F_j false. D(i,j,k,l) bounds |D_i∪U_l| under F_j=true,F_k=false. These predicates give semantic meanings to every numerical profile coordinate.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ProfileClosures; source SHA256 351baf21cf080a3b627e16bfefb7da6dbb6f5cd892ef11e4b13bfdca1a2d3417.

/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Union
namespace OAI.Paper320
end OAI.Paper320


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]

def Nested (F : L → (I → Bool) → Bool) : Prop :=
  ∀ i j, i ≤ j → ∀ x, F j x = true → F i x = true

noncomputable def flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => f (flip x {a}) = b

def ABound (F : L → (I → Bool) → Bool) (i j : L) (v : ℕ) : Prop :=
  ∀ x, F i x = false → (flipsTo (F j) true x).card ≤ v

def BBound (F : L → (I → Bool) → Bool) (i j : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → (flipsTo (F i) false x).card ≤ v

def MBound (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false → (flipsTo (F i) false x).card ≤ v

def PBound (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ) : Prop :=
  ∀ x, F i x = true → F j x = false → (flipsTo (F k) true x).card ≤ v

def DBound (F : L → (I → Bool) → Bool) (i j k l : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false →
    ((flipsTo (F i) false x) ∪ (flipsTo (F l) true x)).card ≤ v



















































end
end ThreeBoundProfiles


