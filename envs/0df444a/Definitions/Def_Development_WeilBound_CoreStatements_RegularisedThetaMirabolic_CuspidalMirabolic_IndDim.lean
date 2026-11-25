-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
-- name    : Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:32.872199+00:00
-- url     : https://prove2.me/theorems/5e97be7a-29d2-4d02-8036-626a349f6142
-- title:
--   Ind Dim
-- statement:
--   Definitions and structural lemmas for Ind Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
namespace PositivityTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
abbrev Cos (k : Type) [Field k] [Fintype k] (n : ℕ) : Type := Quotient (QuotientGroup.rightRel (uniSub k n))
def cls (x : mirabSub k n) : Cos k n := Quotient.mk (QuotientGroup.rightRel (uniSub k n)) x
def rep (x : mirabSub k n) : mirabSub k n := (cls n x).out
theorem rep_mem (x : mirabSub k n) : x * (rep n x)⁻¹ ∈ uniSub k n :=
  QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel (uniSub k n)) x)
variable (ψ₀ : AddChar k ℂ)
def psiExt (y : mirabSub k n) : ℂ := by
  classical exact if h : y ∈ uniSub k n then genericChar n ψ₀ ⟨y, h⟩ else 0
def restr : MirabInducedSpace n ψ₀ →ₗ[ℂ] (Cos k n → ℂ) where
  toFun f c := (f : mirabSub k n → ℂ) c.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def extFun (g : Cos k n → ℂ) (x : mirabSub k n) : ℂ := psiExt n ψ₀ (x * (rep n x)⁻¹) * g (cls n x)
end PositivityTheory.Mirab.Dim


