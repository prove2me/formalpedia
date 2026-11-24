-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
-- name    : Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:03.897231+00:00
-- url     : https://prove2.me/theorems/4fde18ca-be7e-4129-be4b-e64e0163197f
-- title:
--   Coeff Iterate Zero
-- statement:
--   Definitions and structural lemmas for Coeff Iterate Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
section Gen
variable {k : Type*} [Field k] {Z B : Type*}
structure Contr (Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)) : Prop where
  noConst : ∀ t, NoConst (Ψ t)
  contr : ∀ (t t' : B → MvPowerSeries Z k) (n : ℕ), NoConst t → NoConst t' →
    (∀ c, OrdGE (n + 1) (t c - t' c)) → ∀ b, OrdGE (n + 2) (Ψ t b - Ψ t' b)
namespace Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
def fixPt (_H : Contr Ψ) : B → MvPowerSeries Z k := fun c A => coeff A (Ψ^[A.degree] 0 c)
end Contr
end Gen
section Main
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}
namespace Sys
variable (S : Sys X)
def Mt : Matrix I I C := Matrix.of S.tan
def Rr (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) : C :=
  ∑ s ∈ Finset.range μ.degree, ∑ c : I, S.al c (s + 1) x * coeff μ (t c ^ (V.l ^ (s + 1)))
def dl (x : I) (μ : I →₀ ℕ) : C := if μ = Finsupp.single x 1 then 1 else 0
def Ps (t : I → MvPowerSeries I C) : I → MvPowerSeries I C := fun c μ =>
  Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c
end Sys
end Main
end Formalism.L2.FormalSeriesBounds


