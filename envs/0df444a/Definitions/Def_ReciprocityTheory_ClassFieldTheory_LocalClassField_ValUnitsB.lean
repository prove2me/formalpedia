-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:28.105203+00:00
-- url     : https://prove2.me/theorems/a92b850c-37f1-49b3-a077-50dd56d46f23
-- title:
--   Val Units B
-- statement:
--   Definitions and structural lemmas for Val Units B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
def divHom (e : ℕ) : ℤ →+ ℝ := zmultiplesHom ℝ ((e : ℝ)⁻¹)
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
def pUnit : KbarMult p :=
  Additive.ofMul (Units.mk0 (p : PadicAlgCl p) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
def unitOf (x : multOf p K) : Kˣ :=
  Units.mk0 ⟨((Additive.toMul x.1 : (PadicAlgCl p)ˣ) : PadicAlgCl p), x.2⟩
    (fun h => (Additive.toMul x.1 : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h))
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


