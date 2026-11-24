-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
-- name    : Formalism_LocalToGlobal_UnitaryNorms_CharExGen
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:48.083797+00:00
-- url     : https://prove2.me/theorems/858990ec-7082-4c9f-aa7b-e3f3a2a4bf72
-- title:
--   Char Ex Gen
-- statement:
--   Definitions and structural lemmas for Char Ex Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace Formalism.L2.Host
namespace CharEx
variable (L : Type) [Field L] [NumberField L]
def unitIdeles : Subgroup (Ideles L) where
  carrier := {u | ∀ v : HeightOneSpectrum (𝓞 L), Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1}
  one_mem' := fun v => by rw [comp_one]; exact map_one _
  mul_mem' := fun {a b} ha hb v => by
    show Valued.v (((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1
    rw [comp_mul, map_mul, ha v, hb v, one_mul]
  inv_mem' := fun {a} ha v => by
    have h := congrArg Valued.v (comp_mul_inv L a v)
    rw [map_mul, ha v, one_mul, map_one] at h
    exact h
def OpenUnits : Prop := IsOpen (unitIdeles L : Set (Ideles L))
def DivExtC : Prop :=
  ∀ (G : Type) [CommGroup G] (H : Subgroup G) (g : H →* ℂˣ), ∃ g' : G →* ℂˣ, ∀ x : H, g' x = g x
def ClassExp : Prop := ∃ h : ℕ, 0 < h ∧ ∀ x : Ideles L, ∃ k : Lˣ, x ^ h * diagUnits L k ∈ unitIdeles L
variable {L}
end CharEx
end Formalism.L2.Host


