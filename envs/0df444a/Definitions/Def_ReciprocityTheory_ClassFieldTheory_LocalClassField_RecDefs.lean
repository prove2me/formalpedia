-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:46.013451+00:00
-- url     : https://prove2.me/theorems/f81b65c6-08ab-412a-a5b1-27f729c61ccb
-- title:
--   Rec Defs
-- statement:
--   Definitions and structural lemmas for Rec Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecDefs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
abbrev GKab : Type := TopologicalAbelianization (GK p K)
def toAbK : GK p K →* GKab p K := QuotientGroup.mk' _
structure IsAbLK : Prop where
  le : K ≤ L
  fin : FiniteDimensional ℚ_[p] L
  comm : commutator (GK p K) ≤ subG p K L
def normHom : KbarMult p →+ KbarMult p :=
  ∑ᶠ c : GK p K ⧸ subG p K L, (kbarRep p K c.out).toAddMonoidHom
def normSub : AddSubgroup (KbarMult p) := (multOf p L).map (normHom p K L)
def normGrp : Subgroup Kˣ := AddSubgroup.toSubgroup' ((normSub p K L).comap (ofK p K))
def IsArtinK (Art : Kˣ →* GKab p K) : Prop :=
  Continuous Art ∧ Function.Injective Art ∧ DenseRange Art ∧
  (∀ π : Kˣ, vK p K π = 1 → ∀ g : GK p K, toAbK p K g = Art π → IsFrob p K g) ∧
  ∀ L, IsAbLK p K L →
    (∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧ g'⁻¹ * g ∈ subG p K L) ∧
    ∀ (x : Kˣ) (g : GK p K), toAbK p K g = Art x → (g ∈ subG p K L ↔ x ∈ normGrp p K L)
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


