-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.925013+00:00
-- url     : https://prove2.me/theorems/85256b4c-e30b-4654-9b81-e2918472a8dd
-- title:
--   Prod One Sub Primitive Roots
-- statement:
--   Definitions and structural lemmas for Prod One Sub Primitive Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_primitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.N.PreambleDegrees.Loc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial
variable {l : ℕ} [Fact l.Prime]
instance enoughRoots (i : ℕ) : HasEnoughRootsOfUnity (Om l) (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  infer_instance
variable (l)
theorem exists_root_ne_one : ∃ z : Om l, z ^ l = 1 ∧ z ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ 1)
  rw [pow_one] at hζ
  exact ⟨ζ, hζ.pow_eq_one, hζ.ne_one (Fact.out : l.Prime).one_lt⟩
theorem exists_root (x : Om l) : ∃ z : Om l, z ^ l = x := by
  exact IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos
def ζQ : ℕ → Om l
  | 0 => 1
  | 1 => (exists_root_ne_one l).choose
  | (m + 2) => (exists_root l (ζQ (m + 1))).choose
variable {l}
abbrev Q0 (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (Om l) := ⊥
def ofGQ (g : GQ l) : Neutral.B1.GK l (Q0 l) :=
  { g.toRingEquiv with
    commutes' := fun r => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 r.2
      change g (r : Om l) = r
      rw [← ha]
      exact g.commutes a }
section Irr
variable {F : IntermediateField ℚ_[l] (Om l)}
end Irr
end Formalism.MainNotions.N.PreambleDegrees.Loc


