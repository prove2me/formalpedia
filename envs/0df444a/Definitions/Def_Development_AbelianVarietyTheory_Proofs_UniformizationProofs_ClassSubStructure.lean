-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:45.993788+00:00
-- url     : https://prove2.me/theorems/72076d8a-8fc7-4ecf-a971-4aeb115261eb
-- title:
--   Class Sub Structure
-- statement:
--   Definitions and structural lemmas for Class Sub Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClassWeight
abbrev TorChar (X : Type) [AddCommGroup X] (F : Type) [Field F] (N : ℕ) : Subgroup (Multiplicative X →* Fˣ) :=
  (powMonoidHom N : (Multiplicative X →* Fˣ) →* (Multiplicative X →* Fˣ)).ker
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
def evalChar (F : Type) [Field F] (N : ℕ) (α : X) : TorChar X F N →* Fˣ :=
  MonoidHom.mk' (fun τ => τ.1 (Multiplicative.ofAdd α)) fun _ _ => rfl
variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]
def classSub (S : ∀ α, E →ₗ[F] W α) (N : ℕ) (α : X) : Submodule F E where
  carrier := {v | ∀ β, (¬ ∃ mu, β = α + N • mu) → S β v = 0}
  add_mem' := fun {v v'} h h' β hβ => by rw [map_add, h β hβ, h' β hβ, add_zero]
  zero_mem' := fun β _ => map_zero _
  smul_mem' := fun c v h β hβ => by rw [map_smul, h β hβ, smul_zero]
end GlobalTheory.ClassWeight


