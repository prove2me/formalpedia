-- Prove2me | Definitions.Def_godel_modal
-- name    : godel_modal
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T22:35:42.578974+00:00
-- url     : https://prove2.me/theorems/79bfe73c-44ef-4519-a288-72d6cf842b5a
-- title:
--   Shallow embedding of quantified modal logic
-- statement:
--   Worlds, sentences, properties, the modal connectives $\Box$ and $\Diamond$, pointwise negation, symmetry of the accessibility relation, and the universal relation. The embedding is shallow: a modal sentence is a predicate on worlds and a property is a predicate on individuals and worlds, so extensions may vary world to world. Nothing here is specific to Gödel's argument.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Modal.lean#L20-L57

namespace Godel

universe u v

abbrev Sentence (W : Type u) : Type u := W → Prop

abbrev Property (I : Type v) (W : Type u) : Type (max u v) := I → W → Prop

variable {W : Type u} {I : Type v}

def pneg (φ : Property I W) : Property I W := fun x w => ¬ φ x w

def box (r : W → W → Prop) (p : Sentence W) : Sentence W :=
  fun w => ∀ v, r w v → p v

def dia (r : W → W → Prop) (p : Sentence W) : Sentence W :=
  fun w => ∃ v, r w v ∧ p v

def Symm (r : W → W → Prop) : Prop := ∀ w v, r w v → r v w

def univ : W → W → Prop := fun _ _ => True

end Godel


