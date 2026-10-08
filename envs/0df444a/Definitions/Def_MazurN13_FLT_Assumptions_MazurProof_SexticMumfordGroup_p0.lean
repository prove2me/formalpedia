-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordGroup_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordGroup_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:02:12.902231+00:00
-- url     : https://prove2.me/theorems/7905860d-a96e-4bae-b2eb-40db3cadaaa2
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordGroup source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordGroup

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordGroup
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticOrientedPic_p0

set_option autoImplicit false




/-!
# The Mumford group law from oriented Picard normal forms

Given unique balanced Mumford representatives of the oriented Picard classes,
transport the ambient abelian group structure to those representatives.
-/

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

class NormalFormData (O : outParam (InfinityOrder M)) : Prop where
  existsUnique : ∀ c : ConcretePic M O,
    ∃! D : Mumford M, classOf M O D = c

def normalize [NormalFormData M O] (c : ConcretePic M O) : Mumford M :=
  Classical.choose (NormalFormData.existsUnique c)

@[simp]
theorem classOf_normalize [NormalFormData M O] (c : ConcretePic M O) :
    classOf M O (normalize M O c) = c :=
  (Classical.choose_spec (NormalFormData.existsUnique c)).1

theorem normalize_eq_of_class [NormalFormData M O]
    (c : ConcretePic M O) (D : Mumford M) (hD : classOf M O D = c) :
    normalize M O c = D := by
  exact ((Classical.choose_spec (NormalFormData.existsUnique c)).2 D hD).symm

theorem classOf_injective [NormalFormData M O] :
    Function.Injective (classOf M O) := by
  intro D E hDE
  have hD : normalize M O (classOf M O E) = D :=
    normalize_eq_of_class M O (classOf M O E) D hDE
  have hE : normalize M O (classOf M O E) = E :=
    normalize_eq_of_class M O (classOf M O E) E rfl
  exact hD.symm.trans hE

def normalFormEquiv [NormalFormData M O] : Mumford M ≃ ConcretePic M O where
  toFun := classOf M O
  invFun := normalize M O
  left_inv D := by
    exact normalize_eq_of_class M O (classOf M O D) D rfl
  right_inv := classOf_normalize M O

/-- The group law is inherited from the oriented Picard group.  The
orientation in `NormalFormData` is an output parameter, so this instance is
selected only after the oriented normal-form data have been fixed. -/
noncomputable instance instAddCommGroupMumford [NormalFormData M O] :
    AddCommGroup (Mumford M) :=
  Equiv.addCommGroup (normalFormEquiv M O)

def classEquiv [NormalFormData M O] : Mumford M ≃+ ConcretePic M O :=
  Equiv.addEquiv (normalFormEquiv M O)

@[simp]
theorem classEquiv_apply [NormalFormData M O] (D : Mumford M) :
    classEquiv M O D = classOf M O D := by
  rfl

@[simp]
theorem classOf_add [NormalFormData M O] (D E : Mumford M) :
    classOf M O (D + E) = classOf M O D + classOf M O E := by
  simpa only [classEquiv_apply] using (classEquiv M O).map_add D E

@[simp]
theorem classOf_neg [NormalFormData M O] (D : Mumford M) :
    classOf M O (-D) = -classOf M O D := by
  simpa only [classEquiv_apply] using (classEquiv M O).map_neg D

@[simp]
theorem classOf_nsmul [NormalFormData M O] (n : ℕ) (D : Mumford M) :
    classOf M O (n • D) = n • classOf M O D := by
  simpa only [classEquiv_apply] using map_nsmul (classEquiv M O) n D

theorem group_zero_eq_balanced_zero [NormalFormData M O] :
    (0 : Mumford M) = zero M := by
  apply classOf_injective M O
  calc
    classOf M O 0 = classEquiv M O 0 := (classEquiv_apply M O 0).symm
    _ = 0 := map_zero (classEquiv M O)
    _ = classOf M O (zero M) := (classOf_zero M O).symm

end

end MazurProof.SexticMumford


