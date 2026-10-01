-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
-- name    : LocalConjugacy_Proof_Counterexamples_Quaternion
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:21:30.365378+00:00
-- url     : https://prove2.me/theorems/1fdc6c61-45e5-43c2-8723-91fc4e10d035
-- title:
--   The quaternion action and its sign cocycle
-- statement:
--   Explicit rotation and reflection automorphisms of $Q_8$, their $D_6$ action, the semidirect product, and the sign cocycle used in the quaternion counterexample in §1.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

/-!
The `Q₈ ⋊ S₃` obstruction from the introduction. We use Mathlib's quaternion
and dihedral groups, with `S₃ = DihedralGroup 3`. The action rotates `i,j,k`
and sends `(i,j,k)` to `(-j,-i,-k)` under a reflection.
All finite checks use kernel-checked `decide`, never `native_decide`.
-/

namespace LocalConjugacy.QuaternionExample

abbrev Q := QuaternionGroup 2
abbrev S := DihedralGroup 3

open QuaternionGroup

def rotate : Q → Q
  | .a i => ![a 0, xa 0, a 2, xa 2] i
  | .xa i => ![xa 3, a 3, xa 1, a 1] i

def reflect : Q → Q
  | .a i => ![a 0, xa 2, a 2, xa 0] i
  | .xa i => ![a 3, xa 3, a 1, xa 1] i

def act : S → Q → Q
  | .r i, x => rotate^[i.val] x
  | .sr i, x => reflect (rotate^[i.val] x)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem act_one : ∀ x : Q, act 1 x = x := by decide
theorem act_mul : ∀ s t : S, ∀ x : Q, act (s * t) x = act s (act t x) := by decide
theorem act_mul_Q : ∀ s : S, ∀ x y : Q, act s (x * y) = act s x * act s y := by decide

def action : S →* MulAut Q where
  toFun s :=
    { toFun := act s
      invFun := act s⁻¹
      left_inv := fun x => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun x => by rw [← act_mul, mul_inv_cancel, act_one]
      map_mul' := act_mul_Q s }
  map_one' := by ext x; exact act_one x
  map_mul' s t := by ext x; exact act_mul s t x

abbrev G := Q ⋊[action] S

/-- The nontrivial central cocycle (sign of the permutation). -/
def signCocycle : S → Q
  | .r _ => 1
  | .sr _ => a 2

def IsCocycle (f : S → Q) : Prop :=
  ∀ s t, f (s * t) = f s * act s (f t)

def Equivalent (f g : S → Q) : Prop :=
  ∃ n : Q, ∀ s, g s = n⁻¹ * f s * act s n

instance (f : S → Q) : Decidable (IsCocycle f) := inferInstanceAs
  (Decidable (∀ s t, f (s * t) = f s * act s (f t)))
instance (f g : S → Q) : Decidable (Equivalent f g) := inferInstanceAs
  (Decidable (∃ n : Q, ∀ s, g s = n⁻¹ * f s * act s n))

theorem sign_isCocycle : IsCocycle signCocycle := by decide






/-- Reconstruction of a cocycle from its values on `r` and `s`. -/
def candidate (a b : Q) : S → Q
  | .r i => ![1, a, a * act (.r 1) a] i
  | .sr i => b * act (.sr 0) (![1, a, a * act (.r 1) a] i)











end LocalConjugacy.QuaternionExample

end LocalConjugacy.Proof

end


