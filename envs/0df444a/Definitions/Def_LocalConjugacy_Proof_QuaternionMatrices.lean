-- Prove2me | Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
-- name    : LocalConjugacy_Proof_QuaternionMatrices
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:27:10.364795+00:00
-- url     : https://prove2.me/theorems/0aa4f5e7-c407-4235-a853-98a8ca144046
-- title:
--   The quaternion example in the general linear group
-- statement:
--   Four explicit matrices over $\mathbb F_3$ representing the quaternion generators and the symmetric-group generators. Kernel-checked multiplication, faithfulness, and coverage certificates give $Q_8\rtimes S_3\cong GL(2,3)$.
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
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion

/-! Supporting definitions and the structural proofs required by their types and values. -/

section


/-!
A concrete matrix representation of the first counterexample.  The four matrices
below generate Q₈ and a complement S₃ in GL₂(F₃). Their multiplication, faithfulness,
and coverage of all invertible matrices are verified by kernel reduction.
-/
namespace LocalConjugacy.Proof
namespace QuaternionMatrices

open LocalConjugacy.QuaternionExample
set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- The generator `i` of Q₈, satisfying `i² = -1`. -/
def matrixI : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 1; 2, 0]
/-- The generator `j` of Q₈, with `j² = -1` and `ij = -ji`. -/
def matrixJ : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 1, 2]
/-- Rotation of the three quaternion axes. -/
def matrixR : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 1; 2, 2]
/-- Reflection implementing the action used by the cocycle calculation. -/
def matrixT : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 2, 2]

/-- Matrix of an element in Mathlib's quaternion presentation. -/
def quaternionMatrix : Q → Matrix (Fin 2) (Fin 2) (ZMod 3)
  | .a i => matrixI ^ i.val
  | .xa i => matrixJ * matrixI ^ i.val

/-- Matrix of a rotation or reflection in the chosen complement. -/
def symmetricMatrix : S → Matrix (Fin 2) (Fin 2) (ZMod 3)
  | .r i => matrixR ^ i.val
  | .sr i => matrixT * matrixR ^ i.val

/-- Matrix of the semidirect-product normal form. -/
def groupMatrix (g : G) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  quaternionMatrix g.left * symmetricMatrix g.right

/-- The finite product enumeration used only in the explicit certificates. -/
instance : Fintype G := Fintype.ofEquiv (Q × S) SemidirectProduct.equivProd.symm

/-- Each of the 48 normal forms has invertible determinant. -/
theorem groupMatrix_det : ∀ g : G, (groupMatrix g).det ≠ 0 := by decide

/-- The chosen matrices obey exactly the specified semidirect-product action. -/
theorem groupMatrix_mul : ∀ g h : G,
    groupMatrix (g * h) = groupMatrix g * groupMatrix h := by decide

/-- No two different normal forms represent the same matrix. -/
theorem groupMatrix_injective : Function.Injective groupMatrix := by
  exact (by decide : ∀ g h : G, groupMatrix g = groupMatrix h → g = h)

/-- Every invertible two-by-two matrix over F₃ occurs among the normal forms. -/
theorem groupMatrix_covers : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3),
    M.det ≠ 0 → ∃ g : G, groupMatrix g = M := by decide

/-- The representation as a homomorphism into Mathlib's general linear group. -/
def matrixHom : G →* GL (Fin 2) (ZMod 3) where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero (groupMatrix g) (groupMatrix_det g)
  map_one' := by apply Units.ext; decide
  map_mul' g h := by apply Units.ext; exact groupMatrix_mul g h

/-- Injectivity and surjectivity are both consequences of the finite certificates. -/
theorem matrixHom_bijective : Function.Bijective matrixHom := by
  constructor
  · intro g h he
    exact groupMatrix_injective (congrArg Units.val he)
  · intro M
    obtain ⟨g, hg⟩ := groupMatrix_covers M.val (Matrix.GeneralLinearGroup.det_ne_zero M)
    exact ⟨g, Units.ext hg⟩

/-- The promised identification Q₈ ⋊ S₃ ≃ GL₂(F₃). -/
noncomputable def matrixEquiv : G ≃* GL (Fin 2) (ZMod 3) :=
  MulEquiv.ofBijective matrixHom matrixHom_bijective

end QuaternionMatrices
end LocalConjugacy.Proof

end


