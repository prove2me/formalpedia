-- Prove2me | Definitions.Def_LocalConjugacy_Proof_QuaternionAction
-- name    : LocalConjugacy_Proof_QuaternionAction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:31:41.32192+00:00
-- url     : https://prove2.me/theorems/e9b26c16-3000-4a03-82cd-6bd830901ccb
-- title:
--   Transporting the quaternion action to the symmetric group
-- statement:
--   Transport of finite cocycles and their quotient under a domain equivalence, the quaternion action of Mathlib’s symmetric group, and the induced equivalences of semidirect products and matrix groups.
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
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices

/-! Supporting definitions and the structural proofs required by their types and values. -/

section


/-! Transport the explicit dihedral presentation to the draft's symmetric group.
The transport preserves the full cocycle quotient and all Sylow restrictions. -/
namespace LocalConjugacy.Proof

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Precomposition by a group isomorphism is an equivalence of cocycles. -/
def finiteCocycleDomainEquiv {J K N : Type*} [Group J] [Group K] [Group N]
    (a : J →* MulAut N) (e : K ≃* J) :
    FiniteCocycle a ≃ FiniteCocycle (a.comp e.toMonoidHom) where
  toFun f := ⟨fun x => f.val (e x), by
    intro x y
    simpa using f.property (e x) (e y)⟩
  invFun f := ⟨fun x => f.val (e.symm x), by
    intro x y
    simpa using f.property (e.symm x) (e.symm y)⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp

/-- The same coefficient witnesses cohomology before and after domain transport. -/
def finiteH1DomainEquiv {J K N : Type*} [Group J] [Group K] [Group N]
    (a : J →* MulAut N) (e : K ≃* J) :
    FiniteH1 a ≃ FiniteH1 (a.comp e.toMonoidHom) :=
  Quotient.congr (finiteCocycleDomainEquiv a e) (by
    intro f g
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, fun x => hn (e x)⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, fun x => ?_⟩
      change ∀ y, g.val (e y) = n⁻¹ * f.val (e y) * a (e y) n at hn
      simpa only [e.apply_symm_apply] using hn (e.symm x))

/-- The draft's action, expressed on Mathlib's S₃. -/
def quaternionAction : S3 →* MulAut Q8 :=
  LocalConjugacy.QuaternionExample.action.comp dihedralEquiv.symm.toMonoidHom

/-- Changing the presentation of the complement changes neither the group nor
its specified action on the normal quaternion subgroup. -/
def quaternionPresentationEquiv :
    (Q8 ⋊[quaternionAction] S3) ≃* LocalConjugacy.QuaternionExample.G :=
  SemidirectProduct.congr (MulEquiv.refl _) dihedralEquiv.symm (by intro s; rfl)

/-- The concrete GL₂(F₃) identification in the draft's presentation. -/
noncomputable def quaternionGLEquiv :
    (Q8 ⋊[quaternionAction] S3) ≃* GL (Fin 2) (ZMod 3) :=
  quaternionPresentationEquiv.trans QuaternionMatrices.matrixEquiv









end LocalConjugacy.Proof

end


