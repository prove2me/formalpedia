-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:28:05.418699+00:00
-- url     : https://prove2.me/theorems/8b1b0555-fad8-4416-8942-58d2fc0a12d3
-- title:
--   Length Eps Img Eq Add
-- statement:
--   Definitions and structural lemmas for Length Eps Img Eq Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEpsImgEqAdd.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.NG
universe u
section LenEpsAux
variable {O OO : Type*} [CommRing O] [Ring OO] [Algebra O OO]
lemma mem_epsImg_iff {M : Type*} [AddCommGroup M] [Module OO M] [Module O M]
    [IsScalarTower O OO M] (ε : OO) (x : M) :
    x ∈ epsImg O (M := M) ε ↔ ∃ y : M, ε • y = x := by
  simp [epsImg]
def epsMap {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A] [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) : epsImg O (M := A) ε →ₗ[O] epsImg O (M := B) ε :=
  LinearMap.restrict (φ.restrictScalars O) (fun x hx => by
    rw [mem_epsImg_iff] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨φ y, by simp⟩)
end LenEpsAux
end Formalism.NG


