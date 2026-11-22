-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:34.20485+00:00
-- url     : https://prove2.me/theorems/ae97be9c-8d39-4fc6-a66a-7961924f34d4
-- title:
--   Length Eq Ker Add Range
-- statement:
--   Definitions and structural lemmas for Length Eq Ker Add Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
namespace IdempotentNormalFormsRhoFacts
section Sel
variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]
lemma mem_sel (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (G : ∀ w, Submodule O (Cw w))
    (Q : Submodule O C) (x : C) :
    x ∈ Q ⊓ ⨅ w ∈ what₂, (G w).comap (res w) ↔ x ∈ Q ∧ ∀ w ∈ what₂, res w x ∈ G w := by
  simp [Submodule.mem_inf, Submodule.mem_iInf]
def relaxMap (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w))
    (Q : Submodule O C) :
    ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)) →ₗ[O]
      ((w : what₂) → (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype)) :=
  LinearMap.pi fun w => (Submodule.mkQ _) ∘ₗ
    ((res w.1 ∘ₗ Submodule.subtype _).codRestrict (F' w.1)
      fun x => ((mem_sel what₂ res F' Q x.1).mp x.2).2 w.1 w.2)
end Sel
end IdempotentNormalFormsRhoFacts
namespace IdempotentNormalFormsRhoFacts
section Sel2
variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]
  (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C)
end Sel2
end IdempotentNormalFormsRhoFacts
namespace IdempotentNormalFormsRhoFacts
end IdempotentNormalFormsRhoFacts
end Formalism.NG


