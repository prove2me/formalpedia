-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebra
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebra
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:04.852659+00:00
-- url     : https://prove2.me/theorems/73d386e8-0a69-415f-a9cf-2ad8a59569c6
-- title:
--   Unit Lemma Local Any Residue Char Of Lie Algebra
-- statement:
--   Definitions and structural lemmas for Unit Lemma Local Any Residue Char Of Lie Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebra.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedBaseChangeLatticeCountEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyOverExtIntegralReductionPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardResidueFieldLocalOrderUnitaryProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnramifiedEmbeddingOfInvolutionAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.UnrAny
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
section Assembly
variable {K K' : UQ}
def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }
end Assembly
end GlobalTheory.UnitLemma.UnrAny


