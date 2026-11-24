-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_WhittakerCovolume_MeasProps
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_WhittakerCovolume_MeasProps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:39.84531+00:00
-- url     : https://prove2.me/theorems/06b45dfe-8a57-4035-92aa-6ffed7f746ee
-- title:
--   Meas Props
-- statement:
--   Definitions and structural lemmas for Meas Props, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/WhittakerCovolume/MeasProps.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.KWhit.MeasP
open HeckeCharacterZeroLocus.SiegelWeilU MeasureTheory
open scoped TensorProduct
def ratHerm (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) :
    AddSubgroup (HermR (AF F) σ n) :=
  AddSubgroup.comap (HermR (AF F) σ n).subtype
    (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom).range
def ratTupA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → AF F ⊗[F] E) :=
  (AddMonoidHom.compLeft (AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin M)) (Fin n)).range
def HermCovol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (n : ℕ) (ν : Measure (HermR (AF F) σ n)), SdHerm F E σ (AF F) ψ n ν →
    ∃ 𝓕, IsAddFundamentalDomain (ratHerm F E σ n) 𝓕 ν ∧ ν 𝓕 = 1
def TupCovol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)),
    SdW F E σ M J (AF F) ψ n μ → ∃ 𝓕, IsAddFundamentalDomain (ratTupA F E n M) 𝓕 μ ∧ μ 𝓕 = 1
end PositivityTheory.SiegelWeilFormula.KWhit.MeasP
end


