-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_IsInfEmb
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_IsInfEmb
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:27.140496+00:00
-- url     : https://prove2.me/theorems/d0c3151f-f273-5f18-8345-48fdf33b3641
-- title:
--   Is Inf Emb
-- statement:
--   Definitions and structural lemmas for Is Inf Emb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/IsInfEmb.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_InstTopologicalSpaceHA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcS.MainNotions.StandardLattice
open NumberField HcS.BasicNotions Finset
open scoped ENNReal
section SW
open HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
end SW
section Vol
open HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def infMat (θ : Ainf F ⊗[F] E →+* ℂ) (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) ℂ :=
  (((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))).map θ
def IsInfEmb (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ) : Prop :=
  (∀ x : E, θ ((1 : Ainf F) ⊗ₜ[F] x) = τ x) ∧ Continuous fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))
end Vol
section DS
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
end DS
section Fam
end Fam
end HcS.MainNotions.StandardLattice


