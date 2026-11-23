-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:41.936142+00:00
-- url     : https://prove2.me/theorems/cacb9597-e81f-4086-bab5-0100dd0b6155
-- title:
--   Pull Loc St
-- statement:
--   Definitions and structural lemmas for Pull Loc St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/PullLocSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Matrix
open scoped TensorProduct
def CompG : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ g : HA (AF F) σ J, ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v
def FibInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (h : HA (Ainf F) σ J) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      ∫ X, Φinf (h • X) ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
def FibInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (h : HA (Fv F v) σ J) (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
      ∫ X, Φv (h • X) ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))
def smulHomeo {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  continuous_toFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)
  continuous_invFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)
end PI.VolStabSW


