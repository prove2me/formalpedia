-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:12.080175+00:00
-- url     : https://prove2.me/theorems/3c165759-42cb-4ba3-ab6a-c4b9446ed192
-- title:
--   Loc Dens St
-- statement:
--   Definitions and structural lemmas for Loc Dens St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoNuFin
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
  Filter
open scoped TensorProduct
def qV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Nat.card (𝓞 F ⧸ v.asIdeal) : ℝ)
def QvSum : Prop := ∀ (F : Type) [Field F] [NumberField F],
  Summable fun v : HeightOneSpectrum (𝓞 F) => (qV v)⁻¹ ^ 2
def ArchPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∃ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf ∧ HasCompactSupport Φinf ∧
      ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) ≠ 0
def LocPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∃ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv ∧
      ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) ≠ 0
def DensAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ‖∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) - 1‖ ≤
      C * (qV v)⁻¹ ^ 2
end PI.VolStabSW


