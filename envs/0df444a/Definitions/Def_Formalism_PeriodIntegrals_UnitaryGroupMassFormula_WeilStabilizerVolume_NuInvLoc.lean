-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:28.281427+00:00
-- url     : https://prove2.me/theorems/179c5160-a2b8-4378-a8c2-a1eaf9ef6f5a
-- title:
--   Nu Inv Loc
-- statement:
--   Definitions and structural lemmas for Nu Inv Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/NuInvLoc.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
def GramPres : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ (g : HA (AF F) σ J) (X : Fin a → Fin M → AF F ⊗[F] E),
    gramR (AF F) σ J (g • X) = gramR (AF F) σ J X
def PullLoc : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (g : HA (AF F) σ J) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    ∃ (Φinf' : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf' : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv' : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf' ∧ HasCompactSupport Φinf' ∧ IsPureFin b Φf' Φv' ∧
      IsProdInfFin (fun X => Φ (g • X)) Φinf' Φf' ∧
      (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
        ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
        ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
        ∫ X, Φinf' X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
        ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
        ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
        IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
          {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
        ∫ X, Φv' v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)))
end PI.VolStabW


