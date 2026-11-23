-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:30.753404+00:00
-- url     : https://prove2.me/theorems/77b3240a-af05-438e-be5a-050982af9131
-- title:
--   Nu Ne St
-- statement:
--   Definitions and structural lemmas for Nu Ne St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/NuNeSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
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
def ThetaFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∀ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) → IsAdm F E (fun X => (φ X : ℂ)) →
      ∫⁻ h in 𝓕, ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (AF F) (X : Fin a → Fin M → E))) ∂μ < ⊤
def LamEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → ∃ (lam : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (μ'' : Measure (stabT (AF F) σ J X0)), μ''.IsHaarMeasure ∧ IsCompatT F E σ M J X0 μ μ'' lam ∧
      ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → lam K < ⊤
def FinVolStab : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 _hT =>
  ∀ μ'' : Measure (stabT (AF F) σ J X0), μ''.IsHaarMeasure →
    ∀ 𝓕'' : Set (stabT (AF F) σ J X0),
      IsFundamentalDomain (ratIn F E σ M J (stabT (AF F) σ J X0)) 𝓕'' μ'' → μ'' 𝓕'' < ⊤
def InvStab : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  ∀ μ'' : Measure (stabT (AF F) σ J X0), μ''.IsHaarMeasure → μ''.IsInvInvariant
def AdmCpt : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) → IsAdm F E (fun X => (φ X : ℂ)) →
    ∃ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K ∧ ∃ C : ℝ, ∀ X, φ X ≤ C ∧ (X ∉ K → φ X = 0)
end PI.VolStabW


