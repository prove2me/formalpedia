-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:59.568507+00:00
-- url     : https://prove2.me/theorems/8a9b4dfa-9e39-42fb-94b0-f90763280010
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
section Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
def Obox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => OEv (E := E) v
def SdNormO : Prop :=
  (∀ (ι : Type) [Fintype ι] [Nonempty ι], sdE (E := E) ψ v ι = 0) ∨
  ∃ m : ℝ, 0 < m ∧ ∀ (ι : Type) [Fintype ι], (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧
    (sdE (E := E) ψ v ι (Obox (E := E) v ι)).toReal = m ^ Fintype.card ι
def VolZZO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ ((r + 1) * (r + 1)) →
      (μ (ZZOrd (E := E) v r)).toReal =
        m ^ ((r + 1) * (r + 1)) *
          ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹
def VolUO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (UIdx r → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ Fintype.card (UIdx r) →
      ((μ.prod μ) (localVolumeOrdinary (E := E) v r)).toReal =
        ∏ q : UIdx r, (m ^ 2 * (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)
def VolPO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (Unit → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v Unit)).toReal = m →
      ∀ l : Fin (r + 1),
        (μ ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPOrd (E := E) v r l)).toReal =
          m * (absV v (alp v r l) ^ 4)⁻¹
def ArithO : Prop :=
  ∀ (typed : Prop) (g r : ℕ) (m : ℝ), ¬ typed →
    m ^ ((r + 1) * (r + 1)) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹) *
        jacS v typed g r =
      (∏ q : UIdx r, (m ^ 2 * (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)) *
        ∏ l : Fin (r + 1), (m * (absV v (alp v r l) ^ 4)⁻¹)
end Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
end PI.LocJacOrd.W


