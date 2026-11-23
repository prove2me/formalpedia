-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:44.938114+00:00
-- url     : https://prove2.me/theorems/4a8b655b-a9d7-4524-b7fe-22cff5b931e8
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical
section Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
def Obox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => OEv (E := E) v
def SplitHyp : Prop :=
  Module.finrank F E = 2 ∧ σ ≠ AlgHom.id F E ∧ ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1
def SdNorm : Prop :=
  (∀ (ι : Type) [Fintype ι] [Nonempty ι], sdE (E := E) ψ v ι = 0) ∨
  ∃ m : ℝ, 0 < m ∧ ∀ (ι : Type) [Fintype ι], (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧
    (sdE (E := E) ψ v ι (Obox (E := E) v ι)).toReal = m ^ Fintype.card ι
def VolZZ : Prop :=
  ∀ (g r : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (m : ℝ),
    SplitHyp σ v → 0 < g → TF ∈ HermR (Fv F v) σ (r + 1) → TF' ∈ HermR (Fv F v) σ (r + 1) →
    (∀ i j, (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) →
    ∀ μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ ((r + 1) * (r + 1)) →
      (μ (ZZTyp σ v g r TF TF')).toReal =
        m ^ ((r + 1) * (r + 1)) * absV v (g : Fv F v) ^ (3 * ((r + 1) * (r + 1))) *
          ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹
def VolU : Prop :=
  ∀ (g r : ℕ) (m : ℝ), SplitHyp σ v → 0 < g →
    ∀ μ : Measure (UIdx r → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ Fintype.card (UIdx r) →
      ((μ.prod μ) (deepCongruenceVolume (E := E) v g r)).toReal =
        ∏ q : UIdx r, (m ^ 2 * absV v (g : Fv F v) ^ 2 *
          (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)
def VolPP : Prop :=
  ∀ (g r T T' : ℕ) (m : ℝ), SplitHyp σ v → 0 < g → (g : ℤ) ∣ ((T : ℤ) - T') →
    ∀ μ : Measure (Unit → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v Unit)).toReal = m →
      ∀ l : Fin (r + 1),
        (μ ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l)).toReal =
          m * absV v (g : Fv F v) ^ 3 * (absV v (alp v r l) ^ 4)⁻¹
def Arith : Prop :=
  ∀ (typed : Prop) (g r : ℕ) (m : ℝ), typed → 0 < g →
    m ^ ((r + 1) * (r + 1)) * absV v (g : Fv F v) ^ (3 * ((r + 1) * (r + 1))) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹) *
        jacS v typed g r =
      (∏ q : UIdx r, (m ^ 2 * absV v (g : Fv F v) ^ 2 *
          (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)) *
        ∏ l : Fin (r + 1), (m * absV v (g : Fv F v) ^ 3 * (absV v (alp v r l) ^ 4)⁻¹)
end Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
end PI.UnitaryGroupMassFormula.LocJacTyp


