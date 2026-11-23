-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:56.276419+00:00
-- url     : https://prove2.me/theorems/2276ff7d-56b7-4a97-8f26-e6ca8685ee37
-- title:
--   Sd Uniq
-- statement:
--   Definitions and structural lemmas for Sd Uniq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdUniq.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
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
namespace SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
def TestEx {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  ∃ Φ : V → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ ∧ ∃ z, Φ (-z) ≠ 0
def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}
section Lattice
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
end Lattice
def AnnAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (χ : V → V → ℂ) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsClosed (ann χ L) ∧
    ∃ K, IsCompact K ∧ ann χ L ⊆ K
section Triv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
end Triv
section Nontriv
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K
end Nontriv
section Add
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
end Add
section ContY
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]
end ContY
end SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW
def SdTestInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ →
      TestEx μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))) ∧
    (∀ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν →
      TestEx ν (fun S T => psiInf F ψ (pairHerm (Ainf F) σ a S T)))
def SdTestV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ →
      TestEx μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) ∧
    (∀ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν →
      TestEx ν (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T)))
def AnnV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    AnnAt (V := Fin a → Fin M → Fv F v ⊗[F] E) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
    AnnAt (V := HermR (Fv F v) σ a) (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T))
def DualLatV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F),
    DualAt v (BR (Fv F v) σ J (n := a)) ∧ DualAt v (pairHerm (Fv F v) σ a)
end PI.VolStabW


