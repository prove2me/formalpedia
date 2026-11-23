-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:34.251935+00:00
-- url     : https://prove2.me/theorems/a4d06d02-a801-4972-8333-7e9203500e15
-- title:
--   Norm Mod
-- statement:
--   Definitions and structural lemmas for Norm Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormMod.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
namespace PI.ProdFormulaE
open scoped Classical in

def modF (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    (a : K) : ℝ :=
  if h : a = 0 then 0 else ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ)
section
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
end
def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (t : 𝒪[K]), t ≠ 0 →
      modF K (t : K) * (Nat.card (𝒪[K] ⧸ Ideal.span {t}) : ℝ) = 1
open IsDedekindDomain NumberField in

def CardStep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι → (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ (a : 𝓞 F), a ≠ 0 → ∀ t : 𝒪[K], (t : K) = ι (a : F) →
      Nat.card (𝒪[K] ⧸ Ideal.span {t}) = Ideal.absNorm (p.maxPowDividing (Ideal.span {a}))
end PI.ProdFormulaE


