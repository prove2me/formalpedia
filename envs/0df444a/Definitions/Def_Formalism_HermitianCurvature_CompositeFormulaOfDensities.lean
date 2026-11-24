-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
-- name    : Formalism_HermitianCurvature_CompositeFormulaOfDensities
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:29:32.341831+00:00
-- url     : https://prove2.me/theorems/5db1a846-a2ec-4dd5-90bc-f2129173f8f8
-- title:
--   Composite Formula Of Densities
-- statement:
--   Definitions and structural lemmas for Composite Formula Of Densities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/CompositeFormulaOfDensities.lean

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
def TopDensMeas {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) : Prop :=
  ∀ (w : List (Letter ℂ S)) (u v : Ix S → RadSp P.k P.r z z' π π'), InK (K (Fin.last P.r)) u →
    InK (K (Fin.last P.r)) v → ∀ c : Fin P.r → ℂ,
      StronglyMeasurable (fun q : Cf P.r 0 × Mt P.k P.r => topDens L st w u v (glue 0 c q.1) (Matrix.of q.2))
def CompositeFormulaOfDensities : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    TopIdent (S := S) P z z' π π' μ L st K l0 → TopDensNonneg (S := S) P z z' π π' L st K l0 →
    SliceIn (S := S) P z z' π π' L st K l0 → StepDens (S := S) P z z' π π' μ L st K l0 →
    TopDensMeas S P z z' π π' μ L st K → CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0
def HerAnalyticE {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) : Prop :=
  AdjTop (S := S) P z z' π π' μ L st K l0 ∧ StepDens (S := S) P z z' π π' μ L st K l0 ∧
    FormInt S P z z' π π' μ L st l0 K ∧ TopDensMeas S P z z' π π' μ L st K
def HerAnalyticEAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    HerAnalyticE S P z z' π π' μ L st l0 (herK S P z z' π π' L st l0 D)
def HerAnalyticCOfE : Prop := HerAnalyticEAll → HerAnalyticCAll
def TopDensMeasAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')), TopDensMeas S P z z' π π' μ L st K
def HerAnalyticF {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) : Prop :=
  AdjTop (S := S) P z z' π π' μ L st K l0 ∧ StepDens (S := S) P z z' π π' μ L st K l0 ∧
    FormInt S P z z' π π' μ L st l0 K
def HerAnalyticFAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    HerAnalyticF S P z z' π π' μ L st l0 (herK S P z z' π π' L st l0 D)
end Formalism.FourierDecayAlt.P5


