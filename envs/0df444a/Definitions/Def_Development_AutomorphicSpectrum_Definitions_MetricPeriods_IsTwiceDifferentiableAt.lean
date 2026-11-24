-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:28.248833+00:00
-- url     : https://prove2.me/theorems/8b9c2481-6a58-4435-875a-0932af1414ce
-- title:
--   Is Twice Differentiable At
-- statement:
--   Definitions and structural lemmas for Is Twice Differentiable At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/IsTwiceDifferentiableAt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_PairRelationOfScaledRatio
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_InFlagDomainOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory
def SamePot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P Q : LocPot X) : Prop :=
  ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
    ∀ y ∈ V, P.φ x y - Q.φ x y = (G y).re
def sumPot {X : Type} [TopologicalSpace X] {σ : Type} [Fintype σ] (c : σ → ℝ) (P : σ → LocPot X) : LocPot X where
  U x := ⋂ a, (P a).U x
  isOpen_U x := isOpen_iInter_of_finite fun a => (P a).isOpen_U x
  mem_U x := Set.mem_iInter.2 fun a => (P a).mem_U x
  φ x y := ∑ a, c a * (P a).φ x y
structure AnSys (e : ℕ) (σ : Type) where

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  Θ : LocPot X

  L : LocPot X

  s : X → X → ℂ

  nb : ℕ

  m : Fin nb → ℕ

  W : Fin nb → Set X
  potΘ : IsPotential A Θ
  posΘ : IsPosPot A Θ
  potL : IsPotential A L
  sec : IsSection A L s
  snc : IsSNC A L s m W
  norm_le : ∀ y, logNormSec L s y ≤ 0

  th : σ → LocPot X

  ph : σ → X → ℝ

  phT : σ → ℝ → X → ℝ

  C₅ : ℝ

  C : ℝ

  t₀ : ℝ
  sing : ∀ a, IsSingWeight A L s (th a) (ph a) C₅
  reg : ∀ a, IsRegFamily A Θ L s (th a) (ph a) (phT a) C t₀
  c2 : ∀ a, IsRegFamilyC2 A s (ph a) (phT a)
attribute [instance] AnSys.top AnSys.compact AnSys.t2
namespace AnSys
variable {e : ℕ} {σ : Type} (S : AnSys e σ)
def open' : Set S.X := (bdry S.s)ᶜ
def potT (a : σ) (t : ℝ) : LocPot S.X := S.th a + LocPot.ofFun (S.phT a t)
def potH (a : σ) : LocPot S.X := S.th a + LocPot.ofFun (S.ph a)
def degNum (w : Fin e → σ) : ℝ := mInt S.A (fun j => S.th (w j)) fun _ => 1
def degPoly [Fintype σ] : MvPolynomial σ ℝ := formPoly e S.degNum
def comap {σ' : Type} (f : σ' → σ) : AnSys e σ' :=
  { S with
    th := fun a => S.th (f a), ph := fun a => S.ph (f a), phT := fun a => S.phT (f a)
    sing := fun a => S.sing (f a), reg := fun a => S.reg (f a), c2 := fun a => S.c2 (f a) }
end AnSys
section Period
variable {e : ℕ} {X : Type} [TopologicalSpace X] {Ψ : Type} {N : ℕ}
def IsPeriodChart (A : FinHolAtlas e X) (j : ℕ) (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X)
    (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsOpen V ∧ x ∈ V ∧ (∀ τ a b, A.HoloOn V fun y => g τ y a b) ∧ (∀ τ, ∀ y ∈ V, InFlagDomain N j (g τ y)) ∧
    ∀ p : Ψ × Fin N, ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, (pot p).φ x y = stepPot N j p.2 (g p.1 y) + (G y).re
def IsFlagImmersionAt (A : FinHolAtlas e X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ) (x : X) : Prop :=
  ∀ k, x ∈ (A.chart k).source → ∀ v : Fin e → ℂ,
    (∀ τ, ((g τ x)⁻¹ * Matrix.of fun a b =>
        fderiv ℂ (fun z => g τ ((A.chart k).symm z) a b) (A.chart k x) v).BlockTriangular id) → v = 0
def IsUniformised (A : FinHolAtlas e X) (U : Set X) (j : ℕ) (pot : Ψ × Fin N → LocPot X) : Prop :=
  (∀ x ∈ U, ∃ V g, IsPeriodChart A j pot x V g) ∧
    ∃ x ∈ U, ∃ V g, IsPeriodChart A j pot x V g ∧ IsFlagImmersionAt A g x
end Period
section Param
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def IsNull (A : FinHolAtlas e X) (N : Set X) : Prop :=
  ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) = 0
def IsParam (A : FinHolAtlas e X) (V : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) : Prop :=
  IsOpen V ∧ ContinuousOn Φ V ∧ Set.InjOn Φ V ∧
    ∀ j, AnalyticOnNhd ℂ (A.chart j ∘ Φ) (V ∩ Φ ⁻¹' (A.chart j).source)
def IsParamCover (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ)) (Φ : ℕ → (Fin e → ℂ) → X) : Prop :=
  (∀ n, IsParam A (V n) (Φ n)) ∧ (∀ n, MeasurableSet (B n) ∧ B n ⊆ V n) ∧
    (Pairwise fun n n' => Disjoint (Φ n '' B n) (Φ n' '' B n')) ∧ IsNull A (⋃ n, Φ n '' B n)ᶜ
def paramDens (P : Fin e → LocPot X) (Φ : (Fin e → ℂ) → X) (z : Fin e → ℂ) : ℝ :=
  maDens (fun i z' => (P i).φ (Φ z) (Φ z')) z
def IsTwiceDifferentiableAt (A : FinHolAtlas e X) (P : LocPot X) (x : X) : Prop :=
  ∀ j, x ∈ (A.chart j).source → ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) (A.chart j x)
end Param
end GlobalTheory.CompanionTheory.Ar.PB


