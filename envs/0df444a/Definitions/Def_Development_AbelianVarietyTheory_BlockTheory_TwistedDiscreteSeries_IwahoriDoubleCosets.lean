-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:00.867508+00:00
-- url     : https://prove2.me/theorems/2dfee3b1-7a0d-44f8-b6f4-72275396d33c
-- title:
--   Iwahori Double Cosets
-- statement:
--   Definitions and structural lemmas for Iwahori Double Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
section General
variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
def IsIntegralOp (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ (v : V) (l : Module.Dual ℂ V),
    Integrable (fun g => f g * l (π g v)) μ ∧ l (A v) = ∫ g, f g * l (π g v) ∂μ
def HasFinTrace (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (LinearMap.range A) ∧
    LinearMap.trace ℂ (LinearMap.range A)
      (A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        fun v _ => LinearMap.mem_range_self A v) = c
def HasTrace (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (c : ℂ) : Prop :=
  ∃ A : V →ₗ[ℂ] V, IsIntegralOp μ π f A ∧ HasFinTrace A c
end General
section Local
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
def unipO : Subgroup (GL n k) := unipB k n ⊓ KO k n
def unipLowerOne : Subgroup (GL n k) := unipBLower k n ⊓ KOne k n
variable {k n}
def Contracts (t : n → kˣ) : Prop :=
  (∀ u ∈ unipO k n, diagT k n t * u * (diagT k n t)⁻¹ ∈ unipO k n) ∧
    ∀ u ∈ unipLowerOne k n, (diagT k n t)⁻¹ * u * diagT k n t ∈ unipLowerOne k n
example : Contracts (1 : n → kˣ) := ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩
def deltaB (t : n → kˣ) : ℝ := ∏ i, ∏ j with i < j, nabs k (t i / t j)
def iwahoriCoset (t : n → kˣ) : Set (GL n k) :=
  {g | ∃ a ∈ iwahori k n, ∃ b ∈ iwahori k n, g = a * diagT k n t * b}
def cosetInd (t : n → kˣ) : GL n k → ℂ := (iwahoriCoset t).indicator fun _ => 1
variable {V : Type} [AddCommGroup V] [Module ℂ V]
open scoped Classical in

def IsExponents (π : Representation ℂ (GL n k) V) (E : Multiset ((n → kˣ) →* ℂˣ)) : Prop :=
  (∀ χ ∈ E, ∀ s ∈ torusO k n, χ s = 1) ∧ ∀ χ, (E.count χ : ℕ∞) = expMult π χ
variable (k n)
def DominantContracts : Prop :=
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ a : n → ℤ, Antitone a → Contracts fun i => ϖ ^ a i
def TraceFormula : Prop :=
  ∀ [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π →
    FiniteDimensional ℂ (fixed (jacBU π) (torusO k n)) ∧
    (∀ t : n → kˣ, Contracts t →
      HasTrace μ π (cosetInd t)
        ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
          LinearMap.trace ℂ (fixed (jacBU π) (torusO k n)) (jacBUFixed π t))) ∧
    ∃ E : Multiset ((n → kˣ) →* ℂˣ), IsExponents π E ∧
      ∀ t : n → kˣ, Contracts t →
        HasTrace μ π (cosetInd t)
          ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
            (E.map fun χ => (χ t : ℂ)).sum)
end Local
def IwahoriTrace : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ),
    DominantContracts k (Fin r) ∧ TraceFormula k (Fin r)
def IwahoriTraceOfBorelCasselman : Prop := GlobalTheory.Published.BorelCasselman → IwahoriTrace
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets


