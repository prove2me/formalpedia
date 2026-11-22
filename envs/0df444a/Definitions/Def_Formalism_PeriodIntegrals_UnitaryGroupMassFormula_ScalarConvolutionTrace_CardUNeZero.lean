-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:38.643769+00:00
-- url     : https://prove2.me/theorems/7f59f0d5-713c-4b2b-ac32-f4b3a8c47777
-- title:
--   Card UNe Zero
-- statement:
--   Definitions and structural lemmas for Card UNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/CardUNeZero.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
namespace PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
section Defs
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
def projQ (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) : V →ₗ[ℂ] V :=
  ((cardU F k : ℂ))⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x
end Defs
def RepGamConj : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V),
    repGam ψ₀ π = ∑ y : GL (Fin k) F, (π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y
def RepGamComm : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (g : GL (Fin k) F),
    π g ∘ₗ repGam ψ₀ π = repGam ψ₀ π ∘ₗ π g
def QIdem : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V),
    projQ ψ₀ π ∘ₗ projQ ψ₀ π = projQ ψ₀ π
def GenericIff : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V),
    Generic ψ₀ π ↔ projQ ψ₀ π ≠ 0
def RankLeOne : Prop :=
  GelfandGraevMultOne →
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
      Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≤ 1
def SchurC : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
    ∀ f : V →ₗ[ℂ] V, (∀ g, π g ∘ₗ f = f ∘ₗ π g) → ∃ c : ℂ, f = c • LinearMap.id
def TraceRepGam : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ (GL (Fin k) F) V),
    LinearMap.trace ℂ V (repGam ψ₀ π) =
      (Fintype.card (GL (Fin k) F) : ℂ) * LinearMap.trace ℂ V (projQ ψ₀ π)
def IdemTrace : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (e : V →ₗ[ℂ] V), e ∘ₗ e = e →
    LinearMap.trace ℂ V e = (Module.finrank ℂ (LinearMap.range e) : ℂ)
def DimPos : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible → 0 < Module.finrank ℂ V
end PI.GGConvScalarW


