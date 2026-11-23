-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_AdelicLattices_FactPrimes
-- name    : Development_AutomorphicSpectrum_Definitions_AdelicLattices_FactPrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:00.642802+00:00
-- url     : https://prove2.me/theorems/92858766-423e-4410-b524-105805c4ff3d
-- title:
--   Fact Primes
-- statement:
--   Definitions and structural lemmas for Fact Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/AdelicLattices/FactPrimes.lean

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
namespace GlobalTheory.CompanionTheory.Ar.Fl
open NumberField
instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
def logIdeal {O A : Type} [CommRing O] [NormedField A] (ι : O →+* A) (I : Ideal O) : ℝ :=
  Real.log (⨆ a : I, ‖ι (a : O)‖)
structure LogNorms (k : Type) [Field k] where

  inf : (k →+* ℂ) → ℝ

  fin : ∀ p : Nat.Primes, (k →+* ℂ_[p]) → ℝ
namespace LogNorms
variable {k : Type} [Field k] [NumberField k]
def finSum (N : LogNorms k) (p : Nat.Primes) : ℝ := ∑ ι : k →+* ℂ_[p], N.fin p ι
def IsAdelic (N : LogNorms k) : Prop := {p : Nat.Primes | ∃ ι, N.fin p ι ≠ 0}.Finite
def deg (N : LogNorms k) : ℝ := -((∑ s : k →+* ℂ, N.inf s) + ∑ᶠ p, N.finSum p) / Module.finrank ℚ k
def ofElt (x : k) : LogNorms k := ⟨fun s => Real.log ‖s x‖, fun _ ι => Real.log ‖ι x‖⟩
def ext {k' : Type} [Field k'] (f : k →+* k') (N : LogNorms k) : LogNorms k' :=
  ⟨fun s => N.inf (s.comp f), fun p ι => N.fin p (ι.comp f)⟩
end LogNorms
end GlobalTheory.CompanionTheory.Ar.Fl


