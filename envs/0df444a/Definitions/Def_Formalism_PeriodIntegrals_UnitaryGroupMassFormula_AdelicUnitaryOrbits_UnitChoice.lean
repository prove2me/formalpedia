-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:36.895642+00:00
-- url     : https://prove2.me/theorems/edc1cc64-a05f-46ae-8e22-4a633c58d671
-- title:
--   Unit Choice
-- statement:
--   Definitions and structural lemmas for Unit Choice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/UnitChoice.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
def UnitChoice (A : Type) [CommRing A] : Prop :=
  ∀ (k : ℕ) (f : Fin k → A), Ideal.span (Set.range f) = ⊤ →
    ∃ e : Fin k → A, (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 ∧ IsUnit (∑ i, e i * f i)
def StP : Prop := ∀ (F : Type) [Field F] [NumberField F], UnitChoice (AF F)
def StRefl : Prop :=
  ∀ (S : Type) [CommRing S] (s : S →+* S), (∀ z, s (s z) = z) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) S), Formalism.UG.IsHerm s J → IsUnit J.det →
    ∀ (x y : Fin n → S) (lam : S), lam * s lam = 1 → Formalism.UG.hform s J y y = Formalism.UG.hform s J x x →
      IsUnit (Formalism.UG.hform s J x x - s lam * Formalism.UG.hform s J y x) →
      ∃ g : GL (Fin n) S, g ∈ Formalism.UG.UJ s J ∧ (g : Matrix (Fin n) (Fin n) S).mulVec x = y
def StFix : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 →
    (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) → ∀ (R : Type) [CommRing R] [Algebra F R],
    (∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z) ∧
    ∀ z : R ⊗[F] E, sigR R σ z = z →
      z = algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z)
def StLam : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 →
    (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) → ∀ (R : Type) [CommRing R] [Algebra F R], UnitChoice R →
    ∀ (t : R ⊗[F] E) (β : F), β ≠ 0 →
      ∃ lam : R ⊗[F] E, lam * sigR R σ lam = 1 ∧ IsUnit (algebraMap F (R ⊗[F] E) β - sigR R σ lam * t)
def StAsm : Prop := StP → StRefl → StFix → StLam → PI.AdelicOrbitU.AdelicOrbitQuad
end PIW.AdelicOrbitU


