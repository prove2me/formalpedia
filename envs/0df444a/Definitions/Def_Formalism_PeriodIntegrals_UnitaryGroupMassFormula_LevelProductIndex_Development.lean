-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:53.417387+00:00
-- url     : https://prove2.me/theorems/dda30da3-cfc0-4ee3-be2c-44fea470785a
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.LPI
open Formalism.UG
abbrev latA (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      (Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  latS (F := F) (FiniteAdeleRing (𝓞 F) F)
    (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb
abbrev latV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F)
    (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb
def PLGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (O : Subring R) (n k : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (m : Fin k → Fin n → E),
    (∀ i, m i ∈ Lb) → (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) →
    ∀ y : Fin n → E ⊗[F] R,
      y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Lb ↔
        ∃ a : Fin k → R, (∀ i, a i ∈ O) ∧ y = fun j => ∑ i, m i j ⊗ₜ[F] a i
def PLInj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ v, prV (E := E) v z = 0) → z = 0
def PLDown : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    y ∈ latA F Lb → (fun j => prV (E := E) v (y j)) ∈ latV v Lb
def PLUp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Lb →
    ∀ y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ v, (fun j => prV (E := E) v (y j)) ∈ latV v Lb) → y ∈ latA F Lb
def PLLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E)),
    Module.Finite (𝓞 E) Lb →
    ∀ g ∈ levelAfL σ J Lb, ∀ v, bc (prV (E := E) v) g ∈ levelVL σ J v Lb
end PI.LPI


