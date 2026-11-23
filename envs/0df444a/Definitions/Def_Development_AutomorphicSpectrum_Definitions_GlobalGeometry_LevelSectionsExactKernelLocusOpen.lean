-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LevelSectionsExactKernelLocusOpen
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LevelSectionsExactKernelLocusOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:42.816812+00:00
-- url     : https://prove2.me/theorems/fd532d99-5b34-4c00-9244-e41218e94bc5
-- title:
--   Level Sections Exact Kernel Locus Open
-- statement:
--   Definitions and structural lemmas for Level Sections Exact Kernel Locus Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/LevelSectionsExactKernelLocusOpen.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}
def genFibre (O : Type) [CommRing O] [Algebra O Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) :=
  {p | ∀ o : O, o ≠ 0 → unitAt ξ p (algebraMap O Ω o)}
def ConstClosed (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] : Prop :=
  ∀ a : Ω, IsAlgebraic O a → ∃ x y : O, y ≠ 0 ∧ a * algebraMap O Ω y = algebraMap O Ω x
def lineLat (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) : Lat ξ Ω := fun x =>
  Submodule.span (regAt ξ x) {t | ∃ f : Ω, IsCoeffAt A B p q a b x f ∧ t = f⁻¹}
def SplitModAt (A : Lat ξ E) (ϖ : Ω) {N : ℕ} (J : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))) (x y : Cpt ξ) : Prop :=
  (∀ w ∈ A y, ∀ k, J x w k ∈ regAt ξ y ∧ (J x w k - J y w k) / ϖ ∈ regAt ξ y) ∧
    ∃ R : (Fin N → Ω) →ₗ[Ω] E, (∀ k, R (Pi.single k 1) ∈ A y) ∧ ∀ w ∈ A y, ∃ w' ∈ A y, R (J x w) = w + ϖ • w'
def ExactModLat (A B : Lat ξ E) (ϖ : Ω) (N : ℕ) : Prop :=
  ∃ J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω)), ∀ x : Cpt ξ, ¬ unitAt ξ x ϖ → ∃ U : X.Opens, x.1 ∈ U ∧
    ∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → SplitModAt A ϖ J x y ∧ SplitModAt B ϖ J' x y ∧
      ∀ w ∈ A y, ∀ w' ∈ B y, dotProduct (J x w) (J' x w') / ϖ ∈ regAt ξ y
end GlobalTheory.CompanionTheory.Ar.Flat


