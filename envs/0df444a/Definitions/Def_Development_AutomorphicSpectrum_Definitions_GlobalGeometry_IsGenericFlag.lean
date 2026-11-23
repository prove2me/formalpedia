-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:33.224139+00:00
-- url     : https://prove2.me/theorems/0cc78e51-d571-427b-b06d-7e12ad57e962
-- title:
--   Is Generic Flag
-- statement:
--   Definitions and structural lemmas for Is Generic Flag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsGenericFlag.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
def flagStep (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : ℕ) : Submodule Ω E :=
  Submodule.span Ω (b₀ '' {k | (k : ℕ) < i})
namespace Lat
def IsFlagVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) {r : ℕ} (b₀ : Fin r → E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q
def gr (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i}
def IsGenAt (Λ : Lat ξ Ω) (p : Cpt ξ) (t : Ω) : Prop := t ≠ 0 ∧ Λ p = Submodule.span (regAt ξ p) {t}
def tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i}
def grTens {S : Type} [Fintype S] {r : S → ℕ} (L : S → Lat ξ E) (b₀ : ∀ σ, Fin (r σ) → E)
    (a : (Σ σ, Fin (r σ)) → ℤ) : Lat ξ Ω :=
  tens (fun q : Σ σ, Fin (r σ) => (L q.1).gr (b₀ q.1) q.2) a
end Lat
def IsGenericFlag {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E' : Type} [AddCommGroup E'] [Module Ω' E']
    (j : E →+ E') {S : Type} {r : S → ℕ} (V : S → Submodule Ω E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ) : Prop :=
  ∃ (c : ∀ σ, Fin (r σ) → E) (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω'),
    (∀ σ, LinearIndependent Ω (c σ) ∧ Submodule.span Ω (Set.range (c σ)) = V σ) ∧
    (∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) ∧ (∀ σ, LinearIndependent Ω' fun k => j (c σ k)) ∧
    (∀ σ, LinearIndependent Ω' (b₀ σ)) ∧ (∀ σ k, u σ k k = 1) ∧ (∀ σ l k, l < k → u σ l k = 0) ∧
    (∀ σ i, flagStep Ω' (b₀ σ) i = flagStep Ω' (fun k => ∑ l, u σ l k • j (c σ l)) i) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    0 < d ∧ Module.finrank (IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω' = d
end GlobalTheory.CompanionTheory.Ar


