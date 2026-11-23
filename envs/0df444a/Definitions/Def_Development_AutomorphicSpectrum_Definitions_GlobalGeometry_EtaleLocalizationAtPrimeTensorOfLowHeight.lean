-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:03.914736+00:00
-- url     : https://prove2.me/theorems/4bc7f655-4957-4368-9f81-dff08a2e234e
-- title:
--   Etale Localization At Prime Tensor Of Low Height
-- statement:
--   Definitions and structural lemmas for Etale Localization At Prime Tensor Of Low Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/EtaleLocalizationAtPrimeTensorOfLowHeight.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
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
variable {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']
def Lat (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] : Type :=
  (p : Cpt ξ) → Submodule (regAt ξ p) E
namespace Lat
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}
def IsFrameAt (L : Lat ξ E) {r : ℕ} (b : Fin r → E) (p : Cpt ξ) : Prop :=
  LinearIndependent Ω b ∧ L p = Submodule.span (regAt ξ p) (Set.range b)
def IsVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q
def IsVB (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) : Prop := L.IsVBOn Set.univ r V
def inter (L : Lat ξ E) (V : Submodule Ω E) : Lat ξ E := fun p => L p ⊓ V.restrictScalars (regAt ξ p)
def map (L : Lat ξ E) (f : E →ₗ[Ω] E') : Lat ξ E' := fun p => (L p).map (f.restrictScalars (regAt ξ p))
def comap (L : Lat ξ E') (f : E →ₗ[Ω] E') : Lat ξ E := fun p => (L p).comap (f.restrictScalars (regAt ξ p))
def prod (L : Lat ξ E) (L' : Lat ξ E') : Lat ξ (E × E') := fun p => (L p).prod (L' p)
def scale (L : Lat ξ E) (a : Ω) : Lat ξ E := L.map (a • LinearMap.id)
def dual (L : Lat ξ E) : Lat ξ (Module.Dual Ω E) := fun p =>
  { carrier := {w | ∀ e ∈ L p, w e ∈ regAt ξ p}
    add_mem' := fun ha hb e he => by simpa using add_mem (ha e he) (hb e he)
    zero_mem' := fun e _ => by simp
    smul_mem' := fun c w hw e he => by
      show (c : Ω) * w e ∈ regAt ξ p
      exact mul_mem c.2 (hw e he) }
def wedge (L : Lat ξ E) (r : ℕ) : Lat ξ (⋀[Ω]^r E) := fun p =>
  Submodule.span (regAt ξ p) {w | ∃ b : Fin r → E, (∀ i, b i ∈ L p) ∧ w = exteriorPower.ιMulti Ω r b}
def IsChartOf (L : Lat ξ E) {κ : Type} (x : κ → Ω) (lat : κ → AddSubgroup E) : Prop :=
  ∀ c, x c ≠ 0 → ∀ e, e ∈ lat c ↔ ∀ p : Cpt ξ, InChart ξ x c p → e ∈ L p
def IsDegOn (L : Lat ξ E) (T : Set (Cpt ξ)) {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (e₀ : E) : Prop :=
  e₀ ≠ 0 ∧ ∀ p ∈ T, ∀ c : (k : K) → ι k, InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p →
    L p = Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a k) • e₀}
end Lat
def Dominates {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X' ⟶ X) (i : Ω →+* Ω') : Prop :=
  ξ' ≫ f = Spec.map (CommRingCat.ofHom i) ≫ ξ
def Lat.pull {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {F : Type} [AddCommGroup F] [Module Ω' F]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
    (j : E →+ F) : Lat ξ' F := fun p' =>
  Submodule.span (regAt ξ' p') {e' | ∃ (h : genPt ξ ⤳ f p'.1) (e : E), e ∈ L ⟨f p'.1, h⟩ ∧ e' = j e}
end GlobalTheory.CompanionTheory.Ar


