-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:39.458862+00:00
-- url     : https://prove2.me/theorems/ea361640-1144-46f9-aa1d-adddfc3347ee
-- title:
--   Mem Eig Sp Of Mem Ht Dual
-- statement:
--   Definitions and structural lemmas for Mem Eig Sp Of Mem Ht Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
def secVal {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Z, W)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom f)
def FullTorsion (G : Over X) [GrpObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G), g ^ n = 1 →
    ∃ x : Over.mk ξ ⟶ G, g.left = spMap i ≫ x.left
namespace LieModel
def IsHTAt (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) (x : Over.mk ξ ⟶ G) (q : Cpt ξ)
    (w : Module.Dual Ω E) : Prop :=
  w ∈ M.omLat q ∧ ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
      (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap i ≫ x.left → g ^ n = 1 →
        Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h f = c) ∧
    ∀ e v, M.Extends q e v → ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r ∈ regAt ξ q,
      w e = genMap ξ q (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W h f).snd + n * r
def htOm (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) : Lat ξ (Module.Dual Ω E) := fun q =>
  Submodule.span (regAt ξ q) {w | ∃ x : Over.mk ξ ⟶ G, x ^ n = 1 ∧ M.IsHTAt L n x q w}
def htOmEig (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ (Module.Dual Ω (eigSp ρ σ)) :=
  (M.htOm L n).map (eigSp ρ σ).subtype.dualMap
def htDual (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q}
def htW (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) (𝔡 : Ideal O) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q}
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)
example (q : Cpt ξ) : (0 : Module.Dual Ω (eigSp ρ σ)) ∈ M.htOmEig L n ρ σ q := Submodule.zero_mem _
end LieModel
open Classical in

def Lat.patch (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat ξ E := fun q =>
  if ∃ p ∈ S, InFibre ξ p q then ⨅ p ∈ S, ⨅ _ : InFibre ξ p q, Lp p q else L₀ q
end GlobalTheory.CompanionTheory.Ar


