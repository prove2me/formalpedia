-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:55.917512+00:00
-- url     : https://prove2.me/theorems/99363c41-b935-4c2c-831c-395edefddf36
-- title:
--   Holomorphic Hom Determined
-- statement:
--   Definitions and structural lemmas for Holomorphic Hom Determined, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HolHom
section Values
variable {A : Type} [CommRing A] {X : Scheme.{0}}
def evalHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom
theorem valR_eq (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR x U f = evalHom x U h f := by
  rw [valR, dif_pos h]; rfl
theorem valAt'_eq_valR (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valAt' x U f = valR x U f := rfl
end Values
section Hol
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
def HolAt (c : V → (Sp ℂ ⟶ X)) (z : V) : Prop :=
  ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U →
    (∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ U) ∧ ∀ f : Γ(X, U), DifferentiableAt ℂ (fun t => valAt' (c t) U f) z
end Hol
section Deriv
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
def IsDerivAt (c : V → (Sp ℂ ⟶ X)) (z w : V) (v : Sp (DualNumber ℂ) ⟶ X) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = c z ∧
    ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U → ∀ f : Γ(X, U),
      TrivSqZeroExt.snd (valR v U f) = fderiv ℂ (fun t => valAt' (c t) U f) z w
abbrev constVec (x : Sp ℂ ⟶ X) : Sp (DualNumber ℂ) ⟶ X := spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x
def jetHom {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) (U : X.Opens) (hU : ⊤ ≤ c z ⁻¹ᵁ U) :
    Γ(X, U) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' (c z) U f) + TrivSqZeroExt.inr (fderiv ℂ (fun t => valAt' (c t) U f) z w)
  map_one' := by
    have : (fun t => valAt' (c t) U 1) =ᶠ[𝓝 z] fun _ => 1 := (h U hU).1.mono fun t ht => by
      simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0]
    simp
  map_zero' := by
    have : (fun t => valAt' (c t) U 0) =ᶠ[𝓝 z] fun _ => 0 := (h U hU).1.mono fun t ht => by
      simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0]
    simp
  map_add' f f' := by
    have : (fun t => valAt' (c t) U (f + f')) =ᶠ[𝓝 z] fun t => valAt' (c t) U f + valAt' (c t) U f' :=
      (h U hU).1.mono fun t ht => by simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0, fderiv_fun_add ((h U hU).2 f) ((h U hU).2 f')]
    ext <;> simp
  map_mul' f f' := by
    have : (fun t => valAt' (c t) U (f * f')) =ᶠ[𝓝 z] fun t => valAt' (c t) U f * valAt' (c t) U f' :=
      (h U hU).1.mono fun t ht => by simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0, fderiv_fun_mul ((h U hU).2 f) ((h U hU).2 f')]
    ext <;> simp [mul_comm]
end Deriv
section Group
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}
variable {G : Over S} [GrpObj G]
variable {y : Sp ℂ ⟶ S}
end Group
section Linear
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}
end Linear
section Family
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
end Family
end GlobalTheory.HolHom
namespace GlobalTheory
end GlobalTheory


