-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalParameterRingsAndInverseParameterPolynomialBasesDataExplicitPublicPowerProfileV320261019
-- name    : MazurTransfer_Order13MixedOriginalParameterRingsAndInverseParameterPolynomialBasesDataExplicitPublicPowerProfileV320261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T05:45:17.044161+00:00
-- url     : https://prove2.me/theorems/bc589d64-02b6-4af7-ab52-316653982363
-- title:
--   Original mixed single-section parameters and inverse polynomial basis
-- statement:
--   The exact original polynomial parameter identities, coordinate rewrites, inverse parameter subalgebra, explicit three-element polynomial basis and finite free coefficient level sets. Fourteen original source modules retain their per-file headers. Every owned public and private type and every whole nonproof value is independently compared, with original generated proof bodies checked where compiler sharing changes their numbering. Named downstream consumer: both actual single-section affine opens and degree-three FiniteMapData.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact original single-infinity parameter ring presentations,
polynomial bases and finite free level sets for the inverse chart of the same
mixed quadratic curve. Named downstream consumer: the original actual
single-section degree-three FiniteMapData and its arbitrary-degree powers.
Original per-file headers and attribution are retained below.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_monic_quadratic_parameter_power_profile
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalCoefficientAndOverlapBaseChangeMapsData20261019
import Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardZeroSectionData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: basic opens transport through an actual Spec-to-open
isomorphism and its exact global section-ring comparison.
Named downstream consumers: the two actual single-section parameters in
order-13 FiniteMapData. No parameter or curve-specific identity is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalFiniteMapAffineBasicOpenTransport20261019
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{u}} (U : X.Opens) {B : Type u} [CommRing B]

def sectionsRingIso (e : Spec (.of B) ≅ U.toScheme) : Γ(X, U) ≅ CommRingCat.of B :=
  U.topIso.symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ Scheme.ΓSpecIso (.of B)

def transportedSection (e : Spec (.of B) ≅ U.toScheme) (b : B) : Γ(X, U) :=
  (sectionsRingIso U e).commRingCatIsoToRingEquiv.symm b

theorem basicOpen_transport (e : Spec (.of B) ≅ U.toScheme) (b : B) :
    X.basicOpen (transportedSection U e b) =
      (e.hom ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen b := by
  have hq := (sectionsRingIso U e).commRingCatIsoToRingEquiv.apply_symm_apply b
  change (Scheme.ΓSpecIso (.of B)).hom
    (e.hom.appTop (U.topIso.inv (transportedSection U e b))) = b at hq
  have ht : e.hom.appTop (U.topIso.inv (transportedSection U e b)) =
      (Scheme.ΓSpecIso (.of B)).inv b := by
    have hh := congrArg (fun x : B => (Scheme.ΓSpecIso (.of B)).inv x) hq
    have hc : (Scheme.ΓSpecIso (.of B)).inv
        ((Scheme.ΓSpecIso (.of B)).hom
          (e.hom.appTop (U.topIso.inv (transportedSection U e b)))) =
        e.hom.appTop (U.topIso.inv (transportedSection U e b)) := by
      change ((Scheme.ΓSpecIso (.of B)).hom ≫ (Scheme.ΓSpecIso (.of B)).inv)
        (e.hom.appTop (U.topIso.inv (transportedSection U e b))) = _
      rw [Iso.hom_inv_id]
      rfl
    exact hc.symm.trans hh
  have hp : e.hom ⁻¹ᵁ U.toScheme.basicOpen (U.topIso.inv (transportedSection U e b)) =
      PrimeSpectrum.basicOpen b := by
    rw [Scheme.preimage_basicOpen_top, ht, basicOpen_eq_of_affine]
  have hi : e.hom ''ᵁ PrimeSpectrum.basicOpen b =
      U.toScheme.basicOpen (U.topIso.inv (transportedSection U e b)) := by
    rw [← hp, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, ← hi]
  apply SetLike.ext'
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e.hom z, ⟨z, hz, rfl⟩, rfl⟩

end MazurTransfer.MixedOriginalFiniteMapAffineBasicOpenTransport20261019
#print axioms MazurTransfer.MixedOriginalFiniteMapAffineBasicOpenTransport20261019.basicOpen_transport

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transported affine sections pull back to their literal
coordinate images along a Spec morphism landing in the affine open.
Named downstream consumer: reciprocal parameter product on the actual
order-13 two-chart intersection.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalFiniteMapAffineRestrictionTransport20261019
open CategoryTheory AlgebraicGeometry
open MixedOriginalFiniteMapAffineBasicOpenTransport20261019
variable {X : Scheme.{u}} (U : X.Opens) {B A : Type u} [CommRing B] [CommRing A]

theorem inclusion_appLE_self_top :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  rfl

theorem composite_appLE (k : Spec (.of A) ⟶ U.toScheme)
    (h : ⊤ ≤ (k ≫ U.ι) ⁻¹ᵁ U) :
    (k ≫ U.ι).appLE U ⊤ h = U.topIso.inv ≫ k.appTop := by
  have hc := Scheme.Hom.appLE_comp_appLE k U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (show ⊤ ≤ k ⁻¹ᵁ ⊤ by simp)
  rw [inclusion_appLE_self_top] at hc
  have ht : k.appLE ⊤ ⊤ (by simp) = k.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Hom.preimage_top,
      homOfLE_refl, op_id, Functor.map_id]
    exact Category.comp_id _
  rw [ht] at hc
  exact hc.symm

theorem transportedSection_pullback (e : Spec (.of B) ≅ U.toScheme)
    (φ : B →+* A) (b : B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι).appLE U ⊤ h
        (transportedSection U e b)) = φ b := by
  have hq := (sectionsRingIso U e).commRingCatIsoToRingEquiv.apply_symm_apply b
  change (Scheme.ΓSpecIso (.of B)).hom
    (e.hom.appTop (U.topIso.inv (transportedSection U e b))) = b at hq
  have hc := composite_appLE U (Spec.map (CommRingCat.ofHom φ) ≫ e.hom)
    (show ⊤ ≤ ((Spec.map (CommRingCat.ofHom φ) ≫ e.hom) ≫ U.ι) ⁻¹ᵁ U by
      simpa only [Category.assoc] using h)
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have hp := congrArg (fun k : Γ(Spec (.of B), ⊤) ⟶ CommRingCat.of A =>
    k (e.hom.appTop (U.topIso.inv (transportedSection U e b)))) hn
  have hd : (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι).appLE U ⊤ h =
      U.topIso.inv ≫ (Spec.map (CommRingCat.ofHom φ) ≫ e.hom).appTop := by
    simpa only [Category.assoc] using hc
  rw [hd, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (.of A)).hom
    ((Spec.map (CommRingCat.ofHom φ)).appTop
      (e.hom.appTop (U.topIso.inv (transportedSection U e b)))) = φ b
  exact hp.trans (congrArg φ hq)

theorem appLE_injective_of_image_top {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (hImage : j ''ᵁ ⊤ = U) (h : ⊤ ≤ j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U ⊤ h) := by
  let e : Γ(X, U) ≅ Γ(Y, ⊤) :=
    X.presheaf.mapIso (eqToIso hImage).op ≪≫ j.appIso ⊤
  have he : e.hom = j.appLE U ⊤ h := by
    change X.presheaf.map (eqToHom hImage).op ≫ (j.appIso ⊤).hom = _
    rw [Scheme.Hom.appIso_hom']
    exact j.map_appLE' h hImage
  rw [← he]
  exact e.commRingCatIsoToRingEquiv.injective

end MazurTransfer.MixedOriginalFiniteMapAffineRestrictionTransport20261019
#print axioms MazurTransfer.MixedOriginalFiniteMapAffineRestrictionTransport20261019.transportedSection_pullback

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the integral single-section coordinates of MazurTheorem to the mixed
quadratic model. The rescaled multiplication table does not divide by two.
Design boundary: literal coordinate identities for a candidate single-pole
parameter and a finite algebra. Named downstream consumer: actual pointed
mixed finite-map data; affine-open identification and pole orders are separate.
-/

noncomputable section
namespace MazurTransfer.Order13MixedSingleSectionPolynomialIdentities
open Polynomial Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
universe u
variable (R : Type u) [CommRing R]

def t : ordinaryCoordinateRing R := yCoordinate R + (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1)
def p : ordinaryCoordinateRing R := xCoordinate R * t R
def q : ordinaryCoordinateRing R := xCoordinate R * (p R + 1)

theorem candidate_equation : t R ^ 2 - t R * (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1) -
    xCoordinate R * (xCoordinate R + 1) = 0 := by
  have hy := ordinary_relation R
  dsimp only [t]
  linear_combination hy

theorem p_squared : p R ^ 2 = t R * q R - p R := by
  dsimp only [p,q]
  ring

theorem p_mul_q : p R * q R = t R ^ 3 - t R ^ 2 - t R * q R := by
  have ht := candidate_equation R
  dsimp only [p,q]
  linear_combination -(t R) * ht

theorem q_squared : q R ^ 2 = (t R ^ 2 - t R) * p R + (t R - 1) * q R +
    (2 - t R) * t R ^ 2 - t R := by
  have ht := candidate_equation R
  dsimp only [p,q]
  linear_combination (-(t R) * xCoordinate R + t R - 1) * ht

theorem reciprocal_norm_identity : wCoordinate R *
    (wCoordinate R + 1 + zCoordinate R + zCoordinate R ^ 3) =
      zCoordinate R ^ 4 * (1 + zCoordinate R) := by
  have hw := reciprocal_relation R
  linear_combination hw

theorem reciprocal_secondary_identity : wCoordinate R * (wCoordinate R + 1 + zCoordinate R) =
    zCoordinate R ^ 3 * (zCoordinate R + zCoordinate R ^ 2 - wCoordinate R) := by
  have hw := reciprocal_relation R
  linear_combination hw

end MazurTransfer.Order13MixedSingleSectionPolynomialIdentities
#print axioms MazurTransfer.Order13MixedSingleSectionPolynomialIdentities.candidate_equation
#print axioms MazurTransfer.Order13MixedSingleSectionPolynomialIdentities.q_squared
#print axioms MazurTransfer.Order13MixedSingleSectionPolynomialIdentities.reciprocal_secondary_identity

end

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for a general monic mixed quadratic algebra.
Named downstream consumer: mixed single-section power coordinates and finite-algebra bases.
-/

noncomputable section
namespace MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (h f : R)

abbrev equation : Polynomial R := X ^ 2 + C h * X - C f

theorem equation_monic : (equation R h f).Monic := by
  have he : equation R h f = X ^ 2 + (C h * X - C f) := by unfold equation; ring
  rw [he]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_sub_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_mul_le _ _) (by
      calc
        degree (C h) + degree (X : Polynomial R) ≤ 0 + 1 :=
          add_le_add degree_C_le degree_X_le
        _ < (2 : WithBot ℕ) := by norm_num)
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

theorem equation_natDegree : (equation R h f).natDegree = 2 := by
  unfold equation
  rw [natDegree_sub_C]
  calc
    _ = natDegree (X ^ 2 : Polynomial R) := by
      apply natDegree_add_eq_left_of_natDegree_lt
      calc
        natDegree (C h * X : Polynomial R) ≤ natDegree (C h) + natDegree X := natDegree_mul_le
        _ = 1 := by simp
        _ < natDegree (X ^ 2 : Polynomial R) := by simp
    _ = 2 := by simp

def powerBasis : PowerBasis R (AdjoinRoot (equation R h f)) :=
  AdjoinRoot.powerBasis' (equation_monic R h f)

theorem powerBasis_dim : (powerBasis R h f).dim = 2 := equation_natDegree R h f

def basis : Basis (Fin 2) R (AdjoinRoot (equation R h f)) :=
  (powerBasis R h f).basis.reindex (finCongr (powerBasis_dim R h f))

theorem basis_zero : basis R h f 0 = 1 := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R h f).gen ^ ((finCongr (powerBasis_dim R h f)).symm 0).val :=
      (powerBasis R h f).basis_eq_pow _
    _ = 1 := by simp

theorem basis_one : basis R h f 1 = AdjoinRoot.root (equation R h f) := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R h f).gen ^ ((finCongr (powerBasis_dim R h f)).symm 1).val :=
      (powerBasis R h f).basis_eq_pow _
    _ = (powerBasis R h f).gen := by simp
    _ = AdjoinRoot.root (equation R h f) := rfl

def coordinates : AdjoinRoot (equation R h f) ≃ₗ[R] R × R :=
  (basis R h f).equivFun.trans (LinearEquiv.finTwoArrow R R)

theorem coordinates_symm (v : R × R) :
    (coordinates R h f).symm v = AdjoinRoot.of (equation R h f) v.1 +
      AdjoinRoot.of (equation R h f) v.2 * AdjoinRoot.root (equation R h f) := by
  rw [coordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_two, basis_zero, basis_one, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem coordinates_of_add_of_mul_root (a b : R) :
    coordinates R h f (AdjoinRoot.of (equation R h f) a +
      AdjoinRoot.of (equation R h f) b * AdjoinRoot.root (equation R h f)) = (a, b) := by
  rw [← coordinates_symm R h f (a, b), LinearEquiv.apply_symm_apply]

end MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019

#print axioms MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_symm

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the existing single-section coefficient argument to the mixed model.
Design boundary: polynomial coordinates of powers of the actual mixed
single-pole parameter, with monic first coordinate in every characteristic.
Named downstream consumer: independence of the finite-algebra generators.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionPowerCoordinates
open Polynomial MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def powerCoordinates : ℕ → Polynomial R × Polynomial R :=
  Nat.rec (1, 0) (fun _ v => (ordinaryH R * v.1 + ordinaryF R * v.2, v.1))

@[simp] theorem powerCoordinates_zero : powerCoordinates R 0 = (1, 0) := rfl
@[simp] theorem powerCoordinates_succ (n : ℕ) :
    powerCoordinates R (n + 1) =
      (ordinaryH R * (powerCoordinates R n).1 + ordinaryF R * (powerCoordinates R n).2,
        (powerCoordinates R n).1) := rfl

theorem of_ordinaryH :
    AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (ordinaryH R) =
      xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1 := by
  exact Order13MixedQuadraticPolynomialEvaluations.map_ordinaryH R _

theorem root_squared :
    yCoordinate R ^ 2 =
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (ordinaryF R) -
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (ordinaryH R) * yCoordinate R := by
  have ht := root_relation R (ordinaryH R) (ordinaryF R)
  change yCoordinate R ^ 2 +
    AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (ordinaryH R) * yCoordinate R -
    AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (ordinaryF R) = 0 at ht
  linear_combination ht

theorem power_expansion (n : ℕ) :
    t R ^ n =
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (powerCoordinates R n).1 +
        AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (powerCoordinates R n).2 * yCoordinate R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, powerCoordinates_succ]
    simp only [map_add, map_mul]
    rw [of_ordinaryH]
    dsimp only [t]
    have hy := root_squared R
    rw [of_ordinaryH] at hy
    linear_combination
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (powerCoordinates R n).2 * hy

variable [Nontrivial R]

def coordinates : ordinaryCoordinateRing R ≃ₗ[Polynomial R] Polynomial R × Polynomial R :=
  MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial R) (ordinaryH R) (ordinaryF R)

theorem power_coordinates (n : ℕ) : coordinates R (t R ^ n) = powerCoordinates R n := by
  rw [power_expansion]
  exact MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_of_add_of_mul_root
    (Polynomial R) (ordinaryH R) (ordinaryF R) _ _

theorem ordinaryH_degree : (ordinaryH R).natDegree = 3 := by
  unfold ordinaryH
  compute_degree!

omit [Nontrivial R] in
theorem ordinaryH_monic : (ordinaryH R).Monic := by
  unfold ordinaryH
  monicity!

theorem ordinaryF_degree : (ordinaryF R).natDegree = 2 := by
  unfold ordinaryF
  compute_degree!

omit [Nontrivial R] in
theorem ordinaryF_monic : (ordinaryF R).Monic := by
  unfold ordinaryF
  monicity!

variable [IsDomain R]

omit [Nontrivial R] in
theorem power_coordinates_profile (n : ℕ) :
    (powerCoordinates R n).1.Monic ∧
    (powerCoordinates R n).1.natDegree = 3 * n ∧
    (powerCoordinates R n).2.natDegree ≤ 3 * n := by
  simpa only [ordinaryH_degree, powerCoordinates] using
    (MazurTransfer.monic_quadratic_parameter_power_profile R (ordinaryH R) (ordinaryF R)
      (ordinaryH_monic R) (by rw [ordinaryF_degree,ordinaryH_degree]; decide) n)

end MazurTransfer.Order13MixedSingleSectionPowerCoordinates
#print axioms MazurTransfer.Order13MixedSingleSectionPowerCoordinates.power_expansion
#print axioms MazurTransfer.Order13MixedSingleSectionPowerCoordinates.power_coordinates_profile

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete inverse-parameter multiplication proof of the original
order-thirteen model to the integral mixed quadratic coordinate algebra.
Design boundary: an actual multiplication table in A[1/t], without dividing
by two. Named downstream consumer: the second finite chart algebra in
pointed mixed FiniteMapData; actual scheme charts are a separate obligation.
-/

noncomputable section
namespace MazurTransfer.Order13MixedInverseParameterPolynomialIdentities
open Order13DyadicMixedQuadraticCharts Order13MixedSingleSectionPolynomialIdentities
universe u
variable (R : Type u) [CommRing R]
abbrev ordinaryParameterLocalization := Localization.Away (t R)
def s : ordinaryParameterLocalization R := IsLocalization.Away.invSelf (t R)
def a : ordinaryParameterLocalization R := algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (p R) * s R ^ 2
def b : ordinaryParameterLocalization R := algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (q R) * s R ^ 2

private theorem inverse_table {A : Type u} [CommRing A] (T P Q S : A)
    (hS : T * S = 1) (hP : P ^ 2 = T * Q - P)
    (hPQ : P * Q = T ^ 3 - T ^ 2 - T * Q)
    (hQ : Q ^ 2 = (T ^ 2 - T) * P + (T - 1) * Q + (2-T)*T^2-T) :
    (P*S^2)^2 = S*(Q*S^2)-S^2*(P*S^2) ∧
    (P*S^2)*(Q*S^2) = S-S^2-S*(Q*S^2) ∧
    (Q*S^2)^2 = (1-S)*(P*S^2)+(S-S^2)*(Q*S^2)+(2*S^2-S-S^3) := by
  constructor
  · linear_combination S^4*hP + S^3*Q*hS
  constructor
  · linear_combination S^4*hPQ + (S*(T^2*S^2+T*S+1)-S^2*(T*S+1)-S^3*Q)*hS
  · linear_combination S^4*hQ + (P*S^2*(T*S+1-S)+Q*S^3+2*S^2*(T*S+1)-
      S*(T^2*S^2+T*S+1)-S^3)*hS

theorem actual_inverse_parameter_multiplication_table :
    a R ^ 2 = s R * b R - s R ^ 2 * a R ∧
    a R * b R = s R - s R ^ 2 - s R * b R ∧
    b R ^ 2 = (1-s R)*a R+(s R-s R^2)*b R+(2*s R^2-s R-s R^3) := by
  let φ := algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)
  have hP := congrArg φ (p_squared R)
  have hPQ := congrArg φ (p_mul_q R)
  have hQ := congrArg φ (q_squared R)
  simp only [map_pow,map_mul,map_sub,map_add,map_ofNat,map_one] at hP hPQ hQ
  exact inverse_table (φ (t R)) (φ (p R)) (φ (q R)) (s R)
    (IsLocalization.Away.mul_invSelf (t R)) hP hPQ hQ

end MazurTransfer.Order13MixedInverseParameterPolynomialIdentities
#print axioms MazurTransfer.Order13MixedInverseParameterPolynomialIdentities.actual_inverse_parameter_multiplication_table

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the mixed single-pole parameter is a nonzerodivisor over
any integral coefficient ring, and localization at it is injective.
Named downstream consumer: clearing inverse-parameter polynomial relations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionParameterRegular
open Polynomial MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
open Order13MixedSingleSectionPowerCoordinates
open Order13MixedInverseParameterPolynomialIdentities
variable (R : Type u) [CommRing R]

theorem t_mul_y : t R * yCoordinate R =
    AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (ordinaryF R) := by
  have hy := root_squared R
  rw [of_ordinaryH] at hy
  dsimp only [t]
  linear_combination hy

theorem inverse_parameter_isUnit : IsUnit (s R) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R), ?_⟩
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf (t R)

variable [IsDomain R]

theorem parameter_regular : IsRegular (t R) := by
  let : Module.Free (Polynomial R) (ordinaryCoordinateRing R) :=
    Module.Free.of_basis (MixedOriginalFiniteMapCoordinateRewrite20261019.basis (Polynomial R) (ordinaryH R) (ordinaryF R))
  have hf : ordinaryF R ≠ 0 := (ordinaryF_monic R).ne_zero
  have hm : IsSMulRegular (ordinaryCoordinateRing R) (ordinaryF R) :=
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hf)
  have hl : IsLeftRegular (t R) := by
    intro a b hab
    change t R * a = t R * b at hab
    apply hm
    simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq]
    rw [← t_mul_y]
    calc
      (t R * yCoordinate R) * a = yCoordinate R * (t R * a) := by ring
      _ = yCoordinate R * (t R * b) := by rw [hab]
      _ = (t R * yCoordinate R) * b := by ring
  refine ⟨hl, ?_⟩
  intro a b hab
  apply hl
  simpa only [mul_comm] using hab

theorem localization_injective : Function.Injective
    (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)) := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers (t R))
  intro r hr
  obtain ⟨n,rfl⟩ := hr
  exact (parameter_regular R).pow n

end MazurTransfer.Order13MixedSingleSectionParameterRegular
#print axioms MazurTransfer.Order13MixedSingleSectionParameterRegular.parameter_regular
#print axioms MazurTransfer.Order13MixedSingleSectionParameterRegular.localization_injective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL subalgebra of A[1/t] generated by p/t^2 and
q/t^2 is finite over R[S], S acting by 1/t, over every commutative ring.
Named downstream consumer: the second actual affine chart in pointed mixed
FiniteMapData. Adapts the checked span/adjoin proof of the original model
with the integral mixed multiplication table, without inverting two.
Freeness and the actual curve-open identification are separate obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial Submodule
open Order13DyadicMixedQuadraticCharts
open Order13MixedInverseParameterPolynomialIdentities
variable (R : Type u) [CommRing R]

noncomputable def parameterMap : Polynomial R →+* ordinaryParameterLocalization R := (aeval (s R)).toRingHom
scoped instance parameterAlgebra : Algebra (Polynomial R) (ordinaryParameterLocalization R) :=
  (parameterMap R).toAlgebra
scoped instance parameterSMul : SMul (Polynomial R) (ordinaryParameterLocalization R) :=
  (parameterAlgebra R).toSMul
scoped instance parameterModule : Module (Polynomial R) (ordinaryParameterLocalization R) :=
  @Algebra.toModule (Polynomial R) (ordinaryParameterLocalization R) _ _ (parameterAlgebra R)

theorem parameter_algebraMap (f : Polynomial R) :
    algebraMap (Polynomial R) (ordinaryParameterLocalization R) f = aeval (s R) f := rfl

def generators : Set (ordinaryParameterLocalization R) := {1, a R, b R}
def spanningModule : Submodule (Polynomial R) (ordinaryParameterLocalization R) :=
  Submodule.span (Polynomial R) (generators R)
noncomputable def candidateAlgebra : Subalgebra (Polynomial R) (ordinaryParameterLocalization R) :=
  Algebra.adjoin (Polynomial R) ({a R, b R} : Set (ordinaryParameterLocalization R))

private theorem one_mem_span : (1 : ordinaryParameterLocalization R) ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])
private theorem p_mem_span : a R ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])
private theorem q_mem_span : b R ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])

private theorem p_mul_p_mem : a R * a R ∈ spanningModule R := by
  rw [← pow_two, (actual_inverse_parameter_multiplication_table R).1]
  have ht : s R * b R = (X : Polynomial R) • b R := by simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  have ha : s R^2 * a R = (X^2 : Polynomial R) • a R := by simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  rw [ht,ha]
  exact (spanningModule R).sub_mem ((spanningModule R).smul_mem _ (q_mem_span R))
    ((spanningModule R).smul_mem _ (p_mem_span R))

private theorem p_mul_q_mem : a R * b R ∈ spanningModule R := by
  rw [(actual_inverse_parameter_multiplication_table R).2.1]
  have hc : s R-s R^2 = (X-X^2 : Polynomial R) • (1 : ordinaryParameterLocalization R) := by
    simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  have hb : s R*b R = (X : Polynomial R) • b R := by simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  rw [hc,hb]
  exact (spanningModule R).sub_mem ((spanningModule R).smul_mem _ (one_mem_span R))
    ((spanningModule R).smul_mem _ (q_mem_span R))

private theorem q_mul_q_mem : b R * b R ∈ spanningModule R := by
  rw [← pow_two, (actual_inverse_parameter_multiplication_table R).2.2]
  have ha : (1-s R)*a R = (1-X : Polynomial R) • a R := by simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  have hb : (s R-s R^2)*b R = (X-X^2 : Polynomial R) • b R := by simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  have hc : 2*s R^2-s R-s R^3 = (2*X^2-X-X^3 : Polynomial R) • (1 : ordinaryParameterLocalization R) := by
    simp [Algebra.smul_def,parameter_algebraMap, _root_.map_ofNat]
  rw [ha,hb,hc]
  exact (spanningModule R).add_mem
    ((spanningModule R).add_mem ((spanningModule R).smul_mem _ (p_mem_span R))
      ((spanningModule R).smul_mem _ (q_mem_span R)))
    ((spanningModule R).smul_mem _ (one_mem_span R))

theorem spanningModule_mul_closed 
    (v w : ordinaryParameterLocalization R) (hv : v ∈ spanningModule R) (hw : w ∈ spanningModule R) :
    v * w ∈ spanningModule R := by
  have hle : spanningModule R * spanningModule R ≤ spanningModule R := by
    change span (Polynomial R) (generators R) * span (Polynomial R) (generators R) ≤ _
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, w, hw, rfl⟩
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · simpa using one_mem_span R
    · simpa using p_mem_span R
    · simpa using q_mem_span R
    · simpa using p_mem_span R
    · exact p_mul_p_mem R
    · exact p_mul_q_mem R
    · simpa using q_mem_span R
    · change b R * a R ∈ spanningModule R
      rw [mul_comm]
      exact p_mul_q_mem R
    · exact q_mul_q_mem R
  exact hle (Submodule.mul_mem_mul hv hw)

theorem candidateAlgebra_eq_span  :
    (candidateAlgebra R).toSubmodule = spanningModule R := by
  let S : Subalgebra (Polynomial R) (ordinaryParameterLocalization R) :=
    (spanningModule R).toSubalgebra (one_mem_span R) (spanningModule_mul_closed R)
  have hBS : candidateAlgebra R ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rcases hz with rfl | rfl
    · exact p_mem_span R
    · exact q_mem_span R
  apply le_antisymm
  · exact fun _ hz => hBS hz
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (candidateAlgebra R).one_mem
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)

theorem candidateAlgebra_finite  :
    Module.Finite (Polynomial R) (candidateAlgebra R) := by
  change Module.Finite (Polynomial R) (candidateAlgebra R).toSubmodule
  apply Module.Finite.of_fg
  rw [candidateAlgebra_eq_span R]
  exact Submodule.fg_span (by simp [generators])

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra_eq_span
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra_finite

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the existing single-section degree argument to the mixed model.
Design boundary: the distinct polynomial degrees of the actual parameter
powers and generator products. Named downstream consumer: the actual
R[T]-linear independence of 1,p,q. Canonical x-polynomial scalars are used.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionWeightedPolynomialCoordinates
open Polynomial
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
open Order13MixedSingleSectionPowerCoordinates
variable (R : Type u) [CommRing R] [IsDomain R]

def firstComponent : ordinaryCoordinateRing R →ₗ[R] Polynomial R :=
  (LinearMap.fst R (Polynomial R) (Polynomial R)).comp
    ((coordinates R).toLinearMap.restrictScalars R)

theorem first_expansion (A B : Polynomial R) :
    firstComponent R (AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) A +
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) B * yCoordinate R) = A := by
  change (coordinates R _).1 = A
  exact congrArg Prod.fst (MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_of_add_of_mul_root
    (Polynomial R) (ordinaryH R) (ordinaryF R) A B)

theorem first_power (n : ℕ) :
    firstComponent R (t R ^ n) = (powerCoordinates R n).1 := by
  rw [power_expansion, first_expansion]

omit [IsDomain R] in
theorem p_power_expansion (n : ℕ) :
    p R * t R ^ n =
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (X * (powerCoordinates R (n + 1)).1) +
        AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) (X * (powerCoordinates R (n + 1)).2) *
          yCoordinate R := by
  rw [p, mul_assoc, ← pow_succ', power_expansion]
  simp only [map_mul]
  change AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) X * _ = _
  ring

omit [IsDomain R] in
theorem q_power_expansion (n : ℕ) :
    q R * t R ^ n =
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R))
        (X ^ 2 * (powerCoordinates R (n + 1)).1 + X * (powerCoordinates R n).1) +
      AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R))
        (X ^ 2 * (powerCoordinates R (n + 1)).2 + X * (powerCoordinates R n).2) *
          yCoordinate R := by
  have hq : q R * t R ^ n =
      xCoordinate R ^ 2 * t R ^ (n + 1) + xCoordinate R * t R ^ n := by
    rw [pow_succ]
    dsimp [q, p]
    ring
  rw [hq, power_expansion, power_expansion]
  simp only [map_add, map_mul, map_pow, _root_.map_ofNat]
  change AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) X ^ 2 * _ +
    AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) X * _ = _
  ring

theorem first_p_power (n : ℕ) :
    firstComponent R (p R * t R ^ n) = X * (powerCoordinates R (n + 1)).1 := by
  rw [p_power_expansion, first_expansion]

theorem first_q_power (n : ℕ) :
    firstComponent R (q R * t R ^ n) =
      X ^ 2 * (powerCoordinates R (n + 1)).1 + X * (powerCoordinates R n).1 := by
  rw [q_power_expansion, first_expansion]

def weightedPowers : Fin 3 × ℕ → ordinaryCoordinateRing R
  | (i,n) => if i = 0 then t R ^ n else if i = 1 then p R * t R ^ n else q R * t R ^ n

def weight : Fin 3 × ℕ → ℕ
  | (i,n) => if i = 0 then 3 * n else if i = 1 then 3 * n + 4 else 3 * n + 5

theorem weight_injective : Function.Injective weight := by
  rintro ⟨i,n⟩ ⟨j,m⟩ h
  fin_cases i <;> fin_cases j <;> simp [weight] at h <;>
    congr <;> omega

theorem first_power_degree (n : ℕ) :
    (firstComponent R (t R ^ n)).natDegree = 3 * n := by
  rw [first_power]
  exact (power_coordinates_profile R n).2.1

theorem first_p_power_degree (n : ℕ) :
    (firstComponent R (p R * t R ^ n)).natDegree = 3 * n + 4 := by
  obtain ⟨hm, hd, -⟩ := power_coordinates_profile R (n + 1)
  rw [first_p_power, natDegree_X_mul hm.ne_zero, hd]
  omega

theorem first_q_power_degree (n : ℕ) :
    (firstComponent R (q R * t R ^ n)).natDegree = 3 * n + 5 := by
  obtain ⟨hm, hd, -⟩ := power_coordinates_profile R (n + 1)
  have hA : (powerCoordinates R (n + 1)).1 ≠ 0 := hm.ne_zero
  have hdtop : (X ^ 2 * (powerCoordinates R (n + 1)).1).natDegree = 3 * n + 5 := by
    rw [natDegree_X_pow_mul _ hA, hd]
    omega
  have hdlower : (X * (powerCoordinates R n).1).natDegree ≤ 3 * n + 1 := by
    have hdn : (powerCoordinates R n).1.natDegree ≤ 3 * n := by
      rw [← first_power, first_power_degree R]
    have hd2X : (X : Polynomial R).natDegree ≤ 1 := by simp
    exact (natDegree_mul_le.trans (Nat.add_le_add hd2X hdn)).trans (by omega)
  rw [first_q_power, natDegree_add_eq_left_of_natDegree_lt (by omega :
    (X * (powerCoordinates R n).1).natDegree <
      (X ^ 2 * (powerCoordinates R (n + 1)).1).natDegree), hdtop]

theorem weighted_first_degree (i : Fin 3 × ℕ) :
    (firstComponent R (weightedPowers R i)).natDegree = weight i := by
  rcases i with ⟨i,n⟩
  fin_cases i
  · simpa [weightedPowers, weight] using first_power_degree R n
  · simpa [weightedPowers, weight] using first_p_power_degree R n
  · simpa [weightedPowers, weight] using first_q_power_degree R n

theorem weighted_first_nonzero (i : Fin 3 × ℕ) :
    firstComponent R (weightedPowers R i) ≠ 0 := by
  rcases i with ⟨i,n⟩
  by_cases hn : n = 0
  · subst n
    fin_cases i
    · have hf := first_power R 0
      simpa [weightedPowers] using hf.trans_ne (one_ne_zero : (1 : Polynomial R) ≠ 0)
    · intro h
      have hd := first_p_power_degree R 0
      simp [weightedPowers] at h
      simp only [pow_zero, mul_one] at hd
      rw [h, natDegree_zero] at hd
      norm_num [weight] at hd
    · intro h
      have hd := first_q_power_degree R 0
      simp [weightedPowers] at h
      simp only [pow_zero, mul_one] at hd
      rw [h, natDegree_zero] at hd
      norm_num [weight] at hd
  · intro h
    have hd := weighted_first_degree R (i,n)
    rw [h, natDegree_zero] at hd
    fin_cases i <;> simp [weight] at hd <;> omega

end MazurTransfer.Order13MixedSingleSectionWeightedPolynomialCoordinates
#print axioms MazurTransfer.Order13MixedSingleSectionWeightedPolynomialCoordinates.weighted_first_degree
#print axioms MazurTransfer.Order13MixedSingleSectionWeightedPolynomialCoordinates.weighted_first_nonzero

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: linear independence of nonzero polynomials of distinct degrees.
Named downstream consumer: actual single-section finite-algebra basis.
-/

noncomputable section
namespace MazurTransfer.MixedOriginalFiniteMapDistinctDegree20261019
open Polynomial
variable {R ι : Type*} [CommRing R] [IsDomain R]

theorem linearIndependent_of_injective_natDegree (v : ι → Polynomial R)
    (hn : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => (v i).natDegree)) :
    LinearIndependent R v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hs i hi
  by_contra hgi
  let k : Finset ι := s.filter (fun j => g j ≠ 0)
  have hk : k.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi,hgi⟩⟩
  obtain ⟨j,hj,hmax⟩ := k.exists_max_image (fun j => (v j).natDegree) hk
  obtain ⟨hjs,hgj⟩ := Finset.mem_filter.mp hj
  have hcoeff : (∑ l ∈ s, g l • v l).coeff (v j).natDegree =
      g j * (v j).leadingCoeff := by
    rw [finsetSum_coeff]
    apply Finset.sum_eq_single j
    · intro l hls hlj
      by_cases hgl : g l = 0
      · simp [hgl]
      · have hlk : l ∈ k := Finset.mem_filter.mpr ⟨hls,hgl⟩
        have hlt : (v l).natDegree < (v j).natDegree :=
          lt_of_le_of_ne (hmax l hlk) (fun he => hlj (hd he))
        rw [coeff_smul, coeff_eq_zero_of_natDegree_lt hlt, smul_zero]
    · exact fun h => (h hjs).elim
  have hz : g j * (v j).leadingCoeff = 0 := by rw [← hcoeff, hs, coeff_zero]
  exact (mul_ne_zero hgj (leadingCoeff_ne_zero.mpr (hn j))) hz

end MazurTransfer.MixedOriginalFiniteMapDistinctDegree20261019
#print axioms MazurTransfer.MixedOriginalFiniteMapDistinctDegree20261019.linearIndependent_of_injective_natDegree

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: independence of actual parameter-polynomial combinations
of 1,p,q over an integral base in every characteristic.
Named downstream consumer: the actual R[T]-basis of the finite subalgebra.
The canonical R-scalar structure is used; polynomial actions are explicit.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionPolynomialCombinationIndependence
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
open Order13MixedSingleSectionWeightedPolynomialCoordinates
variable (R : Type u) [CommRing R] [IsDomain R]

def generator : Fin 3 → ordinaryCoordinateRing R :=
  fun i => if i = 0 then 1 else if i = 1 then p R else q R

omit [IsDomain R] in
theorem weightedPowers_eq (i : Fin 3) (n : ℕ) :
    weightedPowers R (i,n) = generator R i * t R ^ n := by
  fin_cases i <;> simp [weightedPowers,generator]

theorem weightedPowers_linearIndependent :
    LinearIndependent R (weightedPowers R) := by
  apply LinearIndependent.of_comp (firstComponent R)
  apply MixedOriginalFiniteMapDistinctDegree20261019.linearIndependent_of_injective_natDegree
  · exact weighted_first_nonzero R
  · intro i j hij
    apply weight_injective
    simpa only [Function.comp_apply, weighted_first_degree R] using hij

theorem polynomial_combination_expansion (F : Fin 3 → Polynomial R) (N : ℕ)
    (hN : ∀ i, (F i).natDegree < N) :
    (∑ i, aeval (t R) (F i) * generator R i) =
      ∑ k ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ Finset.range N),
        (F k.1).coeff k.2 • weightedPowers R k := by
  rw [Finset.sum_product (Finset.univ : Finset (Fin 3)) (Finset.range N)
    (fun k => (F k.1).coeff k.2 • weightedPowers R k)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [aeval_eq_sum_range' (hN i) (t R), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [weightedPowers_eq]
  simp only [Algebra.smul_def]
  ring

theorem polynomial_combination_kernel
    (F : Fin 3 → Polynomial R)
    (hF : ∑ i, aeval (t R) (F i) * generator R i = 0) : ∀ i, F i = 0 := by
  classical
  let N : ℕ := (Finset.univ.image (fun i => (F i).natDegree)).max' (by simp) + 1
  have hN : ∀ i, (F i).natDegree < N := by
    intro i
    exact Nat.lt_succ_of_le (Finset.le_max' _ _ (by simp))
  have hs : ∑ k ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ Finset.range N),
      (F k.1).coeff k.2 • weightedPowers R k = 0 := by
    rw [← polynomial_combination_expansion R F N hN]
    exact hF
  have hcoeff := (linearIndependent_iff'.mp (weightedPowers_linearIndependent R))
    (((Finset.univ : Finset (Fin 3)) ×ˢ Finset.range N)) (fun k => (F k.1).coeff k.2) hs
  intro i
  apply Polynomial.ext
  intro n
  by_cases hn : n < N
  · simpa using hcoeff (i,n) (by simp [hn])
  · rw [coeff_eq_zero_of_natDegree_lt (by have := hN i; omega), coeff_zero]

end MazurTransfer.Order13MixedSingleSectionPolynomialCombinationIndependence
#print axioms MazurTransfer.Order13MixedSingleSectionPolynomialCombinationIndependence.polynomial_combination_kernel

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: independence of the actual inverse parameter combinations
of 1,p/t²,q/t² inside the ordinary t-localization.
Named downstream consumer: the inverse finite algebra's explicit R[S]-basis
and all evaluated-quotient bases for whole single-section FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterPolynomialCombinationIndependence
open Polynomial
open Order13DyadicMixedQuadraticCharts
open Order13MixedSingleSectionPolynomialIdentities (t p q)
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
open Order13MixedInverseParameterPolynomialIdentities (s a b)
variable (R : Type u) [CommRing R]

def tImage : ordinaryParameterLocalization R :=
  algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R)

theorem tImage_mul_s : tImage R * s R = 1 :=
  IsLocalization.Away.mul_invSelf (t R)

theorem reflected_aeval (F : Polynomial R) (N : ℕ) (hF : F.natDegree ≤ N) :
    aeval (tImage R) (F.reflect N) = aeval (s R) F * tImage R ^ N := by
  let := (Order13MixedSingleSectionParameterRegular.inverse_parameter_isUnit R).invertible
  have hi : ⅟(s R) = tImage R := invOf_eq_left_inv (tImage_mul_s R)
  have h := eval₂_reflect_mul_pow (algebraMap R (ordinaryParameterLocalization R)) (s R) N F hF
  rw [hi] at h
  change aeval (tImage R) (F.reflect N) * s R ^ N = aeval (s R) F at h
  rw [← h, mul_assoc, ← mul_pow, mul_comm (s R), tImage_mul_s, one_pow, mul_one]

def generator : Fin 3 → ordinaryParameterLocalization R :=
  fun i => if i = 0 then 1 else if i = 1 then a R else b R

theorem clear_a (N : ℕ) : a R * tImage R ^ (N + 2) =
    algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (p R) * tImage R ^ N := by
  have ht : (s R * tImage R) ^ 2 = 1 := by
    rw [mul_comm, tImage_mul_s, one_pow]
  dsimp [a]
  rw [pow_add]
  calc
    _ = algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (p R) *
      (s R * tImage R) ^ 2 * tImage R ^ N := by ring
    _ = _ := by rw [ht, mul_one]

theorem clear_b (N : ℕ) : b R * tImage R ^ (N + 2) =
    algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (q R) * tImage R ^ N := by
  have ht : (s R * tImage R) ^ 2 = 1 := by
    rw [mul_comm, tImage_mul_s, one_pow]
  dsimp [b]
  rw [pow_add]
  calc
    _ = algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (q R) *
      (s R * tImage R) ^ 2 * tImage R ^ N := by ring
    _ = _ := by rw [ht, mul_one]

variable [IsDomain R]

theorem polynomial_combination_kernel 
    (F : Fin 3 → Polynomial R)
    (hF : ∑ i, aeval (s R) (F i) * generator R i = 0) : ∀ i, F i = 0 := by
  classical
  let N : ℕ := (F 0).natDegree + (F 1).natDegree + (F 2).natDegree
  have hN (i : Fin 3) : (F i).natDegree ≤ N := by
    fin_cases i <;> dsimp [N] <;> omega
  let G : Fin 3 → Polynomial R :=
    ![(F 0).reflect N * X ^ 2, (F 1).reflect N, (F 2).reflect N]
  have hzero : ∑ i, aeval (t R) (G i) *
      Order13MixedSingleSectionPolynomialCombinationIndependence.generator R i = 0 := by
    apply Order13MixedSingleSectionParameterRegular.localization_injective R
    simp only [map_sum, map_mul, map_zero]
    let φ := IsScalarTower.toAlgHom R (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)
    change ∑ i, φ (aeval (t R) (G i)) *
      φ (Order13MixedSingleSectionPolynomialCombinationIndependence.generator R i) = 0
    simp only [← aeval_algHom_apply]
    have he : ∑ i, aeval (tImage R) (G i) *
        algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)
          (Order13MixedSingleSectionPolynomialCombinationIndependence.generator R i) =
      (∑ i, aeval (s R) (F i) * generator R i) * tImage R ^ (N + 2) := by
      simp [Fin.sum_univ_three, G,
        Order13MixedSingleSectionPolynomialCombinationIndependence.generator, generator]
      rw [reflected_aeval R (F 0) N (hN 0), reflected_aeval R (F 1) N (hN 1),
        reflected_aeval R (F 2) N (hN 2)]
      have ha := clear_a R N
      have hb := clear_b R N
      rw [pow_add] at ha hb ⊢
      linear_combination -(aeval (s R) (F 1)) * ha - (aeval (s R) (F 2)) * hb
    change ∑ i, aeval (tImage R) (G i) *
      algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)
        (Order13MixedSingleSectionPolynomialCombinationIndependence.generator R i) = 0
    rw [he, hF, zero_mul]
  have hk := Order13MixedSingleSectionPolynomialCombinationIndependence.polynomial_combination_kernel R
    G hzero
  intro i
  fin_cases i
  · have h := hk 0
    change (F 0).reflect N * X ^ 2 = 0 at h
    exact reflect_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 X_ne_zero))
  · have h := hk 1
    change (F 1).reflect N = 0 at h
    exact reflect_eq_zero_iff.mp h
  · have h := hk 2
    change (F 2).reflect N = 0 at h
    exact reflect_eq_zero_iff.mp h

end MazurTransfer.Order13MixedInverseParameterPolynomialCombinationIndependence
#print axioms MazurTransfer.Order13MixedInverseParameterPolynomialCombinationIndependence.reflected_aeval
#print axioms MazurTransfer.Order13MixedInverseParameterPolynomialCombinationIndependence.polynomial_combination_kernel

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite subalgebra has the explicit R[S]-basis
1,p/t²,q/t² over any integral base. Named downstream consumer:
finite free level sets in single-section FiniteMapData.
The parameter S acts by s=1/t, with no assumed module basis.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial Module
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
open Order13MixedInverseParameterPolynomialIdentities
open Order13MixedInverseParameterPolynomialCombinationIndependence
variable (R : Type u) [CommRing R] [IsDomain R]

theorem generator_linearIndependent :
    LinearIndependent (Polynomial R) (generator R) := by
  apply Fintype.linearIndependent_iff.mpr
  intro F hF
  apply polynomial_combination_kernel R F
  simpa only [Algebra.smul_def,parameter_algebraMap] using hF

omit [IsDomain R] in
theorem generator_range : Set.range (generator R) = generators R := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [generator,generators]
  · intro hz
    simp only [generators,Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨0,by simp [generator]⟩
    · exact ⟨1,by simp [generator]⟩
    · exact ⟨2,by simp [generator]⟩

noncomputable def candidateBasis :
    Basis (Fin 3) (Polynomial R) (candidateAlgebra R) := by
  change Basis (Fin 3) (Polynomial R) (candidateAlgebra R).toSubmodule
  exact (Basis.span (generator_linearIndependent R)).map
    (LinearEquiv.ofEq _ _ (by
      rw [generator_range]
      exact (candidateAlgebra_eq_span R).symm))

theorem candidateBasis_value (i : Fin 3) :
    (candidateBasis R i : ordinaryParameterLocalization R) = generator R i := by
  simp [candidateBasis]

theorem candidateAlgebra_free :
    Module.Free (Polynomial R) (candidateAlgebra R) := Module.Free.of_basis (candidateBasis R)

theorem candidateAlgebra_finrank :
    Module.finrank (Polynomial R) (candidateAlgebra R) = 3 := by
  simpa using Module.finrank_eq_card_basis (candidateBasis R)

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.generator_linearIndependent
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateBasis_value
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra_free
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete checked quotient/base-change identification from official
Anthropic FLT, pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: actual algebraic level sets of the parameter in B, with
finite freeness and rank three in every characteristic. Named downstream consumer: full inverse-parameter
FiniteMapData after the still-separate actual affine-open identification.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial Module
open scoped TensorProduct
variable (R : Type u) [CommRing R] [IsDomain R]

scoped instance candidateBaseAlgebra : Algebra R (candidateAlgebra R) :=
  ((algebraMap (Polynomial R) (candidateAlgebra R)).comp (Polynomial.C)).toAlgebra

scoped instance candidateBaseTower : IsScalarTower R (Polynomial R) (candidateAlgebra R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem candidate_base_algebraMap_coe (r : R) :
    (algebraMap R (candidateAlgebra R) r : Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R) =
      algebraMap R (Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R) r := by
  change aeval (Order13MixedInverseParameterPolynomialIdentities.s R) (C r) = _
  exact aeval_C _ _

def parameterElement : candidateAlgebra R :=
  algebraMap (Polynomial R) (candidateAlgebra R) X

variable (S : Type u) [CommRing S] [Algebra R S]

abbrev levelSet (s : S) :=
  S ⊗[R] candidateAlgebra R ⧸
    Ideal.span {(1 : S) ⊗ₜ[R] parameterElement R - s ⊗ₜ[R] (1 : candidateAlgebra R)}

noncomputable def levelSetBasis (s : S) :
    Basis (Fin 3) S (levelSet R S s) := by
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R (candidateAlgebra R) S (parameterElement R) s (by rfl) (by
      change aeval s X = s
      exact aeval_X s)
  exact ((candidateBasis R).baseChange S).map e.symm.toLinearEquiv

theorem levelSet_finite_free_finrank [Nontrivial S] (s : S) :
    Module.Finite S (levelSet R S s) ∧ Module.Free S (levelSet R S s) ∧
      Module.finrank S (levelSet R S s) = 3 := by
  let b := levelSetBasis R S s
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b, by
    simpa using Module.finrank_eq_card_basis b⟩

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSetBasis
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet_finite_free_finrank

end


