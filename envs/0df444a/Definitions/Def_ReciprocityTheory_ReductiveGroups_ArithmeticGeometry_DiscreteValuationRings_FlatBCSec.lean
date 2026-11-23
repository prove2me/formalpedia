-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:40.978953+00:00
-- url     : https://prove2.me/theorems/3e65930a-a023-42de-b7d6-978487a81c80
-- title:
--   Flat BCSec
-- statement:
--   Definitions and structural lemmas for Flat BCSec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
section Cover
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi
end Cover
section Cech
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {Y : Scheme.{0}} (L : LB Y) {n : ℕ} (V : Fin n → Y.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))
include hVc in
lemma pair_le (k l : Fin n) : V k ⊓ V l ≤ L.U (c k) ⊓ L.U (c l) := inf_le_inf (hVc k) (hVc l)
def ev (σ : LB.Sec L) : ∀ k, Γ(Y, V k) := fun k => rs (hVc k) (σ.f (c k))
def dfun (f : ∀ k, Γ(Y, V k)) : ∀ k l, Γ(Y, V k ⊓ V l) := fun k l =>
  rs inf_le_left (f k) - (res (pair_le L V c hVc k l) (L.g (c k) (c l))).val * rs inf_le_right (f l)
end Cech
section Pushout
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
def algX (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
include H in

theorem isPushout_sections (U : X.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (algX p U)) (CommRingCat.ofHom (algebraMap R S))
      (φ.appLE U (φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤) inf_le_left) (CommRingCat.ofHom (algX p' (φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))) := by
  have hST : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ Spec.map (CommRingCat.ofHom (algebraMap R S)) ⁻¹ᵁ ⊤ := le_top
  have hSX : U ≤ p ⁻¹ᵁ ⊤ := le_top
  haveI := isIso_pushoutSection_of_isAffineOpen H hST hSX rfl (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H hST hSX rfl).1 inferInstance
  refine hP.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [algX]
  · have e : (Spec.map (CommRingCat.ofHom (algebraMap R S))).appLE ⊤ ⊤ hST =
        (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      congr 1
    rw [e]
    exact Scheme.ΓSpecIso_naturality _
  · simp
  · ext x
    simp only [algX, CommRingCat.comp_apply, CommRingCat.hom_ofHom, RingHom.comp_apply, Iso.refl_hom,
      CommRingCat.id_apply]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of S)).hom, Iso.hom_inv_id, CommRingCat.id_apply]
omit [Algebra R S] in
lemma rs_algX (U U' : X.Opens) (h : U' ≤ U) (r : R) :
    ReciprocityTheory.ChartRestriction.G.DVR.rs h (algX p U r) = algX p U' r := by
  simp only [algX, RingHom.comp_apply, ReciprocityTheory.ChartRestriction.G.DVR.rs]
  erw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
def eTens (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (algX p U).toAlgebra
    Γ(X, U) ⊗[R] S ≃+* Γ(X', φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤) :=
  letI := (algX p U).toAlgebra
  ((CommRingCat.isPushout_tensorProduct R Γ(X, U) S).isoIsPushout _ _
    (isPushout_sections p p' φ H U hU)).commRingCatIsoToRingEquiv
omit [Algebra R S] in

def rsL (U U' : X.Opens) (h : U' ≤ U) :
    letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
    Γ(X, U) →ₗ[R] Γ(X, U') :=
  letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
  { toFun := ReciprocityTheory.ChartRestriction.G.DVR.rs h
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.id_apply]
      rw [ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX] }
omit [Algebra R S] in

def mulL (U : X.Opens) (u : Γ(X, U)) :
    letI := (algX p U).toAlgebra
    Γ(X, U) →ₗ[R] Γ(X, U) :=
  letI := (algX p U).toAlgebra
  { toFun := fun a => u * a
    map_add' := fun a b => mul_add u a b
    map_smul' := fun r a => by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.id_apply]
      ring }
end Pushout
section Main
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
omit [Algebra R S] in

def smulSec (L : LB X) (a : R) (θ : LB.Sec L) : LB.Sec L where
  f i := algX p (L.U i) a * θ.f i
  compat i j := by
    show ReciprocityTheory.ChartRestriction.G.DVR.rs _ (_ * _) = _ * ReciprocityTheory.ChartRestriction.G.DVR.rs _ (_ * _)
    have e : ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (θ.f i) =
        (L.g i j).val * ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (θ.f j) := θ.compat i j
    rw [rs_mul, rs_mul, rs_algX, rs_algX, e]
    ring
end Main
section IsoRel
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Y : Scheme.{0}} {L M : LB Y}
def IsoRel (w : LB.Iso L M) (s : LB.Sec L) (s' : LB.Sec M) : Prop :=
  ∀ (i : M.ι) (k : L.ι),
    (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ L.U k ≤ M.U i)).op).hom (s'.f i) =
      (show Γ(Y, M.U i ⊓ L.U k) from (w.s (i, k) : Γ(Y, (LB.div M L).U (i, k)))) *
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ L.U k ≤ L.U k)).op).hom (s.f k)
end IsoRel
section IsoMain
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
end IsoMain
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC


