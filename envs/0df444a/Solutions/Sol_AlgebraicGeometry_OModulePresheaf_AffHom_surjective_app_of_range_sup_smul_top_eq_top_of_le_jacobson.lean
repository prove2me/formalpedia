-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f75cbc83-a28a-5c81-b983-2a5f636075fc

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace SurjNakayamaAux

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

abbrev A (U : X.affineOpens) : Type u := Γ(X, U.1)

theorem opens_eq_top (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) [UniversallyClosed f]
    (W : X.Opens) (hW : ∀ x : X, I ≤ (f.base x).asIdeal → x ∈ W) : W = ⊤ := by
  by_contra hne
  set Z : Set X := (W : Set X)ᶜ with hZ
  have hZc : IsClosed Z := W.2.isClosed_compl
  have hZne : Z.Nonempty := by
    by_contra h
    apply hne
    rw [Set.not_nonempty_iff_eq_empty, hZ, Set.compl_empty_iff] at h
    exact TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_top.symm)
  have himg : IsClosed (f.base '' Z) := f.isClosedMap Z hZc
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp himg
  have hJtop : J ≠ ⊤ := by
    intro hJtop
    have hempty : PrimeSpectrum.zeroLocus (J : Set R) = ∅ := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr hJtop
    obtain ⟨z, hz⟩ := hZne
    have : f.base z ∈ f.base '' Z := ⟨z, hz, rfl⟩
    rw [hJ, hempty] at this
    exact this
  obtain ⟨M, hMmax, hJM⟩ := Ideal.exists_le_maximal J hJtop
  have hMmem : (⟨M, hMmax.isPrime⟩ : PrimeSpectrum R) ∈ f.base '' Z := by
    rw [hJ]
    exact hJM
  obtain ⟨z, hz, hfz⟩ := hMmem
  have hIM : I ≤ (f.base z).asIdeal := by
    rw [hfz]
    intro r hr
    have hr' : r ∈ (⊥ : Ideal R).jacobson := hI hr
    rw [Ideal.jacobson, Submodule.mem_sInf] at hr'
    exact hr' M ⟨bot_le, hMmax⟩
  exact hz (hW z hIM)

theorem mem_basicOpen_of_sub_one_mem (I : Ideal R) (W : X.affineOpens) (s : A W)
    (hs : letI := Scheme.TwoAffineOpenCover.algebraOfHom f W.1; s - 1 ∈ I.map (algebraMap R (A W)))
    (x : X) (hxW : x ∈ W.1) (hx : I ≤ (f.base x).asIdeal) : x ∈ X.basicOpen s := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f W.1
  rw [Scheme.mem_basicOpen (hx := hxW)]

  have key : ∀ a ∈ I.map (algebraMap R (A W)),
      X.presheaf.germ W.1 x hxW a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ =>
      X.presheaf.germ W.1 x hxW a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨r, hr, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen (hx := hxW)]

      intro hmem
      have e : (algebraMap R (A W)) r =
          (X.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op).hom (f.appTop ((Scheme.ΓSpecIso (.of R)).inv.hom r)) := rfl
      rw [e, Scheme.basicOpen_res] at hmem
      have h2 : x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of R)).inv.hom r)) := hmem.2
      rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h2
      exact (PrimeSpectrum.mem_basicOpen _ _).mp h2 (hx hr)
    · show X.presheaf.germ W.1 x hxW 0 ∈ _
      rw [map_zero]
      exact Ideal.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb
    · intro c a _ ha
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ ha
  have h1 : X.presheaf.germ W.1 x hxW s = 1 - (-(X.presheaf.germ W.1 x hxW (s - 1))) := by
    rw [map_sub, map_one]; ring
  rw [h1]
  refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_
  rw [← IsLocalRing.mem_maximalIdeal]
  exact neg_mem (key _ hs)

variable {F G : OModulePresheaf f} (φ : AffHom F G)

def N (U : X.affineOpens) : Submodule (A U) (G.obj U.1) where
  carrier := {g | ∃ x, φ.app U x = g}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro a _ ⟨x, rfl⟩
    exact ⟨a • x, φ.app_smul U a x⟩

theorem mem_N {U : X.affineOpens} {g : G.obj U.1} : g ∈ N φ U ↔ ∃ x, φ.app U x = g := Iff.rfl

theorem exists_sub_one_mem (I : Ideal R) (W : X.affineOpens) [Module.Finite (A W) (G.obj W.1)]
    (h : LinearMap.range (φ.app W) ⊔ I • (⊤ : Submodule R (G.obj W.1)) = ⊤) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f W.1
    ∃ s : A W, s - 1 ∈ I.map (algebraMap R (A W)) ∧ ∀ g : G.obj W.1, ∃ x, φ.app W x = s • g := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f W.1
  haveI := G.isScalarTower W.1
  set I' : Ideal (A W) := I.map (algebraMap R (A W)) with hI'

  have hle : (⊤ : Submodule (A W) (G.obj W.1 ⧸ N φ W)) ≤ I' • ⊤ := by
    rintro q -
    induction q using Submodule.Quotient.induction_on with
    | H g =>
      have hg : g ∈ LinearMap.range (φ.app W) ⊔ I • (⊤ : Submodule R (G.obj W.1)) := by rw [h]; trivial
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
      have h0 : (Submodule.Quotient.mk (φ.app W x) : G.obj W.1 ⧸ N φ W) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
      rw [Submodule.Quotient.mk_add, h0, zero_add]
      refine Submodule.smul_induction_on hz (fun r hr g' _ => ?_) (fun a b ha hb => ?_)
      · rw [← algebraMap_smul (A W) r g', Submodule.Quotient.mk_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
      · rw [Submodule.Quotient.mk_add]
        exact Submodule.add_mem _ ha hb
  obtain ⟨s, hs1, hs0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I' (⊤ : Submodule (A W) (G.obj W.1 ⧸ N φ W))
      Module.Finite.fg_top hle
  refine ⟨s, hs1, fun g => ?_⟩
  have := hs0 (Submodule.Quotient.mk g) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  exact this

theorem algebraMap_basicOpen (U : X.affineOpens) (t : A U) :
    algebraMap (A U) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := rfl

theorem surj_basicOpen_of_smul_mem (hGq : G.IsQuasicoherent) (W : X.affineOpens) (s : A W)
    (hs : ∀ g : G.obj W.1, ∃ x, φ.app W x = s • g) :
    Function.Surjective (φ.app (X.affineBasicOpen s)) := by
  haveI := W.2.isLocalization_basicOpen s
  have hD : (X.affineBasicOpen s).1 ≤ W.1 := X.basicOpen_le s
  let ρ : A W →+* A (X.affineBasicOpen s) := (X.presheaf.map (homOfLE hD).op).hom
  intro g
  obtain ⟨n, y, hy⟩ := (hGq W s).1 g
  obtain ⟨x, hx⟩ := hs y
  have hy' : G.res hD y = ρ (s ^ n) • g := hy

  have h1 : φ.app (X.affineBasicOpen s) (F.res hD x) = ρ (s ^ (n + 1)) • g := by
    rw [φ.naturality_apply (U := X.affineBasicOpen s) (U' := W) hD x, hx, G.res_smul, hy', smul_smul]
    change (ρ s * ρ (s ^ n)) • g = _
    rw [← map_mul, pow_succ']
  have hu : IsUnit (ρ (s ^ (n + 1))) :=
    IsLocalization.map_units (M := Submonoid.powers s) Γ(X, X.basicOpen s) ⟨s ^ (n + 1), n + 1, rfl⟩
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨v • F.res hD x, ?_⟩
  rw [φ.app_smul, h1, smul_smul, hv, one_smul]

theorem surj_basicOpen (hGq : G.IsQuasicoherent) (U : X.affineOpens) (t : A U)
    (hU : Function.Surjective (φ.app U)) : Function.Surjective (φ.app (X.affineBasicOpen t)) := by
  refine surj_basicOpen_of_smul_mem φ hGq U t fun g => ?_
  obtain ⟨x, hx⟩ := hU (t • g)
  exact ⟨x, hx⟩

theorem surj_of_span_eq_top (hF : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : X.affineOpens)
    (S : Finset (A U)) (hS : Ideal.span (S : Set (A U)) = ⊤)
    (hD : ∀ t : S, Function.Surjective (φ.app (X.affineBasicOpen t.1))) : Function.Surjective (φ.app U) := by
  classical
  intro g

  have hpow : ∀ t : S, ∃ k : ℕ, (t.1 ^ k) • g ∈ N φ U := by
    intro t
    have hDle : (X.affineBasicOpen t.1).1 ≤ U.1 := X.basicOpen_le t.1
    let ρ : A U →+* A (X.affineBasicOpen t.1) := (X.presheaf.map (homOfLE hDle).op).hom
    obtain ⟨xt, hxt⟩ := hD t (G.res hDle g)
    obtain ⟨n, x', hx'⟩ := (hF U t.1).1 xt
    have hx'' : F.res hDle x' = ρ (t.1 ^ n) • xt := hx'

    have h0 : G.res hDle (φ.app U x' - t.1 ^ n • g) = 0 := by
      rw [map_sub, sub_eq_zero, G.res_smul,
        ← φ.naturality_apply (U := X.affineBasicOpen t.1) (U' := U) hDle x', hx'', φ.app_smul, hxt]
    obtain ⟨m, hm⟩ := (hGq U t.1).2 _ h0
    refine ⟨m + n, ?_⟩
    rw [smul_sub, smul_smul, ← pow_add, sub_eq_zero] at hm
    rw [← hm]
    exact ⟨t.1 ^ m • x', φ.app_smul U _ _⟩
  choose k hk using hpow

  set K : ℕ := Finset.univ.sup k with hK
  have hpowK : ∀ t : S, (t.1 ^ K) • g ∈ N φ U := by
    intro t
    have hle : k t ≤ K := Finset.le_sup (Finset.mem_univ t)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hk t)

  have hspan : Ideal.span ((fun a : A U => a ^ K) '' (S : Set (A U))) = ⊤ := Ideal.span_pow_eq_top _ hS K
  let 𝔠 : Ideal (A U) := (N φ U).comap (LinearMap.toSpanSingleton (A U) (G.obj U.1) g)
  have hsub : ((fun a : A U => a ^ K) '' (S : Set (A U))) ⊆ 𝔠 := by
    rintro _ ⟨t, ht, rfl⟩
    change (t ^ K) • g ∈ N φ U
    exact hpowK ⟨t, ht⟩
  have h1 : (1 : A U) ∈ 𝔠 := by
    have := Ideal.span_le.mpr hsub
    rw [hspan] at this
    exact this Submodule.mem_top
  have : (1 : A U) • g ∈ N φ U := h1
  rw [one_smul] at this
  exact this

end SurjNakayamaAux

open SurjNakayamaAux AlgebraicGeometry.OModulePresheaf in

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [UniversallyClosed f]
    {F G : OModulePresheaf f} (hF : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (φ : OModulePresheaf.AffHom F G)
    (h : ∀ U : X.affineOpens, LinearMap.range (φ.app U) ⊔ I • (⊤ : Submodule R (G.obj U.1)) = ⊤)
    (U : X.affineOpens) : Function.Surjective (φ.app U) := by

  have hnak : ∀ W : X.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom f W.1
      ∃ s : A W, s - 1 ∈ I.map (algebraMap R (A W)) ∧ ∀ g : G.obj W.1, ∃ x, φ.app W x = s • g := fun W => by
    haveI : Module.Finite (A W) (G.obj W.1) := hGc W
    exact exists_sub_one_mem φ I W (h W)
  choose s hs1 hs2 using hnak

  have hcov : (⨆ W : X.affineOpens, (X.affineBasicOpen (s W) : X.Opens)) = ⊤ := by
    refine opens_eq_top (f := f) I hI _ fun x hx => ?_
    obtain ⟨W, hxW⟩ : ∃ W : X.affineOpens, x ∈ W.1 := by
      have : x ∈ (⨆ W : X.affineOpens, (W : X.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
      exact Opens.mem_iSup.mp this
    exact Opens.mem_iSup.mpr ⟨W, mem_basicOpen_of_sub_one_mem I W (s W) (hs1 W) x hxW hx⟩

  refine of_affine_open_cover (P := fun V : X.affineOpens => Function.Surjective (φ.app V))
    (fun W : X.affineOpens => X.affineBasicOpen (s W)) hcov U ?_ ?_ ?_
  · exact fun V t hV => surj_basicOpen φ hGq V t hV
  · exact fun V S hS hD => surj_of_span_eq_top φ hF hGq V S hS hD
  · exact fun W => surj_basicOpen_of_smul_mem φ hGq W (s W) (hs2 W)

end
end S_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson (solution)
