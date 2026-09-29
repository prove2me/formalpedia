-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/df3dc5ab-7873-5161-9a59-36d976cd5b04

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mUntwist

open AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  (q : P ⟶ Spec (CommRingCat.of A)) (d m : ℕ)

section Generic

variable {q}

theorem restrictFun_injective_of_ge {W W' : P.Opens} (h : W ≤ W') (h' : W' ≤ W) :
    Function.Injective (restrictFun h) := by
  intro a b hab
  have := congrArg (restrictFun h') hab
  rwa [restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_refl, restrictFun_refl] at this

theorem res_res_eq_self (G : OModulePresheaf q) {W W' : P.Opens} (h : W ≤ W') (h' : W' ≤ W) (x : G.obj W) :
    G.res h (G.res h' x) = x := by
  rw [G.res_res]; exact G.res_refl_apply W x

variable (q) in

theorem isQuasicoherent_unit : (unit q).IsQuasicoherent := by
  intro U f
  haveI := U.2.isLocalization_basicOpen f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) (show Γ(P, P.basicOpen f) from x)
    refine ⟨n, a, ?_⟩
    change (P.presheaf.map (homOfLE (P.basicOpen_le f)).op).hom a
      = (P.presheaf.map (homOfLE (P.basicOpen_le f)).op).hom (f ^ n) * (show Γ(P, P.basicOpen f) from x)
    rw [mul_comm]
    exact h.symm
  · have h0 : algebraMap Γ(P, U.1) Γ(P, P.basicOpen f) (show Γ(P, U.1) from y) = 0 := hy
    obtain ⟨⟨_, n, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).mp h0
    exact ⟨n, h⟩

theorem isQuasicoherent_pow' {G : OModulePresheaf q} (hG : G.IsQuasicoherent) (n : ℕ) :
    (G.pow n).IsQuasicoherent := by
  intro U f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · choose k y hy using fun j : Fin n => (hG U f).1 (x j)
    refine ⟨Finset.univ.sup k, fun j => (f ^ (Finset.univ.sup k - k j)) • y j, funext fun j => ?_⟩
    rw [pow_res_apply]
    change G.res (P.basicOpen_le f) ((f ^ (Finset.univ.sup k - k j)) • y j)
      = (P.presheaf.map (homOfLE (P.basicOpen_le f)).op).hom (f ^ Finset.univ.sup k) • x j
    rw [G.res_smul, hy j, smul_smul, ← map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := k) (Finset.mem_univ j))]
  · choose k hk using fun j : Fin n => (hG U f).2 (y j) (congrFun hy j)
    refine ⟨Finset.univ.sup k, funext fun j => ?_⟩
    change f ^ Finset.univ.sup k • y j = 0
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := k) (Finset.mem_univ j)), pow_add, mul_smul, hk j]
    exact smul_zero _

@[scoped simp] theorem twistObj_sub_val {U : P.Opens} (g g' : twistObj q ι d U) : (g - g').val = g.val - g'.val := rfl

end Generic

def Xsec (a : Fin (r + 1)) (U : P.Opens) : twistObj q ι d U :=
  ⟨fun k => restrictFun (inf_le_right : U ⊓ pullbackChart ι k ≤ pullbackChart ι k) (frameUnit ι k a) ^ d, by
    intro k k'
    have hW : (U ⊓ pullbackChart ι k) ⊓ pullbackChart ι k' ≤ pullbackOverlap ι k k' := by
      rw [pullbackOverlap_eq_inf]; exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have key := congrArg (restrictFun hW) (frameUnit_cocycle ι k k' a)
    rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
    simp only [map_pow, restrictFun_restrictFun]
    rw [← mul_pow, ← key]⟩

@[scoped simp] theorem Xsec_val (a : Fin (r + 1)) (U : P.Opens) (k : Fin (r + 1)) :
    (Xsec ι q d a U).val k = restrictFun (inf_le_right : U ⊓ pullbackChart ι k ≤ pullbackChart ι k) (frameUnit ι k a) ^ d :=
  rfl

theorem res_Xsec (a : Fin (r + 1)) {U U' : P.Opens} (h : U ≤ U') :
    (twist q ι d).res h (Xsec ι q d a U') = Xsec ι q d a U := by
  refine twistObj.ext (funext fun k => ?_)
  rw [twist_res_val, Xsec_val, Xsec_val, map_pow, restrictFun_restrictFun]

abbrev Src (n m : ℕ) : OModulePresheaf q := ((unit q).pow (n + 1)).pow m

abbrev Tgt : OModulePresheaf q := (((twist q ι d).pow (r + 1)).pow (r + 1)).pow m

def ηfun (U : P.Opens) (f : Fin m → Fin (r + 1) → Γ(P, U)) :
    Fin m → Fin (r + 1) → Fin (r + 1) → twistObj q ι d U :=
  fun l i a => f l i • Xsec ι q d a U - f l a • Xsec ι q d i U

theorem ηfun_apply (U : P.Opens) (f : Fin m → Fin (r + 1) → Γ(P, U)) (l i a) :
    ηfun ι q d m U f l i a = f l i • Xsec ι q d a U - f l a • Xsec ι q d i U := rfl

theorem ηfun_add (U : P.Opens) (f g : Fin m → Fin (r + 1) → Γ(P, U)) :
    ηfun ι q d m U (f + g) = ηfun ι q d m U f + ηfun ι q d m U g := by
  funext l i a
  simp only [ηfun_apply, Pi.add_apply, add_smul]
  abel

theorem ηfun_smul (U : P.Opens) (c : Γ(P, U)) (f : Fin m → Fin (r + 1) → Γ(P, U)) :
    ηfun ι q d m U (c • f) = c • ηfun ι q d m U f := by
  funext l i a
  simp only [ηfun_apply, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sub]

theorem res_ηfun {U U' : P.Opens} (h : U ≤ U') (f : Fin m → Fin (r + 1) → Γ(P, U')) (l i a) :
    (twist q ι d).res h (ηfun ι q d m U' f l i a) = ηfun ι q d m U (fun l i => restrictFun h (f l i)) l i a := by
  refine twistObj.ext (funext fun k => ?_)
  simp only [twist_res_val, ηfun_apply, twistObj_sub_val, Pi.sub_apply, twistObj.smul_val, Xsec_val, map_sub,
    map_mul, map_pow, restrictFun_restrictFun]

def η : Hom (Src q r m) (Tgt ι q d m) where
  app U :=
    { toFun := fun f => ηfun ι q d m U f
      map_add' := fun f g => ηfun_add ι q d m U f g
      map_smul' := fun c f => ηfun_smul ι q d m U ((Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap c) f }
  app_smul U c f := ηfun_smul ι q d m U c f
  naturality h :=
    LinearMap.ext fun f => funext fun l => funext fun i => funext fun a => (res_ηfun ι q d m h f l i a).symm

theorem η_app_apply (U : P.Opens) (f : Fin m → Fin (r + 1) → Γ(P, U)) (l i a) :
    (η ι q d m).app U f l i a = f l i • Xsec ι q d a U - f l a • Xsec ι q d i U := rfl

def E : OModulePresheaf q := OModulePresheaf.ker (η ι q d m)

theorem isQuasicoherent_E [IsSeparated q] [IsAffineHom ι] : (E ι q d m).IsQuasicoherent :=
  isQuasicoherent_ker (η ι q d m) (isQuasicoherent_pow' (isQuasicoherent_pow' (isQuasicoherent_unit q) _) _)
    (isQuasicoherent_pow' (isQuasicoherent_pow' (isQuasicoherent_pow' (isQuasicoherent_twist q ι d) _) _) _)

variable {ι q d m} in

abbrev cf {W : P.Opens} (e : (E ι q d m).obj W) (l : Fin m) (i : Fin (r + 1)) : Γ(P, W) := e.1 l i

section Chart

variable {ι q d m}

theorem ker_comp {j : Fin (r + 1)} {W : P.Opens} (hW : W ≤ pullbackChart ι j) (e : (E ι q d m).obj W)
    (l : Fin m) (i : Fin (r + 1)) :
    cf e l i = restrictFun hW (frameUnit ι j i) ^ d * cf e l j := by
  have hk : (η ι q d m).app W e.1 = 0 := LinearMap.mem_ker.mp e.2
  have h0 : ηfun ι q d m W (cf e) l i j = 0 := congrFun (congrFun (congrFun hk l) i) j
  rw [ηfun_apply] at h0
  have h1 : cf e l i • Xsec ι q d j W = cf e l j • Xsec ι q d i W := sub_eq_zero.mp h0
  have h2 := congrArg (fun g : twistObj q ι d W => g.val j) h1
  simp only [twistObj.smul_val, Xsec_val, frameUnit_self, map_one, one_pow, mul_one] at h2

  refine restrictFun_injective_of_ge (inf_le_left : W ⊓ pullbackChart ι j ≤ W) (le_inf le_rfl hW) ?_
  rw [h2, map_mul, map_pow, restrictFun_restrictFun, mul_comm]

def evE (j : Fin (r + 1)) (W : P.Opens) (_hW : W ≤ pullbackChart ι j) :
    (E ι q d m).obj W →ₗ[Γ(P, W)] (Fin m → Γ(P, W)) where
  toFun e := fun l => cf e l j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evE_apply (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (e : (E ι q d m).obj W) (l : Fin m) :
    evE j W hW e l = cf e l j := rfl

theorem ηfun_liftFun_eq_zero (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (c : Fin m → Γ(P, W)) :
    ηfun ι q d m W (fun l i => restrictFun hW (frameUnit ι j i) ^ d * c l) = 0 := by
  funext l i a
  rw [ηfun_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
  refine twistObj.ext (funext fun k => ?_)
  rw [twistObj_sub_val, Pi.sub_apply, twistObj.smul_val, twistObj.smul_val, Xsec_val, Xsec_val,
    twistObj.zero_val, Pi.zero_apply, map_mul, map_mul, map_pow, map_pow, restrictFun_restrictFun,
    restrictFun_restrictFun]

  have hWk : W ⊓ pullbackChart ι k ≤ pullbackOverlap ι k j := by
    rw [pullbackOverlap_eq_inf]; exact le_inf inf_le_right (inf_le_left.trans hW)
  have ka := congrArg (restrictFun hWk) (frameUnit_cocycle ι k j a)
  have ki := congrArg (restrictFun hWk) (frameUnit_cocycle ι k j i)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at ka ki
  rw [← ka, ← ki]
  ring

variable (q d m) in

def liftE (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) :
    (Fin m → Γ(P, W)) →ₗ[Γ(P, W)] (E ι q d m).obj W where
  toFun c := ⟨show (Src q r m).obj W from fun l i => restrictFun hW (frameUnit ι j i) ^ d * c l,
    LinearMap.mem_ker.mpr (ηfun_liftFun_eq_zero j W hW c)⟩
  map_add' c c' := by
    refine Subtype.ext (funext fun l => funext fun i => ?_)
    change restrictFun hW (frameUnit ι j i) ^ d * (c l + c' l)
      = restrictFun hW (frameUnit ι j i) ^ d * c l + restrictFun hW (frameUnit ι j i) ^ d * c' l
    rw [mul_add]
  map_smul' a c := by
    refine Subtype.ext (funext fun l => funext fun i => ?_)
    change restrictFun hW (frameUnit ι j i) ^ d * (a * c l) = a * (restrictFun hW (frameUnit ι j i) ^ d * c l)
    ring

theorem liftE_val (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (c : Fin m → Γ(P, W)) (l i) :
    cf (liftE q d m j W hW c) l i = restrictFun hW (frameUnit ι j i) ^ d * c l := rfl

theorem evE_liftE (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (c : Fin m → Γ(P, W)) :
    evE j W hW (liftE q d m j W hW c) = c := by
  funext l
  rw [evE_apply, liftE_val, frameUnit_self, map_one, one_pow, one_mul]

theorem liftE_evE (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (e : (E ι q d m).obj W) :
    liftE q d m j W hW (evE j W hW e) = e := by
  refine Subtype.ext (funext fun l => funext fun i => ?_)
  change cf (liftE q d m j W hW (evE j W hW e)) l i = cf e l i
  rw [liftE_val, evE_apply, ← ker_comp hW e l i]

theorem evE_surjective (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) :
    Function.Surjective (evE (ι := ι) (q := q) (d := d) (m := m) j W hW) :=
  fun c => ⟨liftE q d m j W hW c, evE_liftE j W hW c⟩

variable (q d m) in

def chartE (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) :
    (E ι q d m).obj W ≃ₗ[Γ(P, W)] (Fin m → Γ(P, W)) :=
  { evE j W hW with
    invFun := liftE q d m j W hW
    left_inv := liftE_evE j W hW
    right_inv := evE_liftE j W hW }

theorem evE_res (j : Fin (r + 1)) {W W' : P.Opens} (h : W ≤ W') (hW' : W' ≤ pullbackChart ι j)
    (e : (E ι q d m).obj W') (l : Fin m) :
    evE j W (h.trans hW') ((E ι q d m).res h e) l = restrictFun h (evE j W' hW' e l) := rfl

theorem evE_change (j j' : Fin (r + 1)) (W : P.Opens) (hWj : W ≤ pullbackChart ι j) (hWj' : W ≤ pullbackChart ι j')
    (e : (E ι q d m).obj W) (l : Fin m) :
    evE j' W hWj' e l = restrictFun hWj (frameUnit ι j j') ^ d * evE j W hWj e l := by
  rw [evE_apply, evE_apply]; exact ker_comp hWj e l j'

end Chart

section Coherent

variable [IsSeparated q] [IsAffineHom ι] (U : P.affineOpens)

def smallFuns : Set Γ(P, U.1) := {f | ∃ j : Fin (r + 1), P.basicOpen f ≤ pullbackChart ι j}

omit [IsSeparated q] in

theorem span_smallFuns : Ideal.span (smallFuns ι U) = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff]
  intro x hx
  have hcov : (⨆ j : ULift.{u} (Fin (r + 1)), (ProjSpace.stdCoverPullback ι).U j) = ⊤ :=
    (ProjSpace.stdCoverPullback ι).iSup_eq_top
  have hx' : x ∈ (⨆ j : ULift.{u} (Fin (r + 1)), (ProjSpace.stdCoverPullback ι).U j) := by
    rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  obtain ⟨f, hfle, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hj⟩ hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, ⟨j.down, hfle⟩⟩, hxf⟩

section Local

variable (f : Γ(P, U.1))

scoped instance moduleU : Module Γ(P, U.1) ((E ι q d m).obj (P.basicOpen f)) :=
  (E ι q d m).moduleRestrict (P.basicOpen_le f)

scoped instance isScalarTower_U : IsScalarTower Γ(P, U.1) Γ(P, P.basicOpen f) ((E ι q d m).obj (P.basicOpen f)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

scoped instance isLocalization_U : IsLocalization.Away f Γ(P, P.basicOpen f) := U.2.isLocalization_basicOpen f

theorem isLocalizedModule_res :
    IsLocalizedModule.Away f ((E ι q d m).resₗ (P.basicOpen_le f) :
      (E ι q d m).obj U.1 →ₗ[Γ(P, U.1)] (E ι q d m).obj (P.basicOpen f)) :=
  isLocalizedModule_res_of_isQuasicoherent (E ι q d m) (isQuasicoherent_E ι q d m) U f

omit [IsSeparated q] [IsAffineHom ι] in
variable {ι f} in

theorem finite_local {j : Fin (r + 1)} (hf : P.basicOpen f ≤ pullbackChart ι j) :
    Module.Finite Γ(P, P.basicOpen f) ((E ι q d m).obj (P.basicOpen f)) :=
  Module.Finite.equiv (chartE q d m j _ hf).symm

end Local

theorem finite : Module.Finite Γ(P, U.1) ((E ι q d m).obj U.1) := by
  haveI := fun g : smallFuns ι U => isLocalizedModule_res ι q d m U g.1
  refine Module.Finite.of_localizationSpan' (smallFuns ι U) (span_smallFuns ι U)
    (Mₚ := fun g : smallFuns ι U => (E ι q d m).obj (P.basicOpen g.1))
    (Rₚ := fun g : smallFuns ι U => Γ(P, P.basicOpen g.1))
    (fun g => (E ι q d m).resₗ (P.basicOpen_le g.1)) fun g => ?_
  obtain ⟨j, hj⟩ := g.2
  exact finite_local q d m U hj

theorem isCoherent_E : (E ι q d m).IsCoherent := fun U => finite ι q d m U

end Coherent

section Untwisting

variable {ι}

def evT (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) : (twist q ι d).obj W ≃ₗ[Γ(P, W)] Γ(P, W) :=
  Classical.choose (exists_linearEquiv_twistObj_of_le_pullbackChart q ι d hW)

theorem restrictFun_evT (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (g : (twist q ι d).obj W) :
    restrictFun (inf_le_left : W ⊓ pullbackChart ι j ≤ W) (evT q d j W hW g) = g.val j :=
  (Classical.choose_spec (exists_linearEquiv_twistObj_of_le_pullbackChart q ι d hW)).1 g

theorem evT_res (j : Fin (r + 1)) {W W' : P.Opens} (h : W' ≤ W) (hW : W ≤ pullbackChart ι j) (g : (twist q ι d).obj W) :
    restrictFun h (evT q d j W hW g) = evT q d j W' (h.trans hW) ((twist q ι d).res h g) := by
  refine restrictFun_injective_of_ge (inf_le_left : W' ⊓ pullbackChart ι j ≤ W') (le_inf le_rfl (h.trans hW)) ?_
  rw [restrictFun_evT, twist_res_val, ← restrictFun_evT q d j W hW g, restrictFun_restrictFun, restrictFun_restrictFun]

theorem evT_change (j j' : Fin (r + 1)) (W : P.Opens) (hWj : W ≤ pullbackChart ι j) (hWj' : W ≤ pullbackChart ι j')
    (g : (twist q ι d).obj W) :
    evT q d j W hWj g = restrictFun hWj (frameUnit ι j j') ^ d * evT q d j' W hWj' g := by
  refine restrictFun_injective_of_ge
    (inf_le_left.trans inf_le_left : (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W) (le_inf (le_inf le_rfl hWj) hWj') ?_
  have eL : restrictFun (inf_le_left.trans inf_le_left : (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W) (evT q d j W hWj g)
      = restrictFun inf_le_left (g.val j) := by
    rw [← restrictFun_evT q d j W hWj g, restrictFun_restrictFun]
  have eR : restrictFun (inf_le_left.trans inf_le_left : (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W) (evT q d j' W hWj' g)
      = restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W ⊓ pullbackChart ι j') (g.val j') := by
    rw [← restrictFun_evT q d j' W hWj' g, restrictFun_restrictFun]
  rw [map_mul, map_pow, eL, eR, restrictFun_restrictFun, g.compat j j']

variable (G : OModulePresheaf q)

def untw (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) :
    G.obj W ⊗[Γ(P, W)] (twist q ι d).obj W →ₗ[Γ(P, W)] G.obj W :=
  (TensorProduct.rid Γ(P, W) (G.obj W)).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (evT q d j W hW).toLinearMap

theorem untw_tmul (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (x : G.obj W) (g : (twist q ι d).obj W) :
    untw q d G j W hW (x ⊗ₜ g) = evT q d j W hW g • x := by
  change TensorProduct.rid Γ(P, W) (G.obj W) (TensorProduct.map LinearMap.id (evT q d j W hW).toLinearMap (x ⊗ₜ g)) = _
  rw [TensorProduct.map_tmul, TensorProduct.rid_tmul]
  rfl

theorem untw_surjective (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) :
    Function.Surjective (untw q d G j W hW) := fun x =>
  ⟨x ⊗ₜ (evT q d j W hW).symm 1, by rw [untw_tmul, LinearEquiv.apply_symm_apply, one_smul]⟩

theorem res_untw (j : Fin (r + 1)) {W W' : P.Opens} (h : W' ≤ W) (hW : W ≤ pullbackChart ι j)
    (t : G.obj W ⊗[Γ(P, W)] (twist q ι d).obj W) :
    G.res h (untw q d G j W hW t) = untw q d G j W' (h.trans hW) ((G.tensor (twist q ι d)).res h t) := by
  change G.res h (untw q d G j W hW t) = untw q d G j W' (h.trans hW) (G.tensorResₛₗ (twist q ι d) h t)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x g => rw [tensorResₛₗ_tmul, untw_tmul, untw_tmul, G.res_smul, ← evT_res]
  | add s t hs ht => rw [map_add, map_add, map_add, map_add, hs, ht]

theorem untw_change (j j' : Fin (r + 1)) (W : P.Opens) (hWj : W ≤ pullbackChart ι j) (hWj' : W ≤ pullbackChart ι j')
    (t : G.obj W ⊗[Γ(P, W)] (twist q ι d).obj W) :
    untw q d G j W hWj t = restrictFun hWj (frameUnit ι j j') ^ d • untw q d G j' W hWj' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul x g => rw [untw_tmul, untw_tmul, evT_change q d j j' W hWj hWj', mul_smul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

theorem app_untw {G' : OModulePresheaf q} (ψ : AffHom G G') (j : Fin (r + 1)) (W : P.affineOpens)
    (hW : W.1 ≤ pullbackChart ι j) (t : G.obj W.1 ⊗[Γ(P, W.1)] (twist q ι d).obj W.1) :
    ψ.app W (untw q d G j W.1 hW t)
      = untw q d G' j W.1 hW ((AffHom.tensorMap ψ (AffHom.id (twist q ι d))).app W t) := by
  change ψ.app W (untw q d G j W.1 hW t)
    = untw q d G' j W.1 hW (TensorProduct.map (ψ.appSections W) ((AffHom.id (twist q ι d)).appSections W) t)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x g =>
    rw [TensorProduct.map_tmul, untw_tmul, untw_tmul, ψ.app_smul, AffHom.appSections_apply, AffHom.appSections_apply,
      AffHom.id_app]
  | add s t hs ht => rw [map_add, map_add, map_add, map_add, hs, ht]

end Untwisting

section Theta

variable {ι}
variable [IsAffineHom ι]

def ch (s : (stdCoverPullback ι).Idx 0) : Fin (r + 1) := (s.1 0).down

theorem inter_le_ch (s : (stdCoverPullback ι).Idx 0) : (stdCoverPullback ι).inter s ≤ pullbackChart ι (ch s) :=
  (stdCoverPullback ι).inter_le s 0

variable (G : OModulePresheaf q)

def sk (τ : (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    (W : P.Opens) (hW : W ≤ (stdCoverPullback ι).inter s) : G.obj W :=
  untw q d G (ch s) W (hW.trans (inter_le_ch s)) ((G.tensor (twist q ι d)).res hW (τ s))

theorem sk_def (τ : (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    (W : P.Opens) (hW : W ≤ (stdCoverPullback ι).inter s) :
    sk q d G τ s W hW = untw q d G (ch s) W (hW.trans (inter_le_ch s)) ((G.tensor (twist q ι d)).res hW (τ s)) := rfl

theorem res_sk (τ : (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    {W W' : P.Opens} (h : W' ≤ W) (hW : W ≤ (stdCoverPullback ι).inter s) :
    G.res h (sk q d G τ s W hW) = sk q d G τ s W' (h.trans hW) := by
  rw [sk_def, sk_def, res_untw, (G.tensor (twist q ι d)).res_res]

def θloc (τ : Fin m → (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    (W : P.Opens) (hW : W ≤ (stdCoverPullback ι).inter s) : (E ι q d m).obj W →ₗ[Γ(P, W)] G.obj W :=
  Fintype.linearCombination Γ(P, W) (fun l => sk q d G (τ l) s W hW) ∘ₗ evE (ch s) W (hW.trans (inter_le_ch s))

theorem θloc_apply (τ : Fin m → (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    (W : P.Opens) (hW : W ≤ (stdCoverPullback ι).inter s) (e : (E ι q d m).obj W) :
    θloc q d m G τ s W hW e = ∑ l, evE (ch s) W (hW.trans (inter_le_ch s)) e l • sk q d G (τ l) s W hW := rfl

theorem res_θloc (τ : Fin m → (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    {W W' : P.Opens} (h : W' ≤ W) (hW : W ≤ (stdCoverPullback ι).inter s) (e : (E ι q d m).obj W) :
    G.res h (θloc q d m G τ s W hW e) = θloc q d m G τ s W' (h.trans hW) ((E ι q d m).res h e) := by
  rw [θloc_apply, θloc_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [G.res_smul, res_sk, evE_res]

def homFam (τ : Fin m → (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0) :
    (internalHom (E ι q d m) G).obj ((stdCoverPullback ι).inter s) :=
  ⟨fun W => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1
      haveI : IsScalarTower A Γ(P, W.1.1) ((E ι q d m).obj W.1.1) := (E ι q d m).isScalarTower W.1.1
      haveI : IsScalarTower A Γ(P, W.1.1) (G.obj W.1.1) := G.isScalarTower W.1.1
      exact (θloc q d m G τ s W.1.1 W.2).restrictScalars A,
    ⟨fun W a x => (θloc q d m G τ s W.1.1 W.2).map_smul a x, fun W W' h x => (res_θloc q d m G τ s h W'.2 x).symm⟩⟩

theorem homFam_apply (τ : Fin m → (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0)
    (s : (stdCoverPullback ι).Idx 0) (W : AffBelow ((stdCoverPullback ι).inter s)) (x : (E ι q d m).obj W.1.1) :
    (homFam q d m G τ s).1 W x = θloc q d m G τ s W.1.1 W.2 x := rfl

theorem res_face_eq (τ : ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) (s : (stdCoverPullback ι).Idx 1)
    {W : P.Opens} (hW : W ≤ (stdCoverPullback ι).inter s) :
    (G.tensor (twist q ι d)).res (hW.trans ((stdCoverPullback ι).inter_le_inter_face s 0))
        (τ.1 ((stdCoverPullback ι).face s 0))
      = (G.tensor (twist q ι d)).res (hW.trans ((stdCoverPullback ι).inter_le_inter_face s 1))
        (τ.1 ((stdCoverPullback ι).face s 1)) := by
  have h := congrFun (LinearMap.mem_ker.mp τ.2) s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Pi.zero_apply] at h
  rw [add_neg_eq_zero] at h
  rw [← (G.tensor (twist q ι d)).res_res hW ((stdCoverPullback ι).inter_le_inter_face s 0),
    ← (G.tensor (twist q ι d)).res_res hW ((stdCoverPullback ι).inter_le_inter_face s 1), h]

theorem d_homFam (τ : Fin m → ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) :
    (internalHom (E ι q d m) G).d (stdCoverPullback ι) 0 (fun s => homFam q d m G (fun l => (τ l).1) s) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.zero_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  rw [add_neg_eq_zero]
  refine Subtype.ext (funext fun W => LinearMap.ext fun x => ?_)
  change θloc q d m G (fun l => (τ l).1) ((stdCoverPullback ι).face s 0) W.1.1
      (W.2.trans ((stdCoverPullback ι).inter_le_inter_face s 0)) x
    = θloc q d m G (fun l => (τ l).1) ((stdCoverPullback ι).face s 1) W.1.1
      (W.2.trans ((stdCoverPullback ι).inter_le_inter_face s 1)) x
  rw [θloc_apply, θloc_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h0 : W.1.1 ≤ pullbackChart ι (ch ((stdCoverPullback ι).face s 0)) :=
    (W.2.trans ((stdCoverPullback ι).inter_le_inter_face s 0)).trans (inter_le_ch _)
  have h1 : W.1.1 ≤ pullbackChart ι (ch ((stdCoverPullback ι).face s 1)) :=
    (W.2.trans ((stdCoverPullback ι).inter_le_inter_face s 1)).trans (inter_le_ch _)
  rw [sk_def, sk_def, res_face_eq q d G (τ l) s W.2,
    untw_change q d G (ch ((stdCoverPullback ι).face s 0)) (ch ((stdCoverPullback ι).face s 1)) W.1.1 h0 h1,
    evE_change (ch ((stdCoverPullback ι).face s 0)) (ch ((stdCoverPullback ι).face s 1)) W.1.1 h0 h1, smul_smul,
    mul_comm]

variable {G} (hGq : G.IsQuasicoherent)

include hGq in

theorem existsUnique_hom (τ : Fin m → ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) :
    ∃! Φ : (internalHom (E ι q d m) G).obj ⊤,
      ∀ s, homFam q d m G (fun l => (τ l).1) s = (internalHom (E ι q d m) G).res le_top Φ :=
  (internalHom_d_zero_eq_zero_iff_existsUnique hGq (stdCoverPullback ι) _).mp (d_homFam q d m G τ)

def Θ (τ : Fin m → ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) : AffHom (E ι q d m) G :=
  internalHom.toAffHom _ _ (existsUnique_hom q d m hGq τ).exists.choose

theorem Θ_spec (τ : Fin m → ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) (s : (stdCoverPullback ι).Idx 0) :
    homFam q d m G (fun l => (τ l).1) s
      = (internalHom (E ι q d m) G).res le_top (existsUnique_hom q d m hGq τ).exists.choose :=
  (existsUnique_hom q d m hGq τ).exists.choose_spec s

theorem Θ_app (τ : Fin m → ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) (s : (stdCoverPullback ι).Idx 0)
    (W : P.affineOpens) (hW : W.1 ≤ (stdCoverPullback ι).inter s) (x : (E ι q d m).obj W.1) :
    (Θ q d m hGq τ).app W x = θloc q d m G (fun l => (τ l).1) s W.1 hW x := by
  have h := congrArg (fun ψ : (internalHom (E ι q d m) G).obj ((stdCoverPullback ι).inter s) => ψ.1 ⟨W, hW⟩ x)
    (Θ_spec q d m hGq τ s)
  exact h.symm

theorem Θ_unique (τ : Fin m → ↥((G.tensor (twist q ι d)).H0 (stdCoverPullback ι))) (Ψ : AffHom (E ι q d m) G)
    (hΨ : ∀ (s : (stdCoverPullback ι).Idx 0) (W : AffBelow ((stdCoverPullback ι).inter s)) (x : (E ι q d m).obj W.1.1),
      Ψ.app W.1 x = θloc q d m G (fun l => (τ l).1) s W.1.1 W.2 x) :
    Ψ = Θ q d m hGq τ := by
  have h1 : ∀ s, homFam q d m G (fun l => (τ l).1) s
      = (internalHom (E ι q d m) G).res le_top (internalHom.ofAffHom _ _ Ψ) :=
    fun s => Subtype.ext (funext fun W => LinearMap.ext fun x => (hΨ s W x).symm)
  have h2 := (existsUnique_hom q d m hGq τ).unique h1 (Θ_spec q d m hGq τ)
  change internalHom.toAffHom _ _ (internalHom.ofAffHom _ _ Ψ) = internalHom.toAffHom _ _ _
  rw [h2]

theorem app_sk [IsSeparated q] {G' : OModulePresheaf q} (ψ : AffHom G G')
    (τ : (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (τ' : (G'.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0)
    (s : (stdCoverPullback ι).Idx 0)
    (hττ' : (AffHom.tensorMap ψ (AffHom.id (twist q ι d))).app ((stdCoverPullback ι).affineInter q s) (τ s) = τ' s)
    (W : P.affineOpens) (hW : W.1 ≤ (stdCoverPullback ι).inter s) :
    ψ.app W (sk q d G τ s W.1 hW) = sk q d G' τ' s W.1 hW := by
  rw [sk_def, sk_def, app_untw,
    AffHom.naturality_apply (AffHom.tensorMap ψ (AffHom.id (twist q ι d))) (U := W)
      (U' := (stdCoverPullback ι).affineInter q s) hW (τ s), hττ']

end Theta

section Nakayama

variable {ι q d m}
variable (I : Ideal A) (F : ℕ → OModulePresheaf q)
  (φ : ∀ k, AffHom (F (k + 1)) (F k))
  (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
  (hφk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))

include hφs hφk in

theorem pow_smul_top_eq_bot (k : ℕ) (U : P.affineOpens) :
    I ^ (k + 1) • (⊤ : Submodule A ((F k).obj U.1)) = ⊥ := by
  refine (Submodule.smul_le.mpr fun a ha x _ => ?_).antisymm bot_le
  obtain ⟨y, rfl⟩ := hφs k U x
  rw [Submodule.mem_bot, ← LinearMap.map_smul, ← LinearMap.mem_ker, hφk k U]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

include hφs hφk in

theorem span_eq_top_of_span_image_eq_top (k : ℕ) (U : P.affineOpens) {n : ℕ}
    (t' : Fin n → (F (k + 1)).obj U.1) (t : Fin n → (F k).obj U.1)
    (hφt : ∀ a, (φ k).app U (t' a) = t a)
    (hgen : Submodule.span Γ(P, U.1) (Set.range t) = ⊤) :
    Submodule.span Γ(P, U.1) (Set.range t') = ⊤ := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
  haveI : IsScalarTower A Γ(P, U.1) ((F (k + 1)).obj U.1) := (F (k + 1)).isScalarTower U.1
  set Sp : Submodule Γ(P, U.1) ((F (k + 1)).obj U.1) := Submodule.span Γ(P, U.1) (Set.range t') with hSp
  set J : Ideal A := I ^ (k + 1) with hJ
  let SpA : Submodule A ((F (k + 1)).obj U.1) := Sp.restrictScalars A

  have himg : ∀ x : (F (k + 1)).obj U.1, ∃ y ∈ Sp, (φ k).app U x = (φ k).app U y := by
    intro x
    have hx : (φ k).app U x ∈ Submodule.span Γ(P, U.1) (Set.range t) := by rw [hgen]; trivial
    have hmap : Submodule.map ((φ k).appSections U) Sp = Submodule.span Γ(P, U.1) (Set.range t) := by
      rw [hSp, Submodule.map_span]
      congr 1
      ext z
      simp only [Set.mem_image, Set.mem_range, AffHom.appSections_apply]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨a, (hφt a).symm⟩
      · rintro ⟨a, rfl⟩; exact ⟨t' a, ⟨a, rfl⟩, hφt a⟩
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨y, hy, hyx.symm⟩
  have hsup : (⊤ : Submodule A ((F (k + 1)).obj U.1)) = SpA ⊔ J • ⊤ := by
    refine le_antisymm (fun x _ => ?_) le_top
    obtain ⟨y, hy, hxy⟩ := himg x
    have hker : x - y ∈ LinearMap.ker ((φ k).app U) := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [hφk k U] at hker
    have : x = y + (x - y) := by abel
    rw [this]
    exact Submodule.add_mem_sup (show y ∈ SpA from hy) hker

  have hJSp : J • SpA ≤ SpA := by
    refine Submodule.smul_le.mpr fun a _ x hx => ?_
    change a • x ∈ Sp
    rw [← smul_one_smul Γ(P, U.1) a x]
    exact Sp.smul_mem _ hx

  have hJ2 : (J * J) • (⊤ : Submodule A ((F (k + 1)).obj U.1)) = ⊥ := by
    have hle : J * J ≤ I ^ (k + 1 + 1) := by
      rw [hJ, ← pow_add]; exact Ideal.pow_le_pow_right (by omega)
    exact le_bot_iff.mp ((Submodule.smul_mono_left hle).trans (pow_smul_top_eq_bot I F φ hφs hφk (k + 1) U).le)
  have hJtop : J • (⊤ : Submodule A ((F (k + 1)).obj U.1)) ≤ SpA := by
    calc J • (⊤ : Submodule A ((F (k + 1)).obj U.1)) = J • (SpA ⊔ J • ⊤) := by rw [← hsup]
      _ = J • SpA ⊔ (J * J) • ⊤ := by rw [Submodule.smul_sup, ← Submodule.mul_smul]
      _ ≤ SpA := by rw [hJ2, sup_bot_eq]; exact hJSp
  have htopA : SpA = ⊤ := by
    rw [eq_top_iff, hsup]; exact sup_le le_rfl hJtop
  rw [eq_top_iff]
  intro x _
  have : x ∈ SpA := by rw [htopA]; trivial
  exact this

end Nakayama

section LocalSurj

variable {ι}
variable [IsAffineHom ι]

theorem span_sk_eq_top [IsSeparated q] (G : OModulePresheaf q) (hGq : G.IsQuasicoherent)
    (τ : Fin m → (G.tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) (s : (stdCoverPullback ι).Idx 0)
    (hgen : Submodule.span Γ(P, (stdCoverPullback ι).inter s) (Set.range fun l => τ l s) = ⊤)
    (U : P.affineOpens) (f : Γ(P, U.1)) (g : Γ(P, (stdCoverPullback ι).inter s))
    (hfg : P.basicOpen f = P.basicOpen g) :
    Submodule.span Γ(P, P.basicOpen f)
      (Set.range fun l => sk q d G (τ l) s (P.basicOpen f) (hfg.le.trans (P.basicOpen_le g))) = ⊤ := by

  let τv : Fin m → G.obj ((stdCoverPullback ι).inter s) ⊗[Γ(P, (stdCoverPullback ι).inter s)]
      (twist q ι d).obj ((stdCoverPullback ι).inter s) := fun l => τ l s
  have hgen' : Submodule.span Γ(P, (stdCoverPullback ι).inter s) (Set.range τv) = ⊤ := hgen
  have hA : Submodule.span Γ(P, (stdCoverPullback ι).inter s)
      (Set.range fun l => sk q d G (τ l) s _ le_rfl) = ⊤ := by
    have hcomp : (fun l => sk q d G (τ l) s _ le_rfl) = untw q d G (ch s) _ (inter_le_ch s) ∘ τv := by
      funext l
      change untw q d G (ch s) _ (inter_le_ch s)
        ((G.tensor (twist q ι d)).res (le_refl ((stdCoverPullback ι).inter s)) (τ l s)) = _
      rw [(G.tensor (twist q ι d)).res_refl_apply]
      rfl
    have := congrArg (Submodule.map (untw q d G (ch s) _ (inter_le_ch s))) hgen'
    rwa [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr (untw_surjective q d G _ _ _),
      ← Set.range_comp, ← hcomp] at this

  have hWs : P.basicOpen f ≤ (stdCoverPullback ι).inter s := hfg.le.trans (P.basicOpen_le g)
  set Sp := Submodule.span Γ(P, P.basicOpen f)
    (Set.range fun l => sk q d G (τ l) s (P.basicOpen f) (hfg.le.trans (P.basicOpen_le g))) with hSp
  have hres : ∀ y : G.obj ((stdCoverPullback ι).inter s), G.res hWs y ∈ Sp := by
    intro y
    have hy : y ∈ Submodule.span Γ(P, (stdCoverPullback ι).inter s)
        (Set.range fun l => sk q d G (τ l) s _ le_rfl) := by rw [hA]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [res_sk]
      exact Submodule.subset_span ⟨l, rfl⟩
    | zero => rw [map_zero]; exact Sp.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact Sp.add_mem hx hy
    | smul c x _ hx => rw [G.res_smul]; exact Sp.smul_mem _ hx
  rw [eq_top_iff]
  rintro x -
  obtain ⟨n, y, hy⟩ := (hGq ((stdCoverPullback ι).affineInter q s) g).1 (G.res hfg.ge x)
  have hy' := congrArg (G.res hfg.le) hy
  rw [G.res_smul, res_res_eq_self] at hy'

  have hu : IsUnit (restrictFun hfg.le (restrictFun (P.basicOpen_le g) g)) :=
    (P.toRingedSpace.isUnit_res_basicOpen g).map _
  obtain ⟨w, hw⟩ := (hu.pow n).exists_left_inv
  have hx : x = w • G.res hWs y := by
    rw [← G.res_res hfg.le (P.basicOpen_le g), hy', map_pow, map_pow, smul_smul, hw, one_smul]
  rw [hx]
  exact Sp.smul_mem w (hres y)

variable [IsSeparated q]
  (I : Ideal A) (F : ℕ → OModulePresheaf q) (hq : ∀ k, (F k).IsQuasicoherent)
  (φ : ∀ k, AffHom (F (k + 1)) (F k))
  (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
  (hφk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
  (σ : ∀ k : ℕ, Fin m → ↥(((F k).tensor (twist q ι d)).H0 (stdCoverPullback ι)))
  (hσ : ∀ (k : ℕ) (l : Fin m),
    (AffHom.tensorMap (φ k) (AffHom.id (twist q ι d))).H0Map (stdCoverPullback ι) (σ (k + 1) l) = σ k l)

include hσ in

theorem σ_step (k : ℕ) (l : Fin m) (s : (stdCoverPullback ι).Idx 0) :
    (AffHom.tensorMap (φ k) (AffHom.id (twist q ι d))).app ((stdCoverPullback ι).affineInter q s) ((σ (k + 1) l).1 s)
      = (σ k l).1 s :=
  congrFun (congrArg Subtype.val (hσ k l)) s

include hσ in

theorem app_sk_succ (k : ℕ) (l : Fin m) (s : (stdCoverPullback ι).Idx 0) (W : P.affineOpens)
    (hW : W.1 ≤ (stdCoverPullback ι).inter s) :
    (φ k).app W (sk q d (F (k + 1)) (σ (k + 1) l).1 s W.1 hW) = sk q d (F k) (σ k l).1 s W.1 hW :=
  app_sk q d (φ k) (σ (k + 1) l).1 (σ k l).1 s (σ_step q d m F φ σ hσ k l s) W hW

include hφs hφk hσ in

theorem span_sk_eq_top_all (s : (stdCoverPullback ι).Idx 0) (W : P.affineOpens) (hW : W.1 ≤ (stdCoverPullback ι).inter s)
    (h0 : Submodule.span Γ(P, W.1) (Set.range fun l => sk q d (F 0) (σ 0 l).1 s W.1 hW) = ⊤) (k : ℕ) :
    Submodule.span Γ(P, W.1) (Set.range fun l => sk q d (F k) (σ k l).1 s W.1 hW) = ⊤ := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    exact span_eq_top_of_span_image_eq_top I F φ hφs hφk k W _ _
      (fun l => app_sk_succ q d m F φ σ hσ k l s W hW) ih

omit [IsSeparated q] in

theorem surjective_local (k : ℕ) (s : (stdCoverPullback ι).Idx 0) (W : P.affineOpens)
    (hW : W.1 ≤ (stdCoverPullback ι).inter s)
    (hspan : Submodule.span Γ(P, W.1) (Set.range fun l => sk q d (F k) (σ k l).1 s W.1 hW) = ⊤) :
    Function.Surjective ((Θ q d m (hq k) (σ k)).app W) := by
  intro y
  have hy : y ∈ Submodule.span Γ(P, W.1) (Set.range fun l => sk q d (F k) (σ k l).1 s W.1 hW) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(P, W.1)).mp hy
  refine ⟨liftE q d m (ch s) W.1 (hW.trans (inter_le_ch s)) c, ?_⟩
  rw [Θ_app q d m (hq k) (σ k) s W hW, θloc_apply, evE_liftE]
  exact hc

end LocalSurj

section LocalToGlobal

variable {ι q d m}

theorem surjective_of_forall_basicOpen {E' G : OModulePresheaf q} (hEq : E'.IsQuasicoherent) (hGq : G.IsQuasicoherent)
    (Ψ : AffHom E' G) (U : P.affineOpens) (S : Set Γ(P, U.1)) (hS : Ideal.span S = ⊤)
    (hloc : ∀ f ∈ S, Function.Surjective (Ψ.app ⟨P.basicOpen f, U.2.basicOpen f⟩)) :
    Function.Surjective (Ψ.app U) := by
  intro y

  let J : Ideal Γ(P, U.1) :=
    (LinearMap.range (Ψ.appSections U)).comap (LinearMap.toSpanSingleton Γ(P, U.1) (G.obj U.1) y)
  have hJ : ∀ f ∈ S, f ∈ J.radical := by
    intro f hf
    obtain ⟨e₀, he₀⟩ := hloc f hf (G.res (P.basicOpen_le f) y)
    obtain ⟨n, e₁, he₁⟩ := (hEq U f).1 e₀
    have hz : G.res (P.basicOpen_le f) (Ψ.app U e₁ - f ^ n • y) = 0 := by
      rw [map_sub, ← Ψ.naturality_apply (U := ⟨P.basicOpen f, U.2.basicOpen f⟩) (U' := U) (P.basicOpen_le f) e₁,
        he₁, Ψ.app_smul, he₀, G.res_smul, sub_self]
    obtain ⟨N, hN⟩ := (hGq U f).2 _ hz
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hN
    refine ⟨N + n, Submodule.mem_comap.mpr ⟨f ^ N • e₁, ?_⟩⟩
    rw [AffHom.appSections_apply, Ψ.app_smul, hN]
    rfl
  have hJtop : J = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hS, Ideal.span_le]
    exact hJ
  have h1 : (1 : Γ(P, U.1)) ∈ J := by rw [hJtop]; trivial
  obtain ⟨e, he⟩ := (Submodule.mem_comap.mp h1 : _ ∈ LinearMap.range (Ψ.appSections U))
  refine ⟨e, ?_⟩
  rw [← one_smul Γ(P, U.1) y]
  exact he

end LocalToGlobal

section Main

variable [IsClosedImmersion ι] [IsSeparated q]
  (I : Ideal A) (F : ℕ → OModulePresheaf q) (hq : ∀ k, (F k).IsQuasicoherent)
  (φ : ∀ k, AffHom (F (k + 1)) (F k))
  (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
  (hφk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
  (σ : ∀ k : ℕ, Fin m → ↥(((F k).tensor (twist q ι d)).H0 (stdCoverPullback ι)))
  (hσ : ∀ (k : ℕ) (l : Fin m),
    (AffHom.tensorMap (φ k) (AffHom.id (twist q ι d))).H0Map (stdCoverPullback ι) (σ (k + 1) l) = σ k l)
  (hgen : ∀ s : (stdCoverPullback ι).Idx 0,
    Submodule.span Γ(P, (stdCoverPullback ι).inter s)
      (Set.range fun l : Fin m => (σ 0 l : ((F 0).tensor (twist q ι d)).cochain (stdCoverPullback ι) 0) s) = ⊤)

def biBasic (U : P.affineOpens) : Set Γ(P, U.1) :=
  {f | ∃ (s : (stdCoverPullback ι).Idx 0) (g : Γ(P, (stdCoverPullback ι).inter s)), P.basicOpen f = P.basicOpen g}

def vtx (j : (stdCoverPullback ι).ι) : (stdCoverPullback ι).Idx 0 :=
  ⟨fun _ => j, fun a b hab => absurd (Fin.lt_def.mp hab) (by have := a.2; have := b.2; omega)⟩

theorem U_le_inter_vtx (j : (stdCoverPullback ι).ι) :
    (stdCoverPullback ι).U j ≤ (stdCoverPullback ι).inter (vtx ι j) :=
  le_iInf fun _ => le_rfl

include q in

theorem span_biBasic (U : P.affineOpens) : Ideal.span (biBasic ι U) = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff]
  intro x hx
  have hcov : (⨆ j : ULift.{u} (Fin (r + 1)), (ProjSpace.stdCoverPullback ι).U j) = ⊤ :=
    (ProjSpace.stdCoverPullback ι).iSup_eq_top
  have hx' : x ∈ (⨆ j : ULift.{u} (Fin (r + 1)), (ProjSpace.stdCoverPullback ι).U j) := by
    rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter U.2 ((stdCoverPullback ι).isAffineOpen_inter q (vtx ι j)) x
      ⟨hx, U_le_inter_vtx ι j hj⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, ⟨vtx ι j, g, hfg⟩⟩, hxf⟩

include hφs hφk hσ hgen in
theorem surjective_Θ (k : ℕ) (U : P.affineOpens) : Function.Surjective ((Θ q d m (hq k) (σ k)).app U) := by
  refine surjective_of_forall_basicOpen (isQuasicoherent_E ι q d m) (hq k) _ U (biBasic ι U) (span_biBasic ι q U)
    fun f hf => ?_
  obtain ⟨s, g, hfg⟩ := hf
  have hW : P.basicOpen f ≤ (stdCoverPullback ι).inter s := hfg.le.trans (P.basicOpen_le g)
  exact surjective_local q d m F hq σ k s ⟨P.basicOpen f, U.2.basicOpen f⟩ hW
    (span_sk_eq_top_all q d m I F φ hφs hφk σ hσ s ⟨P.basicOpen f, U.2.basicOpen f⟩ hW
      (span_sk_eq_top q d m (F 0) (hq 0) (fun l => (σ 0 l).1) s (hgen s) U f g hfg) k)

include hσ in
theorem comp_Θ (k : ℕ) :
    (φ k).comp (Θ q d m (hq (k + 1)) (σ (k + 1))) = Θ q d m (hq k) (σ k) := by
  refine Θ_unique q d m (hq k) (σ k) _ fun s W x => ?_
  rw [AffHom.comp_app, Θ_app q d m (hq (k + 1)) (σ (k + 1)) s W.1 W.2, θloc_apply, θloc_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(φ k).app_smul, app_sk_succ q d m F φ σ hσ k l s W.1 W.2]

include hq hφs hφk hσ hgen in
theorem main (hc : ∀ k, (F k).IsCoherent) :
    ∃ (E : OModulePresheaf q) (θ : ∀ k, OModulePresheaf.AffHom E (F k)),
      E.IsCoherent ∧ E.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U) := by
  have _ := hc
  refine ⟨E ι q d m, fun k => Θ q d m (hq k) (σ k), isCoherent_E ι q d m, isQuasicoherent_E ι q d m,
    fun k U => surjective_Θ ι q d m I F hq φ hφs hφk σ hσ hgen k U, fun k U => ?_⟩
  exact congrArg (fun χ : AffHom (E ι q d m) (F k) => χ.app U) (comp_Θ ι q d m F hq φ σ hσ k)

end Main

end P2mUntwist
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.P2mUntwist"

open AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) [IsSeparated q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (d m : ℕ)
    (σ : ∀ k : ℕ, Fin m → ↥(((F k).tensor (ProjSpace.twist q ι d)).H0 (ProjSpace.stdCoverPullback ι)))
    (hσ : ∀ (k : ℕ) (l : Fin m),
      (OModulePresheaf.AffHom.tensorMap (φ k) (OModulePresheaf.AffHom.id (ProjSpace.twist q ι d))).H0Map
        (ProjSpace.stdCoverPullback ι) (σ (k + 1) l) = σ k l)
    (hgen : ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0,
      Submodule.span Γ(P, (ProjSpace.stdCoverPullback ι).inter s)
          (Set.range fun l : Fin m =>
            (σ 0 l : ((F 0).tensor (ProjSpace.twist q ι d)).cochain (ProjSpace.stdCoverPullback ι) 0) s) = ⊤) :
    ∃ (E : OModulePresheaf q) (θ : ∀ k, OModulePresheaf.AffHom E (F k)),
      E.IsCoherent ∧ E.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U) := by
  have _ := hιq
  exact P2mUntwist.main ι q d m I F hq φ hφs hφk σ hσ hgen hc

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top (solution)
