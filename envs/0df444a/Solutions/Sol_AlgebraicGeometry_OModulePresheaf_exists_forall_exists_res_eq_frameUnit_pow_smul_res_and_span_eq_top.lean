-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/837e5597-3ae5-5cf5-8975-7da77c376032

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mSerreAFrames

open AlgebraicGeometry.ProjSpace HomogeneousLocalization

section Geometry

variable (A : Type u) [CommRing A] (N : ℕ)

theorem proj_basicOpen_awayToSection_ratio (j i : Fin (N + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).basicOpen
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X j)).hom
          (ProjSpace.ratio A N j i))
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
          ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) * MvPolynomial.X i) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A with h𝒜
  set z : Away 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) := ProjSpace.ratio A N j i with hz
  have hkey : ∀ (x : Proj 𝒜) (hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)),
      IsUnit ((Proj 𝒜).presheaf.germ _ x hxj ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom z))
        ↔ (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) A) ∉ x.asHomogeneousIdeal := by
    intro x hxj
    have hxj' : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)
        ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxj
    have hgerm := congrArg (fun ψ => CommRingCat.Hom.hom ψ z)
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) x hxj)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    erw [hgerm]
    haveI : IsLocalHom (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom := isLocalHom_of_isIso _
    refine (isUnit_map_iff (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom _).trans ?_
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hval : (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj') z).val
        = Localization.mk (MvPolynomial.X i)
            ⟨(MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ 1, pow_mem hxj' 1⟩ := by
      simp only [hz, ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
      rfl
    rw [show Submonoid.powers_le.mpr hxj = Submonoid.powers_le.mpr hxj' from rfl, hval,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact Iff.rfl
  ext x
  simp only [SetLike.mem_coe, Proj.basicOpen_mul, Proj.mem_basicOpen, Opens.mem_inf]
  refine ⟨fun hx => ?_, fun ⟨hxj, hxi⟩ => ?_⟩
  · have hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) :=
      Scheme.basicOpen_le _ _ hx
    exact ⟨hxj, (hkey x hxj).mp ((Scheme.mem_basicOpen _ _ x hxj).mp hx)⟩
  · exact (Scheme.mem_basicOpen _ _ x hxj).mpr ((hkey x hxj).mpr hxi)

variable {A N} {X : Scheme.{u}} (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

theorem basicOpen_frameUnit (j i : Fin (N + 1)) : X.basicOpen (frameUnit φ j i) = pullbackOverlap φ j i := by
  have h := Scheme.preimage_basicOpen φ
    ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X j)).hom
      (ProjSpace.ratio A N j i))
  rw [proj_basicOpen_awayToSection_ratio] at h
  exact h.symm

end Geometry

section Sections

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)}
  {π : X ⟶ Spec (CommRingCat.of A)} {F : OModulePresheaf π}

variable (F) in
theorem res_smul' {U U' : X.Opens} (h : U ≤ U') (a : Γ(X, U')) (x : F.obj U') :
    F.res h (a • x) = restrictFun h a • F.res h x :=
  F.res_smul h a x

variable (F) in
theorem res_pow_smul {U U' : X.Opens} (h : U ≤ U') (a : Γ(X, U')) (k : ℕ) (x : F.obj U') :
    F.res h (a ^ k • x) = restrictFun h a ^ k • F.res h x := by
  rw [res_smul', map_pow]

variable (F) in

theorem res_res_eq_self {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W) (x : F.obj W) :
    F.res h (F.res h' x) = x := by
  rw [F.res_res]; exact F.res_refl_apply W x

variable (F) in
theorem res_injective_of_ge {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W) : Function.Injective (F.res h) :=
  fun x y hxy => by rw [← res_res_eq_self F h' h x, ← res_res_eq_self F h' h y, hxy]

variable [IsAffineHom φ]

variable (φ) in

abbrev Uaff (i : Fin (N + 1)) : X.affineOpens := ⟨pullbackChart φ i, isAffineOpen_pullbackChart φ i⟩

variable (φ) in

abbrev Oaff (j i : Fin (N + 1)) : X.affineOpens := ⟨pullbackOverlap φ j i, isAffineOpen_pullbackOverlap φ j i⟩

theorem exists_numer (hq : F.IsQuasicoherent) (j i : Fin (N + 1)) (x : F.obj (pullbackOverlap φ j i)) :
    ∃ (n : ℕ) (y : F.obj (pullbackChart φ j)),
      F.res (pullbackOverlap_le_left φ j i) y =
        restrictFun (pullbackOverlap_le_left φ j i) (frameUnit φ j i) ^ n • x := by
  have e := basicOpen_frameUnit φ j i
  obtain ⟨n, y, hy⟩ := (hq (Uaff φ j) (frameUnit φ j i)).1 (F.res e.le x)
  refine ⟨n, y, ?_⟩
  have h2 := congrArg (F.res e.ge) hy
  rw [F.res_res, res_smul', res_res_eq_self F e.ge e.le x, restrictFun_restrictFun, map_pow] at h2
  exact h2

theorem exists_torsion (hq : F.IsQuasicoherent) (j i : Fin (N + 1)) (y : F.obj (pullbackChart φ j))
    (hy : F.res (pullbackOverlap_le_left φ j i) y = 0) :
    ∃ n : ℕ, frameUnit φ j i ^ n • y = 0 := by
  have e := basicOpen_frameUnit φ j i
  refine (hq (Uaff φ j) (frameUnit φ j i)).2 y ?_
  have : F.res (X.basicOpen_le (frameUnit φ j i)) y = F.res e.le (F.res (pullbackOverlap_le_left φ j i) y) := by
    rw [F.res_res]
  rw [this, hy, map_zero]

omit [IsAffineHom φ] in

theorem inf_le_O (j j' i : Fin (N + 1)) : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackOverlap φ j j' :=
  inf_le_left

theorem exists_torsion_overlap (hq : F.IsQuasicoherent) (j j' i : Fin (N + 1)) (y : F.obj (pullbackOverlap φ j j'))
    (hy : F.res (inf_le_O j j' i : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ _) y = 0) :
    ∃ n : ℕ, restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j i) ^ n • y = 0 := by
  set w : Γ(X, pullbackOverlap φ j j') := restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j i) with hw
  have e : X.basicOpen w = pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i := by
    rw [hw, restrictFun, Scheme.basicOpen_res, basicOpen_frameUnit]
  refine (hq (Oaff φ j j') w).2 y ?_
  have : F.res (X.basicOpen_le w) y = F.res e.le (F.res (inf_le_O j j' i) y) := by rw [F.res_res]
  rw [this, hy, map_zero]

end Sections

section Extend

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} [IsAffineHom φ]
  {π : X ⟶ Spec (CommRingCat.of A)} {F : OModulePresheaf π}

omit [IsAffineHom φ] in

theorem inf_le_O' (j j' i : Fin (N + 1)) :
    pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackOverlap φ j' i := by
  rw [pullbackOverlap_eq_inf, pullbackOverlap_eq_inf, pullbackOverlap_eq_inf]
  exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

omit [IsAffineHom φ] in

theorem cocycle_inf (j j' i : Fin (N + 1)) :
    restrictFun (inf_le_left.trans (pullbackOverlap_le_left φ j j') :
        pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackChart φ j) (frameUnit φ j j')
      * restrictFun ((inf_le_O' j j' i).trans (pullbackOverlap_le_left φ j' i) :
        pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackChart φ j') (frameUnit φ j' i)
      = restrictFun (inf_le_right.trans (pullbackOverlap_le_left φ j i) :
        pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackChart φ j) (frameUnit φ j i) := by
  have key := congrArg (restrictFun (inf_le_left : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackOverlap φ j j'))
    (frameUnit_cocycle φ j j' i)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  exact key

structure ExtData (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    (F : OModulePresheaf π) (i : Fin (N + 1)) (t : F.obj (pullbackChart φ i)) where

  n : ℕ

  e : ℕ

  y : ∀ j : Fin (N + 1), F.obj (pullbackChart φ j)
  hy : ∀ j : Fin (N + 1), F.res (pullbackOverlap_le_left φ j i) (y j) =
    restrictFun (pullbackOverlap_le_left φ j i) (frameUnit φ j i) ^ n • F.res (pullbackOverlap_le_right φ j i) t

  hδ : ∀ j j' : Fin (N + 1),
    restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j i) ^ e •
      (F.res (pullbackOverlap_le_left φ j j') (y j) -
        restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j j') ^ n •
          F.res (pullbackOverlap_le_right φ j j') (y j')) = 0

theorem exists_numer_uniform (hq : F.IsQuasicoherent) (i : Fin (N + 1)) (t : F.obj (pullbackChart φ i)) :
    ∃ (n : ℕ) (y : ∀ j : Fin (N + 1), F.obj (pullbackChart φ j)), ∀ j : Fin (N + 1),
      F.res (pullbackOverlap_le_left φ j i) (y j) =
        restrictFun (pullbackOverlap_le_left φ j i) (frameUnit φ j i) ^ n • F.res (pullbackOverlap_le_right φ j i) t := by
  have hnum := fun j => exists_numer (φ := φ) hq j i (F.res (pullbackOverlap_le_right φ j i) t)
  choose n0 y0 hy0 using hnum
  refine ⟨Finset.univ.sup n0, fun j => frameUnit φ j i ^ (Finset.univ.sup n0 - n0 j) • y0 j, fun j => ?_⟩
  have hn0 : n0 j ≤ Finset.univ.sup n0 := Finset.le_sup (Finset.mem_univ j)
  rw [res_pow_smul, hy0 j, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn0]

theorem exists_extData (hq : F.IsQuasicoherent) (i : Fin (N + 1)) (t : F.obj (pullbackChart φ i)) :
    Nonempty (ExtData φ F i t) := by
  obtain ⟨n, y, hy⟩ := exists_numer_uniform (φ := φ) hq i t

  have hvan : ∀ j j' : Fin (N + 1),
      F.res (inf_le_O j j' i : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ _)
        (F.res (pullbackOverlap_le_left φ j j') (y j) -
          restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j j') ^ n •
            F.res (pullbackOverlap_le_right φ j j') (y j')) = 0 := by
    intro j j'
    have hW1 : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackOverlap φ j i := inf_le_right
    have hW2 : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ pullbackOverlap φ j' i := inf_le_O' j j' i
    have hA : F.res (inf_le_O j j' i : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ _)
        (F.res (pullbackOverlap_le_left φ j j') (y j))
        = restrictFun (hW1.trans (pullbackOverlap_le_left φ j i)) (frameUnit φ j i) ^ n •
            F.res (hW1.trans (pullbackOverlap_le_right φ j i)) t := by
      have e1 : F.res (inf_le_O j j' i : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ _)
          (F.res (pullbackOverlap_le_left φ j j') (y j)) = F.res hW1 (F.res (pullbackOverlap_le_left φ j i) (y j)) := by
        rw [F.res_res, F.res_res]
      rw [e1, hy j, res_pow_smul, restrictFun_restrictFun, F.res_res]
    have hB : F.res (inf_le_O j j' i : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ _)
        (restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j j') ^ n •
            F.res (pullbackOverlap_le_right φ j j') (y j'))
        = (restrictFun ((inf_le_O j j' i).trans (pullbackOverlap_le_left φ j j')) (frameUnit φ j j')
            * restrictFun (hW2.trans (pullbackOverlap_le_left φ j' i)) (frameUnit φ j' i)) ^ n •
            F.res (hW1.trans (pullbackOverlap_le_right φ j i)) t := by
      have e2 : F.res (inf_le_O j j' i : pullbackOverlap φ j j' ⊓ pullbackOverlap φ j i ≤ _)
          (F.res (pullbackOverlap_le_right φ j j') (y j')) = F.res hW2 (F.res (pullbackOverlap_le_left φ j' i) (y j')) := by
        rw [F.res_res, F.res_res]
      rw [res_pow_smul, restrictFun_restrictFun, e2, hy j', res_pow_smul, restrictFun_restrictFun, F.res_res,
        ← mul_smul, ← mul_pow]
    rw [map_sub, hA, hB, cocycle_inf j j' i, sub_self]
  have htor := fun j j' => exists_torsion_overlap (φ := φ) hq j j' i _ (hvan j j')
  choose e0 he0 using htor
  let e : ℕ := Finset.univ.sup fun p : Fin (N + 1) × Fin (N + 1) => e0 p.1 p.2
  have he0' : ∀ j j', e0 j j' ≤ e := fun j j' =>
    Finset.le_sup (f := fun p : Fin (N + 1) × Fin (N + 1) => e0 p.1 p.2) (Finset.mem_univ (j, j'))
  refine ⟨⟨n, e, y, hy, fun j j' => ?_⟩⟩
  rw [← Nat.sub_add_cancel (he0' j j'), pow_add, mul_smul, he0 j j', smul_zero]

variable {i : Fin (N + 1)} {t : F.obj (pullbackChart φ i)}

def ExtData.fam (D : ExtData φ F i t) (q : ℕ) (j : Fin (N + 1)) : F.obj (pullbackChart φ j) :=
  frameUnit φ j i ^ q • D.y j

theorem ExtData.fam_compat (D : ExtData φ F i t) {q : ℕ} (hq : D.e ≤ q) (j j' : Fin (N + 1)) :
    F.res (pullbackOverlap_le_left φ j j') (D.fam q j) =
      restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j j') ^ (D.n + q) •
        F.res (pullbackOverlap_le_right φ j j') (D.fam q j') := by
  simp only [ExtData.fam]
  rw [res_pow_smul, res_pow_smul]

  have hcoc : restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j j') ^ (D.n + q)
      * restrictFun (pullbackOverlap_le_right φ j j') (frameUnit φ j' i) ^ q
      = restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j i) ^ q
        * restrictFun (pullbackOverlap_le_left φ j j') (frameUnit φ j j') ^ D.n := by
    rw [pow_add, mul_assoc, ← mul_pow, frameUnit_cocycle φ j j' i]; ring
  rw [← mul_smul, hcoc, mul_smul, ← sub_eq_zero, ← smul_sub, ← Nat.sub_add_cancel hq, pow_add, mul_smul,
    D.hδ j j', smul_zero]

theorem ExtData.fam_self (D : ExtData φ F i t) (q : ℕ) : D.fam q i = t := by
  simp only [ExtData.fam, frameUnit_self, one_pow, one_smul]
  have h := D.hy i
  rw [frameUnit_self, map_one, one_pow, one_smul] at h
  have hle : pullbackChart φ i ≤ pullbackOverlap φ i i := by rw [pullbackOverlap_eq_inf]; exact le_inf le_rfl le_rfl
  exact res_injective_of_ge F (pullbackOverlap_le_left φ i i) hle h

end Extend

section Main

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
  {π : X ⟶ Spec (CommRingCat.of A)} (F : OModulePresheaf π)

theorem main (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ (m : ℕ) (s : Fin m → ∀ i : Fin (N + 1), F.obj (pullbackChart φ i)),
        (∀ (a : Fin m) (i j : Fin (N + 1)),
          F.res (pullbackOverlap_le_left φ i j) (s a i) =
            restrictFun (pullbackOverlap_le_left φ i j) (frameUnit φ i j) ^ d •
              F.res (pullbackOverlap_le_right φ i j) (s a j)) ∧
        ∀ i : Fin (N + 1), Submodule.span Γ(X, pullbackChart φ i) (Set.range fun a : Fin m => s a i) = ⊤ := by
  classical

  have hfg : ∀ i : Fin (N + 1), ∃ S : Finset (F.obj (pullbackChart φ i)),
      Submodule.span Γ(X, pullbackChart φ i) (S : Set (F.obj (pullbackChart φ i))) = ⊤ := by
    intro i
    haveI : Module.Finite Γ(X, pullbackChart φ i) (F.obj (pullbackChart φ i)) := hc (Uaff φ i)
    exact Module.Finite.fg_top
  choose S hS using hfg

  have hD : ∀ g : Σ i : Fin (N + 1), ↥(S i), Nonempty (ExtData φ F g.1 g.2.1) :=
    fun g => exists_extData hq g.1 g.2.1
  have D : ∀ g : Σ i : Fin (N + 1), ↥(S i), ExtData φ F g.1 g.2.1 := fun g => Classical.choice (hD g)
  let ι := Σ i : Fin (N + 1), ↥(S i)
  haveI : Fintype ι := by
    dsimp only [ι]; infer_instance
  let bound : ι → ℕ := fun g => (D g).n + (D g).e
  refine ⟨Finset.univ.sup bound, fun d hd => ?_⟩
  have hbd : ∀ g : ι, (D g).n + (D g).e ≤ d := fun g => (Finset.le_sup (f := bound) (Finset.mem_univ g)).trans hd
  let m := Fintype.card ι
  let eqv : ι ≃ Fin m := Fintype.equivFin ι

  let s : Fin m → ∀ j : Fin (N + 1), F.obj (pullbackChart φ j) := fun a j => (D (eqv.symm a)).fam (d - (D (eqv.symm a)).n) j
  refine ⟨m, s, fun a j j' => ?_, fun i => ?_⟩
  · have hq' : (D (eqv.symm a)).e ≤ d - (D (eqv.symm a)).n := by have := hbd (eqv.symm a); omega
    have h := (D (eqv.symm a)).fam_compat hq' j j'
    rwa [Nat.add_sub_cancel' (by have := hbd (eqv.symm a); omega : (D (eqv.symm a)).n ≤ d)] at h
  · rw [eq_top_iff, ← hS i]
    refine Submodule.span_le.mpr fun x hx => Submodule.subset_span ?_
    have hx' : x ∈ S i := Finset.mem_coe.mp hx
    refine ⟨eqv ⟨i, ⟨x, hx'⟩⟩, ?_⟩
    show (D (eqv.symm (eqv ⟨i, ⟨x, hx'⟩⟩))).fam (d - (D (eqv.symm (eqv ⟨i, ⟨x, hx'⟩⟩))).n) i = x
    rw [Equiv.symm_apply_apply]
    exact (D ⟨i, ⟨x, hx'⟩⟩).fam_self _

end Main

end P2mSerreAFrames

end

open AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    {π : X ⟶ Spec (CommRingCat.of A)} (F : OModulePresheaf π) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ (m : ℕ) (s : Fin m → ∀ i : Fin (N + 1), F.obj (ProjSpace.pullbackChart φ i)),
        (∀ (a : Fin m) (i j : Fin (N + 1)),
          F.res (ProjSpace.pullbackOverlap_le_left φ i j) (s a i) =
            ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j) ^ d •
              F.res (ProjSpace.pullbackOverlap_le_right φ i j) (s a j)) ∧
        ∀ i : Fin (N + 1),
          Submodule.span Γ(X, ProjSpace.pullbackChart φ i) (Set.range fun a : Fin m => s a i) = ⊤ :=
  P2mSerreAFrames.main φ F hc hq

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top (solution)
