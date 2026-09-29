-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1311fa03-e831-5a8c-9a00-d96601b93889

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mQcExtFrames

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

theorem basicOpen_prod_frameUnit (j : Fin (N + 1)) {i : ℕ} (c : Fin (i + 1) → Fin (N + 1)) (s : Finset (Fin (i + 1))) :
    X.basicOpen (∏ v ∈ s, frameUnit φ j (c v)) = pullbackChart φ j ⊓ ⨅ v ∈ s, pullbackChart φ (c v) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_one]
    refine le_antisymm (le_inf le_rfl (le_iInf fun v => le_iInf fun hv => absurd hv (Finset.notMem_empty v))) inf_le_left
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, basicOpen_frameUnit, pullbackOverlap_eq_inf, Finset.iInf_insert]
    exact (inf_inf_distrib_left _ _ _).symm

theorem basicOpen_prod_frameUnit_univ (j : Fin (N + 1)) {i : ℕ} (c : Fin (i + 1) → Fin (N + 1)) :
    X.basicOpen (∏ v, frameUnit φ j (c v)) = pullbackChart φ j ⊓ ⨅ v, pullbackChart φ (c v) := by
  rw [basicOpen_prod_frameUnit]
  congr 1
  refine le_antisymm (le_iInf fun v => (iInf_le _ v).trans (iInf_le _ (Finset.mem_univ v)))
    (le_iInf fun v => le_iInf fun _ => iInf_le _ v)

end Geometry

section Setup

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  {i : ℕ} (c : Fin (i + 1) → Fin (r + 1))

abbrev W : P.Opens := ⨅ v, pullbackChart ι (c v)

abbrev fU (j : Fin (r + 1)) : Γ(P, pullbackChart ι j) := ∏ v, frameUnit ι j (c v)

theorem UW_le_U (j : Fin (r + 1)) : pullbackChart ι j ⊓ W ι c ≤ pullbackChart ι j := inf_le_left
theorem UW_le_W (j : Fin (r + 1)) : pullbackChart ι j ⊓ W ι c ≤ W ι c := inf_le_right

abbrev OW (j l : Fin (r + 1)) : P.Opens := pullbackOverlap ι j l ⊓ (pullbackChart ι j ⊓ W ι c)

theorem OW_le_O (j l : Fin (r + 1)) : OW ι c j l ≤ pullbackOverlap ι j l := inf_le_left
theorem OW_le_UWj (j l : Fin (r + 1)) : OW ι c j l ≤ pullbackChart ι j ⊓ W ι c := inf_le_right
theorem OW_le_UWl (j l : Fin (r + 1)) : OW ι c j l ≤ pullbackChart ι l ⊓ W ι c :=
  le_inf (inf_le_left.trans (pullbackOverlap_le_right ι j l)) (inf_le_right.trans inf_le_right)
theorem OW_le_Uj (j l : Fin (r + 1)) : OW ι c j l ≤ pullbackChart ι j := inf_le_left.trans (pullbackOverlap_le_left ι j l)
theorem OW_le_Ul (j l : Fin (r + 1)) : OW ι c j l ≤ pullbackChart ι l := inf_le_left.trans (pullbackOverlap_le_right ι j l)
theorem OW_le_W' (j l : Fin (r + 1)) : OW ι c j l ≤ W ι c := inf_le_right.trans inf_le_right

theorem frameUnit_pow_mul_prod (j l : Fin (r + 1)) :
    restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (i + 1)
        * restrictFun (pullbackOverlap_le_right ι j l) (fU ι c l)
      = restrictFun (pullbackOverlap_le_left ι j l) (fU ι c j) := by
  rw [fU, fU, map_prod, map_prod, ← Fin.prod_const (i + 1) (restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l)),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => frameUnit_cocycle ι j l (c v)

theorem frameUnit_pow_mul_prod_res (j l : Fin (r + 1)) {V : P.Opens} (hV : V ≤ pullbackOverlap ι j l) :
    restrictFun (hV.trans (pullbackOverlap_le_left ι j l)) (frameUnit ι j l) ^ (i + 1)
        * restrictFun (hV.trans (pullbackOverlap_le_right ι j l)) (fU ι c l)
      = restrictFun (hV.trans (pullbackOverlap_le_left ι j l)) (fU ι c j) := by
  have key := congrArg (restrictFun hV) (frameUnit_pow_mul_prod ι c j l)
  rw [map_mul, map_pow, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  exact key

theorem frameUnit_mul_res (j l : Fin (r + 1)) {V : P.Opens} (hV : V ≤ pullbackOverlap ι j l) (k : Fin (r + 1)) :
    restrictFun (hV.trans (pullbackOverlap_le_left ι j l)) (frameUnit ι j l)
        * restrictFun (hV.trans (pullbackOverlap_le_right ι j l)) (frameUnit ι l k)
      = restrictFun (hV.trans (pullbackOverlap_le_left ι j l)) (frameUnit ι j k) := by
  have key := congrArg (restrictFun hV) (frameUnit_cocycle ι j l k)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  exact key

end Setup

section Sections

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)}
  {q : P ⟶ Spec (CommRingCat.of A)} {G : OModulePresheaf q}
  {i : ℕ} {c : Fin (i + 1) → Fin (r + 1)}

variable (G) in
theorem res_smul' {U U' : P.Opens} (h : U ≤ U') (a : Γ(P, U')) (x : G.obj U') :
    G.res h (a • x) = restrictFun h a • G.res h x :=
  G.res_smul h a x

variable (G) in
theorem res_res_eq_self {V V' : P.Opens} (h : V ≤ V') (h' : V' ≤ V) (x : G.obj V) : G.res h (G.res h' x) = x := by
  rw [G.res_res]; exact G.res_refl_apply V x

variable [IsAffineHom ι]

variable (ι) in

abbrev Uaff (j : Fin (r + 1)) : P.affineOpens := ⟨pullbackChart ι j, isAffineOpen_pullbackChart ι j⟩

variable (ι) in

abbrev Oaff (j l : Fin (r + 1)) : P.affineOpens := ⟨pullbackOverlap ι j l, isAffineOpen_pullbackOverlap ι j l⟩

variable (c) in

theorem exists_numer (hq : G.IsQuasicoherent) (j : Fin (r + 1)) (x : G.obj (pullbackChart ι j ⊓ W ι c)) :
    ∃ (n : ℕ) (y : G.obj (pullbackChart ι j)),
      G.res (UW_le_U ι c j) y = restrictFun (UW_le_U ι c j) (fU ι c j) ^ n • x := by
  have e := basicOpen_prod_frameUnit_univ ι j c
  obtain ⟨n, y, hy⟩ := (hq (Uaff ι j) (fU ι c j)).1 (G.res e.le x)
  refine ⟨n, y, ?_⟩
  have h2 := congrArg (G.res e.ge) hy
  rw [G.res_res, res_smul', res_res_eq_self G e.ge e.le x, restrictFun_restrictFun, map_pow] at h2
  exact h2

variable (c) in

theorem exists_torsion (hq : G.IsQuasicoherent) (j l : Fin (r + 1)) (y : G.obj (pullbackOverlap ι j l))
    (hy : G.res (OW_le_O ι c j l) y = 0) :
    ∃ e : ℕ, restrictFun (pullbackOverlap_le_left ι j l) (fU ι c j) ^ e • y = 0 := by
  set w : Γ(P, pullbackOverlap ι j l) := restrictFun (pullbackOverlap_le_left ι j l) (fU ι c j) with hw
  have e : P.basicOpen w = OW ι c j l := by
    rw [hw, restrictFun, Scheme.basicOpen_res, basicOpen_prod_frameUnit_univ]
  refine (hq (Oaff ι j l) w).2 y ?_
  have : G.res (P.basicOpen_le w) y = G.res e.le (G.res (OW_le_O ι c j l) y) := by rw [G.res_res]
  rw [this, hy, map_zero]

end Sections

section Extend

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : OModulePresheaf q}
  {i : ℕ} {c : Fin (i + 1) → Fin (r + 1)} {d : ℕ} {t : G.obj (⨅ v, pullbackChart ι (c v))}

abbrev τ (c : Fin (i + 1) → Fin (r + 1)) (d : ℕ) (t : G.obj (⨅ v, pullbackChart ι (c v))) (j : Fin (r + 1)) :
    G.obj (pullbackChart ι j ⊓ W ι c) :=
  restrictFun (UW_le_U ι c j) (frameUnit ι j (c 0)) ^ d • G.res (UW_le_W ι c j) t

variable (ι G c d t) in

structure ExtData where

  n : ℕ

  e : ℕ

  y : ∀ j : Fin (r + 1), G.obj (pullbackChart ι j)
  hy : ∀ j : Fin (r + 1), G.res (UW_le_U ι c j) (y j) = restrictFun (UW_le_U ι c j) (fU ι c j) ^ n • τ c d t j
  hδ : ∀ j l : Fin (r + 1),
    restrictFun (pullbackOverlap_le_left ι j l) (fU ι c j) ^ e •
      (G.res (pullbackOverlap_le_left ι j l) (y j) -
        restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (d + n * (i + 1)) •
          G.res (pullbackOverlap_le_right ι j l) (y l)) = 0

omit [IsAffineHom ι] in
theorem res_pow_smul {U U' : P.Opens} (h : U ≤ U') (a : Γ(P, U')) (k : ℕ) (x : G.obj U') :
    G.res h (a ^ k • x) = restrictFun h a ^ k • G.res h x := by
  rw [res_smul', map_pow]

theorem exists_numer_uniform (hq : G.IsQuasicoherent) :
    ∃ (n : ℕ) (y : ∀ j : Fin (r + 1), G.obj (pullbackChart ι j)), ∀ j : Fin (r + 1),
      G.res (UW_le_U ι c j) (y j) = restrictFun (UW_le_U ι c j) (fU ι c j) ^ n • τ c d t j := by
  choose n0 y0 hy0 using fun j => exists_numer c hq j (τ c d t j)
  refine ⟨Finset.univ.sup n0, fun j => fU ι c j ^ (Finset.univ.sup n0 - n0 j) • y0 j, fun j => ?_⟩
  have hn0 : n0 j ≤ Finset.univ.sup n0 := Finset.le_sup (Finset.mem_univ j)
  rw [res_pow_smul, hy0 j, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn0]

omit [IsAffineHom ι] in

theorem discrepancy_vanishes {n : ℕ} {y : ∀ j : Fin (r + 1), G.obj (pullbackChart ι j)}
    (hy : ∀ j : Fin (r + 1), G.res (UW_le_U ι c j) (y j) = restrictFun (UW_le_U ι c j) (fU ι c j) ^ n • τ c d t j)
    (j l : Fin (r + 1)) :
    G.res (OW_le_O ι c j l)
      (G.res (pullbackOverlap_le_left ι j l) (y j) -
        restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (d + n * (i + 1)) •
          G.res (pullbackOverlap_le_right ι j l) (y l)) = 0 := by

  have hA : G.res (OW_le_O ι c j l) (G.res (pullbackOverlap_le_left ι j l) (y j))
      = (restrictFun (OW_le_Uj ι c j l) (fU ι c j) ^ n * restrictFun (OW_le_Uj ι c j l) (frameUnit ι j (c 0)) ^ d) •
          G.res (OW_le_W' ι c j l) t := by
    have e1 : G.res (OW_le_O ι c j l) (G.res (pullbackOverlap_le_left ι j l) (y j))
        = G.res (OW_le_UWj ι c j l) (G.res (UW_le_U ι c j) (y j)) := by rw [G.res_res, G.res_res]
    rw [e1, hy j, res_pow_smul, res_pow_smul, restrictFun_restrictFun, restrictFun_restrictFun, G.res_res, smul_smul]
  have hB : G.res (OW_le_O ι c j l) (restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (d + n * (i + 1)) •
        G.res (pullbackOverlap_le_right ι j l) (y l))
      = (restrictFun (OW_le_Uj ι c j l) (frameUnit ι j l) ^ (d + n * (i + 1)) *
          (restrictFun (OW_le_Ul ι c j l) (fU ι c l) ^ n * restrictFun (OW_le_Ul ι c j l) (frameUnit ι l (c 0)) ^ d)) •
          G.res (OW_le_W' ι c j l) t := by
    have e1 : G.res (OW_le_O ι c j l) (G.res (pullbackOverlap_le_right ι j l) (y l))
        = G.res (OW_le_UWl ι c j l) (G.res (UW_le_U ι c l) (y l)) := by rw [G.res_res, G.res_res]
    rw [res_pow_smul, restrictFun_restrictFun, e1, hy l, res_pow_smul, res_pow_smul, restrictFun_restrictFun,
      restrictFun_restrictFun, G.res_res, smul_smul, smul_smul, mul_assoc]
  rw [map_sub, hA, hB, ← sub_smul]

  have h1 := frameUnit_pow_mul_prod_res ι c j l (OW_le_O ι c j l)
  have h2 := frameUnit_mul_res ι j l (OW_le_O ι c j l) (c 0)
  have hcoef : restrictFun (OW_le_Uj ι c j l) (frameUnit ι j l) ^ (d + n * (i + 1)) *
        (restrictFun (OW_le_Ul ι c j l) (fU ι c l) ^ n * restrictFun (OW_le_Ul ι c j l) (frameUnit ι l (c 0)) ^ d)
      = restrictFun (OW_le_Uj ι c j l) (fU ι c j) ^ n * restrictFun (OW_le_Uj ι c j l) (frameUnit ι j (c 0)) ^ d := by
    rw [show restrictFun (OW_le_Uj ι c j l) (fU ι c j) = _ from h1.symm,
      show restrictFun (OW_le_Uj ι c j l) (frameUnit ι j (c 0)) = _ from h2.symm]
    show _ = (restrictFun (OW_le_Uj ι c j l) (frameUnit ι j l) ^ (i + 1) * restrictFun (OW_le_Ul ι c j l) (fU ι c l)) ^ n *
      (restrictFun (OW_le_Uj ι c j l) (frameUnit ι j l) * restrictFun (OW_le_Ul ι c j l) (frameUnit ι l (c 0))) ^ d
    ring
  rw [hcoef, sub_self, zero_smul]

theorem exists_extData (hq : G.IsQuasicoherent) : Nonempty (ExtData ι G c d t) := by
  obtain ⟨n, y, hy⟩ := exists_numer_uniform (c := c) (d := d) (t := t) hq
  choose e0 he0 using fun j l => exists_torsion c hq j l _ (discrepancy_vanishes hy j l)
  let e : ℕ := Finset.univ.sup fun p : Fin (r + 1) × Fin (r + 1) => e0 p.1 p.2
  have hle : ∀ j l, e0 j l ≤ e := fun j l =>
    Finset.le_sup (f := fun p : Fin (r + 1) × Fin (r + 1) => e0 p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨⟨n, e, y, hy, fun j l => ?_⟩⟩
  rw [← Nat.sub_add_cancel (hle j l), pow_add, mul_smul, he0 j l, smul_zero]

def ExtData.t' (E : ExtData ι G c d t) (j : Fin (r + 1)) : G.obj (pullbackChart ι j) := fU ι c j ^ E.e • E.y j

omit [IsAffineHom ι] in

theorem ExtData.key (E : ExtData ι G c d t) (j l : Fin (r + 1)) :
    restrictFun (pullbackOverlap_le_left ι j l) (fU ι c j) ^ E.e • G.res (pullbackOverlap_le_left ι j l) (E.y j)
      = (restrictFun (pullbackOverlap_le_left ι j l) (fU ι c j) ^ E.e *
          restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (d + E.n * (i + 1))) •
          G.res (pullbackOverlap_le_right ι j l) (E.y l) := by
  have h := E.hδ j l
  rw [smul_sub, sub_eq_zero, smul_smul] at h
  exact h

omit [IsAffineHom ι] in

theorem ExtData.framesCompat (E : ExtData ι G c d t) : OModulePresheaf.FramesCompat ι G (d + (E.n + E.e) * (i + 1)) E.t' := by
  intro j l
  simp only [ExtData.t']
  rw [res_pow_smul, res_pow_smul, E.key j l, smul_smul]
  congr 1
  have h1 := frameUnit_pow_mul_prod ι c j l
  rw [← h1]
  ring

omit [IsAffineHom ι] in

theorem ExtData.res_t' (E : ExtData ι G c d t) (j : Fin (r + 1)) :
    G.res (UW_le_U ι c j) (E.t' j)
      = (restrictFun (UW_le_U ι c j) (fU ι c j) ^ (E.n + E.e) * restrictFun (UW_le_U ι c j) (frameUnit ι j (c 0)) ^ d) •
          G.res (UW_le_W ι c j) t := by
  simp only [ExtData.t']
  rw [res_pow_smul, E.hy j, smul_smul, smul_smul]
  congr 1
  ring

end Extend

end P2mQcExtFrames

end

open AlgebraicGeometry.ProjSpace in
theorem solution
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (G : OModulePresheaf q) (hq : G.IsQuasicoherent)
    {i : ℕ} (c : Fin (i + 1) → Fin (r + 1)) (d : ℕ) (t : G.obj (⨅ v, ProjSpace.pullbackChart ι (c v))) :
    ∃ (N : ℕ) (t' : ∀ j : Fin (r + 1), G.obj (ProjSpace.pullbackChart ι j)),
      OModulePresheaf.FramesCompat ι G (d + N * (i + 1)) t' ∧
      ∀ j : Fin (r + 1),
        G.res (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
            (t' j) =
          ((∏ v : Fin (i + 1), ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c v))) ^ N *
              ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c 0)) ^ d) •
            G.res (inf_le_right : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ⨅ v, ProjSpace.pullbackChart ι (c v)) t := by
  obtain ⟨E⟩ := P2mQcExtFrames.exists_extData (ι := ι) (c := c) (d := d) (t := t) hq
  refine ⟨E.n + E.e, E.t', E.framesCompat, fun j => ?_⟩
  rw [E.res_t' j, ← map_prod]

end S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent (solution)
