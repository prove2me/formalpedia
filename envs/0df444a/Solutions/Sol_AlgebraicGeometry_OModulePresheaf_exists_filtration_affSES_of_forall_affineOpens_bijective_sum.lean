-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_filtration_affSES_of_forall_affineOpens_bijective_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/27c2a03e-056b-56e1-bd3d-1636e6c88c77

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace C5Body

p2m_open "AlgebraicGeometry AlgebraicGeometry.OModulePresheaf"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

noncomputable def AffSES.transferLeft {A A' B C : OModulePresheaf π} (S : AffSES A B C)
    (u : AffHom A' A) (v : AffHom A A') (huv : ∀ U x, u.app U (v.app U x) = x) (hvu : ∀ U x, v.app U (u.app U x) = x) :
    AffSES A' B C where
  inc := S.inc.comp u
  proj := S.proj
  injective U := by
    intro x y hxy
    have := S.injective U (by simpa [AffHom.comp_app] using hxy)
    simpa [hvu] using congrArg (v.app U) this
  surjective := S.surjective
  exact U := by
    rw [← S.exact U]
    ext z
    simp only [LinearMap.mem_range, AffHom.comp_app]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨u.app U x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨v.app U x, by rw [huv]⟩

noncomputable def AffSES.transferMid {A B B' C : OModulePresheaf π} (S : AffSES A B C)
    (u : AffHom B B') (v : AffHom B' B) (huv : ∀ U x, u.app U (v.app U x) = x) (hvu : ∀ U x, v.app U (u.app U x) = x) :
    AffSES A B' C where
  inc := u.comp S.inc
  proj := S.proj.comp v
  injective U := by
    intro x y hxy
    apply S.injective U
    simpa [AffHom.comp_app, hvu] using congrArg (v.app U) hxy
  surjective U := by
    intro c
    obtain ⟨b, hb⟩ := S.surjective U c
    exact ⟨u.app U b, by simp [AffHom.comp_app, hvu, hb]⟩
  exact U := by
    ext z
    simp only [LinearMap.mem_range, AffHom.comp_app, LinearMap.mem_ker]
    have hz : z = u.app U (v.app U z) := (huv U z).symm
    constructor
    · rintro ⟨a, rfl⟩
      rw [hvu]
      have : S.inc.app U a ∈ LinearMap.ker (S.proj.app U) := by
        rw [← S.exact U]; exact ⟨a, rfl⟩
      exact this
    · intro h0
      have : v.app U z ∈ LinearMap.range (S.inc.app U) := by rw [S.exact U]; exact h0
      obtain ⟨a, ha⟩ := this
      exact ⟨a, by rw [ha, ← hz]⟩

section Pieces

variable (E : OModulePresheaf π) (F : ℕ → OModulePresheaf π) (ι : ∀ j : ℕ, OModulePresheaf.Hom (F j) E)

noncomputable def piData (k : ℕ) : OModulePresheaf π where
  obj U := (i : Fin k) → (F i).obj U
  module U := inferInstance
  moduleSections U := Pi.module _ _ _
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a x => funext fun i => smul_assoc r a (x i)⟩
  res h := LinearMap.pi fun i => ((F i).res h).comp (LinearMap.proj i)
  res_smul h a x := funext fun i => (F i).res_smul h a (x i)
  res_refl U := LinearMap.ext fun x => funext fun i => LinearMap.congr_fun ((F i).res_refl U) (x i)
  res_comp h h' := LinearMap.ext fun x => funext fun i => LinearMap.congr_fun ((F i).res_comp h h') (x i)

theorem piData_res_apply (k : ℕ) {U U' : V.Opens} (h : U ≤ U') (x : (piData F k).obj U') (i : Fin k) :
    (piData F k).res h x i = (F i).res h (x i) := rfl

noncomputable def sumHom (k : ℕ) : OModulePresheaf.Hom (piData F k) E where
  app U := ∑ i : Fin k, ((ι i).app U).comp (LinearMap.proj i)
  app_smul U a x := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ι i).app_smul U a (x i)
  naturality h := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ι i).naturality_apply h (x i)

theorem sumHom_app (k : ℕ) (U : V.Opens) (x : (piData F k).obj U) :
    (sumHom E F ι k).app U x = ∑ i : Fin k, (ι i).app U (x i) := by
  change (∑ i : Fin k, ((ι i).app U).comp (LinearMap.proj i)) x = _
  rw [LinearMap.sum_apply]
  rfl

noncomputable def Q (k : ℕ) : OModulePresheaf π := OModulePresheaf.im (sumHom E F ι k)

noncomputable def gFun (k : ℕ) (U : V.Opens) (s : (i : Fin k) → (F i).obj U) (m : ℕ) : E.obj U :=
  if h : m < k then (ι m).app U (s ⟨m, h⟩) else 0

theorem sum_eq_sum_range_gFun (k : ℕ) (U : V.Opens) (s : (i : Fin k) → (F i).obj U) :
    ∑ i : Fin k, (ι i).app U (s i) = ∑ m ∈ Finset.range k, gFun E F ι k U s m := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gFun, dif_pos i.2]

noncomputable def extendZero {k d : ℕ} (U : V.Opens) (s : (i : Fin k) → (F i).obj U) : (j : Fin d) → (F j).obj U :=
  fun j => if h : (j : ℕ) < k then s ⟨j, h⟩ else 0

theorem sum_extendZero {k d : ℕ} (hk : k ≤ d) (U : V.Opens) (s : (i : Fin k) → (F i).obj U) :
    ∑ j : Fin d, (ι j).app U (extendZero F U s j) = ∑ i : Fin k, (ι i).app U (s i) := by
  rw [sum_eq_sum_range_gFun E F ι k U s]
  have h1 : ∑ j : Fin d, (ι j).app U (extendZero F U s j) = ∑ m ∈ Finset.range d, gFun E F ι k U s m := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (j : ℕ) < k
    · simp only [extendZero, gFun, dif_pos h]
    · simp only [extendZero, gFun, dif_neg h, map_zero]
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro m _ hm
  simp only [Finset.mem_range, not_lt] at hm
  simp only [gFun, dif_neg (not_lt.2 hm)]

theorem range_le_range_of_le {k k' : ℕ} (hk : k ≤ k') (U : V.Opens) :
    LinearMap.range ((sumHom E F ι k).app U) ≤ LinearMap.range ((sumHom E F ι k').app U) := by
  rintro x ⟨s, rfl⟩
  exact ⟨extendZero F U s, by rw [sumHom_app, sumHom_app, sum_extendZero E F ι hk]⟩

theorem range_zero_eq_bot (U : V.Opens) : LinearMap.range ((sumHom E F ι 0).app U) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨s, rfl⟩
  simp [sumHom_app]

section Affine

variable (d : ℕ) (h : ∀ U : V.affineOpens, Function.Bijective
      (fun s : (j : Fin d) → (F j).obj U.1 => ∑ j : Fin d, (ι j).app U.1 (s j)))

noncomputable def topIn : AffHom (Q E F ι d) E where
  app U := (LinearMap.range ((sumHom E F ι d).app U.1)).subtype
  app_smul _ _ _ := rfl
  naturality _ := rfl

include h

theorem bijective_sumHom (U : V.affineOpens) : Function.Bijective ((sumHom E F ι d).app U.1) := by
  have e : (fun s : (j : Fin d) → (F j).obj U.1 => ∑ j : Fin d, (ι j).app U.1 (s j)) = ⇑((sumHom E F ι d).app U.1) :=
    funext fun s => (sumHom_app E F ι d U.1 s).symm
  rw [← e]; exact h U

noncomputable def coords (U : V.affineOpens) : E.obj U.1 ≃ₗ[R] ((j : Fin d) → (F j).obj U.1) :=
  (LinearEquiv.ofBijective ((sumHom E F ι d).app U.1) (bijective_sumHom E F ι d h U)).symm

theorem coords_symm_apply (U : V.affineOpens) (s : (j : Fin d) → (F j).obj U.1) :
    (coords E F ι d h U).symm s = ∑ j : Fin d, (ι j).app U.1 (s j) := by
  rw [← sumHom_app E F ι d U.1 s]; rfl

theorem sum_coords (U : V.affineOpens) (x : E.obj U.1) :
    ∑ j : Fin d, (ι j).app U.1 (coords E F ι d h U x j) = x := by
  rw [← coords_symm_apply E F ι d h U]; exact (coords E F ι d h U).symm_apply_apply x

theorem coords_sum (U : V.affineOpens) (s : (j : Fin d) → (F j).obj U.1) :
    coords E F ι d h U (∑ j : Fin d, (ι j).app U.1 (s j)) = s := by
  rw [← coords_symm_apply E F ι d h U]; exact (coords E F ι d h U).apply_symm_apply s

theorem coords_sections_smul (U : V.affineOpens) (a : Γ(V, U.1)) (x : E.obj U.1) :
    coords E F ι d h U (a • x) = a • coords E F ι d h U x := by
  conv_lhs => rw [← sum_coords E F ι d h U x]
  rw [← sumHom_app, ← (sumHom E F ι d).app_smul, sumHom_app, coords_sum]
  rfl

theorem coords_res {U U' : V.affineOpens} (hle : U.1 ≤ U'.1) (x : E.obj U'.1) (j : Fin d) :
    coords E F ι d h U (E.res hle x) j = (F j).res hle (coords E F ι d h U' x j) := by
  conv_lhs => rw [← sum_coords E F ι d h U' x]
  rw [← sumHom_app, ← (sumHom E F ι d).naturality_apply hle, sumHom_app, coords_sum]
  rfl

theorem mem_range_iff_coords (U : V.affineOpens) {k : ℕ} (hk : k ≤ d) (x : E.obj U.1) :
    x ∈ LinearMap.range ((sumHom E F ι k).app U.1) ↔ ∀ j : Fin d, k ≤ (j : ℕ) → coords E F ι d h U x j = 0 := by
  constructor
  · rintro ⟨s, rfl⟩ j hj
    rw [sumHom_app, ← sum_extendZero E F ι hk, coords_sum]
    simp only [extendZero, dif_neg (not_lt.2 hj)]
  · intro hz
    refine ⟨fun i => coords E F ι d h U x ⟨i, lt_of_lt_of_le i.2 hk⟩, ?_⟩
    rw [sumHom_app]
    conv_rhs => rw [← sum_coords E F ι d h U x]
    rw [← sum_extendZero E F ι hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · simp only [extendZero, dif_pos hj]
    · simp only [extendZero, dif_neg hj]; rw [hz j (not_lt.1 hj)]

noncomputable def core {k : ℕ} (hk : k < d) : AffSES (Q E F ι k) (Q E F ι (k + 1)) (F k) where
  inc :=
    { app := fun U => Submodule.inclusion (range_le_range_of_le E F ι (Nat.le_succ k) U.1)
      app_smul := fun U a x => rfl
      naturality := fun hle => rfl }
  proj :=
    { app := fun U =>
        { toFun := fun x => coords E F ι d h U x.1 ⟨k, hk⟩
          map_add' := fun x y => by
            change coords E F ι d h U (x.1 + y.1) ⟨k, hk⟩ = _
            rw [map_add]; rfl
          map_smul' := fun r x => by
            change coords E F ι d h U (r • x.1) ⟨k, hk⟩ = _
            rw [LinearEquiv.map_smul]; rfl }
      app_smul := fun U a x => by
        change coords E F ι d h U (a • x.1) ⟨k, hk⟩ = a • coords E F ι d h U x.1 ⟨k, hk⟩
        rw [coords_sections_smul]; rfl
      naturality := fun {U U'} hle => by
        refine LinearMap.ext fun x => ?_
        change coords E F ι d h U (E.res hle x.1) ⟨k, hk⟩ = (F k).res hle (coords E F ι d h U' x.1 ⟨k, hk⟩)
        exact coords_res E F ι d h hle x.1 ⟨k, hk⟩ }
  injective U := by
    intro x y hxy
    exact Submodule.inclusion_injective (range_le_range_of_le E F ι (Nat.le_succ k) U.1) hxy
  surjective U := by
    intro y
    refine ⟨⟨(ι k).app U.1 y, ?_⟩, ?_⟩
    · refine ⟨Fin.snoc (α := fun i : Fin (k + 1) => (F i).obj U.1) (fun _ => 0) y, ?_⟩
      rw [sumHom_app, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, map_zero, Finset.sum_const_zero, zero_add, Fin.snoc_last]
      rfl
    · change coords E F ι d h U ((ι k).app U.1 y) ⟨k, hk⟩ = y
      have : (ι k).app U.1 y = ∑ j : Fin d, (ι j).app U.1
          (extendZero (k := k + 1) F U.1 (Fin.snoc (α := fun i : Fin (k + 1) => (F i).obj U.1) (fun _ => 0) y) j) := by
        rw [sum_extendZero E F ι hk, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, map_zero, Finset.sum_const_zero, zero_add, Fin.snoc_last]
        rfl
      rw [this, coords_sum]
      simp only [extendZero, Nat.lt_succ_self, dif_pos]
      exact Fin.snoc_last (α := fun i : Fin (k + 1) => (F i).obj U.1) _ _
  exact U := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    change (∃ z, Submodule.inclusion _ z = x) ↔ coords E F ι d h U x.1 ⟨k, hk⟩ = 0
    constructor
    · rintro ⟨z, rfl⟩
      exact (mem_range_iff_coords E F ι d h U hk.le z.1).1 z.2 ⟨k, hk⟩ le_rfl
    · intro h0
      have hx1 := (mem_range_iff_coords E F ι d h U (Nat.succ_le_of_lt hk) x.1).1 x.2
      have : x.1 ∈ LinearMap.range ((sumHom E F ι k).app U.1) := by
        refine (mem_range_iff_coords E F ι d h U hk.le x.1).2 fun j hj => ?_
        rcases Nat.lt_or_ge k j with hlt | hge
        · exact hx1 j hlt
        · have : j = ⟨k, hk⟩ := Fin.ext (le_antisymm hge hj)
          subst this; exact h0
      exact ⟨⟨x.1, this⟩, rfl⟩

theorem mem_range_top (U : V.affineOpens) (x : E.obj U.1) : x ∈ LinearMap.range ((sumHom E F ι d).app U.1) :=
  ⟨coords E F ι d h U x, by rw [sumHom_app, sum_coords]⟩

noncomputable def topOut : AffHom E (Q E F ι d) where
  app U := LinearMap.codRestrict _ LinearMap.id fun x => mem_range_top E F ι d h U x
  app_smul _ _ _ := rfl
  naturality _ := rfl

end Affine

noncomputable def botIn : AffHom (OModulePresheaf.zero π) (Q E F ι 0) := AffHom.zeroFrom _
noncomputable def botOut : AffHom (Q E F ι 0) (OModulePresheaf.zero π) := AffHom.zeroTo _

theorem Q_zero_eq (U : V.affineOpens) (x : (Q E F ι 0).obj U.1) : x = 0 := by
  apply Subtype.ext
  obtain ⟨s, hs⟩ := x.2
  change x.1 = 0
  rw [← hs, sumHom_app]
  simp

end Pieces

end C5Body

open C5Body in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (E : OModulePresheaf π) (d : ℕ) (hd : 0 < d) (F : ℕ → OModulePresheaf π)
    (ι : ∀ j : ℕ, OModulePresheaf.Hom (F j) E)
    (h : ∀ U : V.affineOpens, Function.Bijective
      (fun s : (j : Fin d) → (F j).obj U.1 => ∑ j : Fin d, (ι j).app U.1 (s j))) :
    ∃ P : ℕ → OModulePresheaf π,
      P 0 = OModulePresheaf.zero π ∧ P d = E ∧
      ∀ j : ℕ, j < d → Nonempty (OModulePresheaf.AffSES (P j) (P (j + 1)) (F j)) := by
  classical
  let P : ℕ → OModulePresheaf π := fun j => if j = 0 then OModulePresheaf.zero π else if d ≤ j then E else Q E F ι j
  have hP0 : P 0 = OModulePresheaf.zero π := by simp [P]
  have hPd : P d = E := by simp [P, Nat.pos_iff_ne_zero.1 hd]
  refine ⟨P, hP0, hPd, fun j hj => ?_⟩

  have S0 : OModulePresheaf.AffSES (Q E F ι j) (Q E F ι (j + 1)) (F j) := core E F ι d h hj

  have S1 : OModulePresheaf.AffSES (Q E F ι j) (P (j + 1)) (F j) := by
    by_cases htop : d ≤ j + 1
    · have hdj : j + 1 = d := le_antisymm (Nat.succ_le_of_lt hj) htop
      have : P (j + 1) = E := by simp [P, htop]
      rw [this]
      subst hdj
      exact C5Body.AffSES.transferMid S0 (topIn E F ι (j + 1)) (topOut E F ι (j + 1) h)
        (fun U x => rfl) (fun U x => Subtype.ext rfl)
    · have : P (j + 1) = Q E F ι (j + 1) := by simp [P, htop]
      rw [this]; exact S0
  by_cases hbot : j = 0
  · subst hbot
    rw [hP0]
    exact ⟨C5Body.AffSES.transferLeft S1 (botIn E F ι) (botOut E F ι)
      (fun U x => by rw [Q_zero_eq E F ι U x, Q_zero_eq E F ι U ((botIn E F ι).app U _)])
      (fun U x => Subsingleton.elim _ _)⟩
  · have : P j = Q E F ι j := by simp [P, hbot, not_le.2 hj]
    rw [this]; exact ⟨S1⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum (solution)
