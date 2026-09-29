-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.IterCech.exists_dTot_eq_single_augTot_sub_single_augCech_cup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/391faffb-9e1f-5c2b-ac64-8128080a9338

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_IterCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_oext
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.Hom Spec Scheme IsAffineOpen Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.res_res OModulePresheaf.unit OModulePresheaf.unit_res_apply OModulePresheaf.unit_smul OModulePresheaf.res_smul Scheme.OrderedAffineCover.preimage_iInf_fin OModulePresheaf.cup_apply Scheme.OrderedOpenFamily Scheme.OrderedOpenFamily.face_val OModulePresheaf.BiCech.C OModulePresheaf.BiCech.dH_apply OModulePresheaf.BiCech.dV_apply OModulePresheaf.biCech_dH OModulePresheaf.biCech_dV OModulePresheaf.IterCech.dV_apply OModulePresheaf.IterCech.resTot₀_apply OModulePresheaf.IterCech.augTot OModulePresheaf.IterCech.augTot_apply OModulePresheaf.IterCech.augCech OModulePresheaf.IterCech.augCech_apply OModulePresheaf.iterCech_dH OModulePresheaf.iterCech_dV OModulePresheaf.unitPullback Scheme.OrderedAffineCover.oface Scheme.OrderedAffineCover.osort_val"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_res cochain d H0 unit unit_res_apply unit_smul res res_smul obj cup cup_apply BiCech.C BiCech.dH_apply BiCech.dV_apply biCech biCech_dH biCech_dV IterCech.resTot_apply IterCech.C IterCech.dH IterCech.dH_apply IterCech.dV_apply IterCech.resTot₀_apply IterCech.augTot IterCech.augTot_apply IterCech.augCech IterCech.augCech_apply iterCech iterCech_dH iterCech_dV unitPullback od od_apply ores_apply oext oext_apply_of_injective ounitPullback_apply od_oext ores_ounitPullback_oext"
namespace IterCech
p2m_export "AlgebraicGeometry.OModulePresheaf.IterCech" "resTot_apply C dH dH_apply dV_apply resTot₀_apply augTot augTot_apply augCech augCech_apply"
namespace Staircase
p2m_open "AlgebraicGeometry.OModulePresheaf.IterCech AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section AVal

variable {k : Type u} [CommRing k] {X P : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of k)}
  (f : P ⟶ X) (𝔘 : X.OrderedAffineCover) (p : ℕ) (α : (unit πX).cochain 𝔘 p)

def aval (u : Fin (p + 1) → 𝔘.ι) (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u) : Γ(P, O) :=
  (f.appLE (𝔘.ointer u) O h).hom ((unit πX).oext 𝔘 p α u)

theorem aval_congr {u u' : Fin (p + 1) → 𝔘.ι} (e : u = u') (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u)
    (h' : O ≤ f ⁻¹ᵁ 𝔘.ointer u') : aval f 𝔘 p α u O h = aval f 𝔘 p α u' O h' := by
  subst e; rfl

theorem map_aval (u : Fin (p + 1) → 𝔘.ι) {O O' : P.Opens} (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u) (i : O' ≤ O) :
    (P.presheaf.map (homOfLE i).op).hom (aval f 𝔘 p α u O h) = aval f 𝔘 p α u O' (i.trans h) := by
  rw [aval, aval, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

omit p α in
theorem le_preimage_ointer {n : ℕ} (u : Fin (n + 1) → 𝔘.ι) (O : P.Opens) (h : ∀ j, O ≤ f ⁻¹ᵁ 𝔘.U (u j)) :
    O ≤ f ⁻¹ᵁ 𝔘.ointer u := by
  show O ≤ f ⁻¹ᵁ (⨅ j, 𝔘.U (u j))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  exact le_iInf h

theorem sum_aval_oface (hα : (unit πX).d 𝔘 p α = 0) (u : Fin (p + 2) → 𝔘.ι) (O : P.Opens)
    (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u) :
    ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) •
      aval f 𝔘 p α (𝔘.oface u l) O (h.trans (f.preimage_mono (𝔘.ointer_le_ointer_oface u l))) = 0 := by
  have hod : (unit πX).od 𝔘 p ((unit πX).oext 𝔘 p α) u = 0 := by
    rw [od_oext, hα, map_zero, Pi.zero_apply]
  rw [od_apply] at hod
  change (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (X.presheaf.map (homOfLE (𝔘.ointer_le_ointer_oface u j)).op).hom ((unit πX).oext 𝔘 p α (𝔘.oface u j)))
    = (0 : Γ(X, 𝔘.ointer u)) at hod
  have key := congrArg (f.appLE (𝔘.ointer u) O h).hom hod
  rw [map_sum, map_zero] at key
  refine (Finset.sum_congr rfl fun l _ => ?_).trans key
  rw [map_zsmul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

theorem aval_val (s : 𝔘.Idx p) (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.ointer s.1) :
    aval f 𝔘 p α s.1 O h = (f.appLE (𝔘.inter s) O h).hom (α s) := by
  have hinj : Function.Injective s.1 := s.2.injective
  have hsort : Tuple.sort s.1 = Equiv.refl _ := (Tuple.sort_eq_refl_iff_monotone).2 s.2.monotone
  have hos : 𝔘.osort s.1 hinj = s := Subtype.ext (by rw [Scheme.OrderedAffineCover.osort_val, hsort]; rfl)
  rw [aval, oext_apply_of_injective _ _ _ _ _ hinj, hsort, Equiv.Perm.sign_refl, Units.val_one, one_smul]

  have key : ∀ (s' : 𝔘.Idx p) (e : s' = s) (h1 : 𝔘.ointer s.1 ≤ 𝔘.inter s'),
      (f.appLE (𝔘.ointer s.1) O h).hom ((X.presheaf.map (homOfLE h1).op).hom (α s'))
        = (f.appLE (𝔘.inter s) O h).hom (α s) := by
    intro s' e h1; subst e
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact key _ hos _

end AVal

section Tuples

variable {ιP ιU ιV : Type*}

def tupA (fstP : ιP → ιU) (r p' p : ℕ) (h : r + p' + 1 = p) (K : Fin (r + 1) → ιP) (s : Fin (p' + 1) → ιU) :
    Fin (p + 1) → ιU :=
  fun j => if hj : (j : ℕ) ≤ r then fstP (K ⟨j, by omega⟩) else s ⟨(j : ℕ) - (r + 1), by omega⟩

def tupT (q' q : ℕ) (h : q' = q) (t : Fin (q' + 1) → ιV) : Fin (q + 1) → ιV := fun j => t ⟨j, by omega⟩

def tupK (fstP : ιP → ιU) (r p : ℕ) (h : p ≤ r) (K : Fin (r + 1) → ιP) : Fin (p + 1) → ιU :=
  fun j => fstP (K ⟨j, by omega⟩)

def tupB (sndP : ιP → ιV) (r q' p q : ℕ) (h : p ≤ r) (h' : r + q' + 1 = p + q) (K : Fin (r + 1) → ιP)
    (t : Fin (q' + 1) → ιV) : Fin (q + 1) → ιV :=
  fun j => if hj : p + (j : ℕ) ≤ r then sndP (K ⟨p + j, by omega⟩) else t ⟨p + (j : ℕ) - (r + 1), by omega⟩

def tupKB (sndP : ιP → ιV) (n p q : ℕ) (h : p + q = n) (K : Fin (n + 1) → ιP) : Fin (q + 1) → ιV :=
  fun j => sndP (K ⟨p + j, by omega⟩)

end Tuples

section Setup

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
  (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
  (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
  (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι, (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)

abbrev OO {r p' q' : ℕ} (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx p') (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx q') :
    (pullback πX πY).Opens :=
  (𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).inter t

variable {r p' q' : ℕ} (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx p') (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx q')

theorem OO_le_interK : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K :=
  inf_le_right.trans (((𝔙.preimageFamily (pullback.snd πX πY)).restr_inter_le _ t).trans inf_le_right)

theorem OO_le_fst (a : Fin (p' + 1)) : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.fst πX πY) ⁻¹ᵁ 𝔘.U (s.1 a) :=
  inf_le_left.trans ((𝔘.preimageFamily (pullback.fst πX πY)).inter_le s a)

theorem OO_le_K_fst (l : Fin (r + 1)) : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.fst πX πY) ⁻¹ᵁ 𝔘.U (ofLex (K.1 l)).1 :=
  (OO_le_interK πX πY 𝔘 𝔙 haff hcov K s t).trans ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter_le K l).trans inf_le_left)

theorem OO_le_K_snd (l : Fin (r + 1)) : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.snd πX πY) ⁻¹ᵁ 𝔙.U (ofLex (K.1 l)).2 :=
  (OO_le_interK πX πY 𝔘 𝔙 haff hcov K s t).trans ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter_le K l).trans inf_le_right)

theorem OO_le_snd (b : Fin (q' + 1)) : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.snd πX πY) ⁻¹ᵁ 𝔙.U (t.1 b) :=
  inf_le_right.trans ((((𝔙.preimageFamily (pullback.snd πX πY)).restr_inter_le _ t).trans inf_le_left).trans ((𝔙.preimageFamily (pullback.snd πX πY)).inter_le t b))

theorem le_tupA (p : ℕ) (h : r + p' + 1 = p) :
    OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.fst πX πY) ⁻¹ᵁ 𝔘.ointer (tupA (fun ij => (ofLex ij).1) r p' p h K.1 s.1) := by
  refine le_preimage_ointer _ 𝔘 _ _ fun j => ?_
  unfold tupA
  split_ifs with hj
  · exact OO_le_K_fst πX πY 𝔘 𝔙 haff hcov K s t _
  · exact OO_le_fst πX πY 𝔘 𝔙 haff hcov K s t _

theorem le_tupT (q : ℕ) (h : q' = q) :
    OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.snd πX πY) ⁻¹ᵁ 𝔙.ointer (tupT q' q h t.1) :=
  le_preimage_ointer _ 𝔙 _ _ fun j => OO_le_snd πX πY 𝔘 𝔙 haff hcov K s t _

theorem le_tupK (p : ℕ) (h : p ≤ r) :
    OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.fst πX πY) ⁻¹ᵁ 𝔘.ointer (tupK (fun ij => (ofLex ij).1) r p h K.1) :=
  le_preimage_ointer _ 𝔘 _ _ fun j => OO_le_K_fst πX πY 𝔘 𝔙 haff hcov K s t _

theorem le_tupB (p q : ℕ) (h : p ≤ r) (h' : r + q' + 1 = p + q) :
    OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.snd πX πY) ⁻¹ᵁ 𝔙.ointer (tupB (fun ij => (ofLex ij).2) r q' p q h h' K.1 t.1) := by
  refine le_preimage_ointer _ 𝔙 _ _ fun j => ?_
  unfold tupB
  split_ifs with hj
  · exact OO_le_K_snd πX πY 𝔘 𝔙 haff hcov K s t _
  · exact OO_le_snd πX πY 𝔘 𝔙 haff hcov K s t _

variable (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (β : (unit πY).cochain 𝔙 q)

omit K s t in

def ent (r m' : ℕ) : IterCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily r m' :=
  fun K pq st =>
    if hA : r + pq.1.1 + 1 = p ∧ pq.1.2 = q then
      (show Γ((pullback πX πY), OO πX πY 𝔘 𝔙 haff hcov K st.1 st.2) from
        ((-1 : ℤ) ^ r) •
          (aval (pullback.fst πX πY) 𝔘 p α _ _ (le_tupA πX πY 𝔘 𝔙 haff hcov K st.1 st.2 p hA.1) *
            aval (pullback.snd πX πY) 𝔙 q β _ _ (le_tupT πX πY 𝔘 𝔙 haff hcov K st.1 st.2 q hA.2)))
    else if hB : p ≤ r ∧ pq.1.1 = 0 ∧ r + pq.1.2 + 1 = p + q then
      (show Γ((pullback πX πY), OO πX πY 𝔘 𝔙 haff hcov K st.1 st.2) from
        ((-1 : ℤ) ^ r) •
          (aval (pullback.fst πX πY) 𝔘 p α _ _ (le_tupK πX πY 𝔘 𝔙 haff hcov K st.1 st.2 p hB.1) *
            aval (pullback.snd πX πY) 𝔙 q β _ _ (le_tupB πX πY 𝔘 𝔙 haff hcov K st.1 st.2 p q hB.1 hB.2.2)))
    else 0

end Setup

section Bridges

variable {k : Type u} [CommRing k] {X P : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of k)}
  (f : P ⟶ X) (𝔘 : X.OrderedAffineCover)

omit 𝔘 in
theorem map_app_eq_appLE {U : X.Opens} {V : P.Opens} (e : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)) :
    (P.presheaf.map (homOfLE e).op).hom ((f.app U).hom x) = (f.appLE U V e).hom x := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

omit 𝔘 in
private theorem _root_.AlgebraicGeometry.OModulePresheaf.IterCech.Staircase.map_appLE {U : X.Opens} {V W : P.Opens} (e : V ≤ f ⁻¹ᵁ U) (i : W ≤ V) (x : Γ(X, U)) :
    (P.presheaf.map (homOfLE i).op).hom ((f.appLE U V e).hom x) = (f.appLE U W (i.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

p2m_export "AlgebraicGeometry.OModulePresheaf.IterCech.Staircase" "map_appLE"

theorem map_map_app_eq_aval (p : ℕ) (α : (unit πX).cochain 𝔘 p) (s : 𝔘.Idx p) {V W : P.Opens}
    (e : V ≤ f ⁻¹ᵁ 𝔘.inter s) (i : W ≤ V) :
    (P.presheaf.map (homOfLE i).op).hom ((P.presheaf.map (homOfLE e).op).hom ((f.app (𝔘.inter s)).hom (α s)))
      = aval f 𝔘 p α s.1 W (i.trans e) := by
  rw [map_app_eq_appLE, map_appLE, aval_val]

omit 𝔘 in
theorem tuple_one_eq (ι : Type*) (u : Fin 1 → ι) : u = fun _ => u 0 :=
  funext fun j => congrArg u (Fin.eq_zero j)

theorem aval_zero_eq (α : (unit πX).cochain 𝔘 0) (hα : (unit πX).d 𝔘 0 α = 0) (u v : Fin 1 → 𝔘.ι)
    (O : P.Opens) (hu : O ≤ f ⁻¹ᵁ 𝔘.ointer u) (hv : O ≤ f ⁻¹ᵁ 𝔘.ointer v) :
    aval f 𝔘 0 α u O hu = aval f 𝔘 0 α v O hv := by
  let w : Fin 2 → 𝔘.ι := fun j => if (j : ℕ) = 0 then v 0 else u 0
  have hOu : O ≤ f ⁻¹ᵁ 𝔘.U (u 0) := hu.trans (f.preimage_mono (𝔘.ointer_le u 0))
  have hOv : O ≤ f ⁻¹ᵁ 𝔘.U (v 0) := hv.trans (f.preimage_mono (𝔘.ointer_le v 0))
  have hw : O ≤ f ⁻¹ᵁ 𝔘.ointer w := le_preimage_ointer f 𝔘 w O fun j => by
    by_cases hj : (j : ℕ) = 0
    · simp only [w, hj, if_true]; exact hOv
    · simp only [w, hj, if_false]; exact hOu
  have h0 : 𝔘.oface w 0 = u := by
    funext j
    simp only [Scheme.OrderedAffineCover.oface, Function.comp_apply, Fin.succAbove_zero, w, Fin.val_succ,
      Nat.succ_ne_zero, if_false]
    exact congrArg u (Fin.eq_zero j).symm
  have h1 : 𝔘.oface w 1 = v := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    show w (Fin.succAbove 1 0) = v 0
    rw [show Fin.succAbove (1 : Fin 2) (0 : Fin 1) = 0 from by decide]
    simp only [w, Fin.val_zero, if_true]
  have key := sum_aval_oface f 𝔘 0 α hα w O hw
  rw [Fin.sum_univ_two] at key
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at key
  rw [add_neg_eq_zero, aval_congr f 𝔘 0 α h0 O _ hu, aval_congr f 𝔘 0 α h1 O _ hv] at key
  exact key

variable {R' : Type u} [CommRing R'] {πP : P ⟶ Spec (CommRingCat.of R')}

theorem unitPullback_eq_aval (𝒲 : P.OrderedAffineCover) (lam : 𝒲.ι → 𝔘.ι)
    (hlam : ∀ w, 𝒲.U w ≤ f ⁻¹ᵁ 𝔘.U (lam w)) (p : ℕ) (α : (unit πX).cochain 𝔘 p) (s : 𝒲.Idx p) :
    unitPullback (πX := πP) f 𝒲 𝔘 lam hlam p α s
      = aval f 𝔘 p α (lam ∘ s.1) (𝒲.inter s) (𝒲.ointer_le_preimage_ointer_comp f 𝔘 lam hlam s.1) := by
  rw [← ores_ounitPullback_oext πP πX f 𝒲 𝔘 lam hlam p α, ores_apply, ounitPullback_apply, aval,
    map_app_eq_appLE]
  rfl

end Bridges

section BridgesD

variable {k : Type u} [CommRing k] {X P : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of k)}
  (f : P ⟶ X) (𝔘 : X.OrderedAffineCover)

def avalD (p : ℕ) (α : (unit πX).cochain 𝔘 p) (u : Fin (p + 1) → 𝔘.ι) (O : P.Opens) : Γ(P, O) := by
  classical
  exact if h : O ≤ f ⁻¹ᵁ 𝔘.ointer u then aval f 𝔘 p α u O h else 0

theorem avalD_eq (p : ℕ) (α : (unit πX).cochain 𝔘 p) (u : Fin (p + 1) → 𝔘.ι) (O : P.Opens)
    (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u) : avalD f 𝔘 p α u O = aval f 𝔘 p α u O h := by
  unfold avalD
  rw [dif_pos h]

theorem map_avalD (p : ℕ) (α : (unit πX).cochain 𝔘 p) (u : Fin (p + 1) → 𝔘.ι) {O O' : P.Opens} (i : O' ≤ O)
    (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u) :
    (P.presheaf.map (homOfLE i).op).hom (avalD f 𝔘 p α u O) = avalD f 𝔘 p α u O' := by
  rw [avalD_eq f 𝔘 p α u O h, avalD_eq f 𝔘 p α u O' (i.trans h), map_aval]

theorem sum_avalD_oface (p : ℕ) (α : (unit πX).cochain 𝔘 p) (hα : (unit πX).d 𝔘 p α = 0)
    (u : Fin (p + 2) → 𝔘.ι) (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.ointer u) :
    ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) • avalD f 𝔘 p α (u ∘ Fin.succAbove l) O = 0 := by
  rw [← sum_aval_oface f 𝔘 p α hα u O h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [avalD_eq]
  rfl

theorem avalD_zero_eq (α : (unit πX).cochain 𝔘 0) (hα : (unit πX).d 𝔘 0 α = 0) (u v : Fin 1 → 𝔘.ι)
    (O : P.Opens) (hu : O ≤ f ⁻¹ᵁ 𝔘.ointer u) (hv : O ≤ f ⁻¹ᵁ 𝔘.ointer v) :
    avalD f 𝔘 0 α u O = avalD f 𝔘 0 α v O := by
  rw [avalD_eq f 𝔘 0 α u O hu, avalD_eq f 𝔘 0 α v O hv]
  exact aval_zero_eq f 𝔘 α hα u v O hu hv

theorem avalD_val (p : ℕ) (α : (unit πX).cochain 𝔘 p) (s : 𝔘.Idx p) (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.inter s) :
    avalD f 𝔘 p α s.1 O = (f.appLE (𝔘.inter s) O h).hom (α s) := by
  rw [avalD_eq f 𝔘 p α s.1 O h, aval_val]

end BridgesD

theorem Fin.val_succAbove_ite' {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases hlt : (i : ℕ) < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simpa using hlt)), if_pos hlt, Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (by simpa using not_lt.1 hlt)), if_neg hlt,
      Fin.val_succ]

scoped macro "tup_close" : tactic =>
  `(tactic| first
    | rfl
    | (exfalso; omega)
    | (congr 1; apply Fin.ext; simp only [Fin.val_mk]; omega)
    | (congr 1; apply Fin.ext; simp only [Fin.val_mk, Fin.val_succAbove_ite']; split_ifs <;> omega)
    | (congr 1; congr 1; apply Fin.ext; simp only [Fin.val_mk]; omega)
    | (congr 1; congr 1; apply Fin.ext; simp only [Fin.val_mk, Fin.val_succAbove_ite']; split_ifs <;> omega))

section TupleFaces

variable {ιP ιU ιV : Type*} (fstP : ιP → ιU) (sndP : ιP → ιV)

theorem tupA_face_K (r a p : ℕ) (h : r + 1 + a + 1 = p + 1) (K : Fin (r + 2) → ιP) (s : Fin (a + 1) → ιU)
    (l : Fin (r + 2)) (i : Fin (p + 2)) (hi : (i : ℕ) = l) :
    tupA fstP r a p (by omega) (K ∘ Fin.succAbove l) s = tupA fstP (r + 1) a (p + 1) h K s ∘ Fin.succAbove i := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 h2 h2 <;> simp only [hv] at h1 h2 ⊢ <;> (try split_ifs at h1 h2 ⊢) <;> tup_close

theorem tupA_face_s (r a p : ℕ) (h : r + (a + 1) + 1 = p + 1) (K : Fin (r + 1) → ιP) (s : Fin (a + 2) → ιU)
    (j : Fin (a + 2)) (i : Fin (p + 2)) (hi : (i : ℕ) = r + 1 + j) :
    tupA fstP r a p (by omega) K (s ∘ Fin.succAbove j) = tupA fstP r (a + 1) (p + 1) h K s ∘ Fin.succAbove i := by
  funext x
  have hv := Fin.val_succAbove_ite' i x
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 h2 h2 <;> simp only [hv] at h1 h2 ⊢ <;> (try split_ifs at h1 h2 ⊢) <;> tup_close

theorem tupT_self (q : ℕ) (h : q = q) (t : Fin (q + 1) → ιV) : tupT q q h t = t := by
  funext j
  rfl

theorem tupK_face_le (r p : ℕ) (h : p ≤ r) (hp : p + 1 ≤ r + 1) (K : Fin (r + 2) → ιP) (l : Fin (r + 2))
    (i : Fin (p + 2)) (hi : (i : ℕ) = l) :
    tupK fstP r p h (K ∘ Fin.succAbove l) = tupK fstP (r + 1) (p + 1) hp K ∘ Fin.succAbove i := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  (try split_ifs at hv ⊢) <;> simp only [hv] <;> tup_close

theorem tupK_face_gt (r p : ℕ) (h : p ≤ r) (h' : p ≤ r + 1) (K : Fin (r + 2) → ιP) (l : Fin (r + 2))
    (hl : p + 1 ≤ (l : ℕ)) :
    tupK fstP r p h (K ∘ Fin.succAbove l) = tupK fstP (r + 1) p h' K := by
  funext j
  simp only [Function.comp_apply, tupK]
  tup_close

theorem tupK_eq_face_last (r p : ℕ) (h : p ≤ r) (hp : p + 1 ≤ r) (K : Fin (r + 1) → ιP) (i : Fin (p + 2))
    (hi : (i : ℕ) = p + 1) :
    tupK fstP r p h K = tupK fstP r (p + 1) hp K ∘ Fin.succAbove i := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  (try split_ifs at hv ⊢) <;> simp only [hv] <;> tup_close

theorem tupB_face_K_le (r b p q : ℕ) (h : p ≤ r) (h' : r + b + 1 = p + q) (K : Fin (r + 2) → ιP)
    (t : Fin (b + 1) → ιV) (l : Fin (r + 2)) (hl : (l : ℕ) ≤ p) (i : Fin (q + 2)) (hi : (i : ℕ) = 0) :
    tupB sndP r b p q h h' (K ∘ Fin.succAbove l) t
      = tupB sndP (r + 1) b p (q + 1) (by omega) (by omega) K t ∘ Fin.succAbove i := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 h2 h2 <;> simp only [hv] at h1 h2 ⊢ <;> (try split_ifs at h1 h2 ⊢) <;> tup_close

theorem tupB_face_K_ge (r b p q : ℕ) (h : p ≤ r) (h' : r + b + 1 = p + q) (K : Fin (r + 2) → ιP)
    (t : Fin (b + 1) → ιV) (l : Fin (r + 2)) (hl : p ≤ (l : ℕ)) (i : Fin (q + 2)) (hi : (i : ℕ) = l - p) :
    tupB sndP r b p q h h' (K ∘ Fin.succAbove l) t
      = tupB sndP (r + 1) b p (q + 1) (by omega) (by omega) K t ∘ Fin.succAbove i := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 h2 h2 <;> simp only [hv] at h1 h2 ⊢ <;> (try split_ifs at h1 h2 ⊢) <;> tup_close

theorem tupB_face_t (r b p q : ℕ) (h : p ≤ r) (h' : r + b + 1 = p + q) (K : Fin (r + 1) → ιP)
    (t : Fin (b + 2) → ιV) (j : Fin (b + 2)) (i : Fin (q + 2)) (hi : (i : ℕ) = r + 1 - p + j) :
    tupB sndP r b p q h h' K (t ∘ Fin.succAbove j)
      = tupB sndP r (b + 1) p (q + 1) h (by omega) K t ∘ Fin.succAbove i := by
  funext x
  have hv := Fin.val_succAbove_ite' i x
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 h2 h2 <;> simp only [hv] at h1 h2 ⊢ <;> (try split_ifs at h1 h2 ⊢) <;> tup_close

theorem tupB_self_face_zero (b p : ℕ) (K : Fin (p + 1) → ιP) (t : Fin (b + 1) → ιV) (i : Fin (b + 2))
    (hi : (i : ℕ) = 0) :
    tupB sndP p b p (b + 1) le_rfl (by omega) K t ∘ Fin.succAbove i = t := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 <;> simp only [hv] at h1 ⊢ <;> (try split_ifs at h1 ⊢) <;> tup_close

theorem tupA_zero_face_last (p : ℕ) (K : Fin (p + 1) → ιP) (s : Fin 1 → ιU) (i : Fin (p + 2))
    (hi : (i : ℕ) = p + 1) :
    tupA fstP p 0 (p + 1) (by omega) K s ∘ Fin.succAbove i = tupK fstP p p le_rfl K := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 <;> simp only [hv] at h1 ⊢ <;> (try split_ifs at h1 ⊢) <;> tup_close

theorem tupB_zero_face_last (n p q : ℕ) (h : p + q = n) (K : Fin (n + 1) → ιP) (t : Fin 1 → ιV)
    (i : Fin (q + 2)) (hi : (i : ℕ) = q + 1) :
    tupB sndP n 0 p (q + 1) (by omega) (by omega) K t ∘ Fin.succAbove i = tupKB sndP n p q h K := by
  funext j
  have hv := Fin.val_succAbove_ite' i j
  rw [hi] at hv
  simp only [Function.comp_apply, tupA, tupK, tupB, tupT, tupKB]
  split_ifs with h1 <;> simp only [hv] at h1 ⊢ <;> (try split_ifs at h1 ⊢) <;> tup_close

end TupleFaces

section Comb

variable {ι M : Type*} [AddCommGroup M]

theorem sum_fin_split (a b n : ℕ) (h : a + b = n) (g : Fin n → M) :
    ∑ i, g i = ∑ i : Fin a, g ⟨i, by omega⟩ + ∑ j : Fin b, g ⟨a + j, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_add]
  rfl

theorem cocycle_last (n : ℕ) (Xv : (Fin (n + 1) → ι) → M) (u : Fin (n + 2) → ι)
    (hX : ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Xv (u ∘ Fin.succAbove i) = 0)
    (e : Fin (n + 1) → Fin (n + 2)) (he : ∀ l, (e l : ℕ) = l) (z : Fin (n + 2)) (hz : (z : ℕ) = n + 1) :
    ∑ l : Fin (n + 1), ((-1 : ℤ) ^ (l : ℕ)) • Xv (u ∘ Fin.succAbove (e l))
      = ((-1 : ℤ) ^ n) • Xv (u ∘ Fin.succAbove z) := by
  have he' : ∀ l, e l = Fin.castSucc l := fun l => Fin.ext (by rw [he, Fin.val_castSucc])
  have hz' : z = Fin.last (n + 1) := Fin.ext (by rw [hz, Fin.val_last])
  simp only [he', hz']
  rw [Fin.sum_univ_castSucc] at hX
  simp only [Fin.val_castSucc, Fin.val_last] at hX
  rw [eq_neg_of_add_eq_zero_left hX, pow_succ, mul_neg_one, neg_smul, neg_neg]

theorem cocycle_first (n : ℕ) (Xv : (Fin (n + 1) → ι) → M) (u : Fin (n + 2) → ι)
    (hX : ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Xv (u ∘ Fin.succAbove i) = 0)
    (e : Fin (n + 1) → Fin (n + 2)) (he : ∀ j, (e j : ℕ) = j + 1) (z : Fin (n + 2)) (hz : (z : ℕ) = 0) :
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) • Xv (u ∘ Fin.succAbove (e j)) = Xv (u ∘ Fin.succAbove z) := by
  have he' : ∀ j, e j = Fin.succ j := fun j => Fin.ext (by rw [he, Fin.val_succ])
  have hz' : z = 0 := Fin.ext (by rw [hz, Fin.val_zero])
  simp only [he', hz']
  rw [Fin.sum_univ_succ] at hX
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib] at hX
  rw [← sub_eq_add_neg, sub_eq_zero] at hX
  exact hX.symm

theorem cocycle_split (n : ℕ) (Xv : (Fin (n + 1) → ι) → M) (u : Fin (n + 2) → ι)
    (hX : ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Xv (u ∘ Fin.succAbove i) = 0)
    (c d : ℕ) (hcd : c + d = n + 2) (e₁ : Fin c → Fin (n + 2)) (he₁ : ∀ i, (e₁ i : ℕ) = i)
    (e₂ : Fin d → Fin (n + 2)) (he₂ : ∀ j, (e₂ j : ℕ) = c + j) :
    ∑ i : Fin c, ((-1 : ℤ) ^ (i : ℕ)) • Xv (u ∘ Fin.succAbove (e₁ i))
      + ((-1 : ℤ) ^ c) • ∑ j : Fin d, ((-1 : ℤ) ^ (j : ℕ)) • Xv (u ∘ Fin.succAbove (e₂ j)) = 0 := by
  have he₁' : ∀ i, e₁ i = ⟨i, by omega⟩ := fun i => Fin.ext (by rw [he₁])
  have he₂' : ∀ j, e₂ j = ⟨c + j, by omega⟩ := fun j => Fin.ext (by rw [he₂])
  simp only [he₁', he₂']
  rw [sum_fin_split c d (n + 2) hcd] at hX
  simp only [Fin.val_mk, pow_add, ← smul_smul] at hX
  rw [Finset.smul_sum]
  exact hX

end Comb

section SlotAlgebra

variable {ι S : Type*} [Fintype ι] [CommRing S]

theorem sum_smul_smul_mul_const (c : ℤ) (f : ι → ℤ) (x : ι → S) (y : S) :
    ∑ i, f i • (c • (x i * y)) = c • ((∑ i, f i • x i) * y) := by
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, smul_comm]

theorem sum_smul_smul_const_mul (c : ℤ) (f : ι → ℤ) (y : S) (x : ι → S) :
    ∑ i, f i • (c • (y * x i)) = c • (y * ∑ i, f i • x i) := by
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_comm]

theorem sum_negpow_add_smul_smul_const_mul (n a : ℕ) (c : ℤ) (y : S) (x : Fin n → S) :
    ∑ j : Fin n, ((-1 : ℤ) ^ (a + (j : ℕ))) • (c • (y * x j))
      = (c * (-1 : ℤ) ^ a) • (y * ∑ j : Fin n, ((-1 : ℤ) ^ (j : ℕ)) • x j) := by
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, mul_smul_comm, smul_smul, smul_smul, mul_assoc]
  congr 1
  ring

theorem negpow_sq (a : ℕ) : ((-1 : S) ^ a) * ((-1 : S) ^ a) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

end SlotAlgebra

section DHK

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
  (𝔄 𝔅 ℭ : Z.OrderedOpenFamily)

theorem dHK_apply (r m : ℕ) (c : IterCech.C F 𝔄 𝔅 ℭ r m) (K : ℭ.Idx (r + 1)) (pq : DoubleComplex.Diag m)
    (st : 𝔄.Idx pq.1.1 × (𝔅.restr (ℭ.inter K)).Idx pq.1.2) :
    IterCech.dH F 𝔄 𝔅 ℭ r m c K pq st
      = ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          F.res (inf_le_inf_left _ (𝔅.restr_inter_mono (ℭ.inter_le_inter_face K j) st.2)) (c (ℭ.face K j) pq st) := by
  rw [IterCech.dH_apply, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, IterCech.resTot_apply]

end DHK

section Main

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
  (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
  (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
  (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι, (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)

section Eval

variable (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (β : (unit πY).cochain 𝔙 q)

theorem res_ent_A (r a b : ℕ) {m' : ℕ} (hab : a + b = m') (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) {W : (pullback πX πY).Opens}
    (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx a) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr W).Idx b)
    (O : (pullback πX πY).Opens) (hO : O ≤ OO πX πY 𝔘 𝔙 haff hcov K s t) (hA : r + a + 1 = p) (hq : b = q) :
    (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res hO (ent πX πY 𝔘 𝔙 haff hcov p q α β r m' K ⟨(a, b), hab⟩ (s, t))
      = ((-1 : ℤ) ^ r) • (avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) r a p hA K.1 s.1) O
          * avalD (pullback.snd πX πY) 𝔙 q β (tupT b q hq t.1) O) := by
  unfold ent
  dsimp only
  rw [dif_pos (show r + a + 1 = p ∧ b = q from ⟨hA, hq⟩)]
  show ((pullback πX πY).presheaf.map (homOfLE hO).op).hom
      (((-1 : ℤ) ^ r) • (aval (pullback.fst πX πY) 𝔘 p α _ _ _ * aval (pullback.snd πX πY) 𝔙 q β _ _ _)) = _
  rw [map_zsmul, map_mul, map_aval, map_aval, ← avalD_eq, ← avalD_eq]

theorem res_ent_B (r a b : ℕ) {m' : ℕ} (hab : a + b = m') (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) {W : (pullback πX πY).Opens}
    (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx a) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr W).Idx b)
    (O : (pullback πX πY).Opens) (hO : O ≤ OO πX πY 𝔘 𝔙 haff hcov K s t) (hB : p ≤ r) (ha : a = 0) (hb : r + b + 1 = p + q) :
    (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res hO (ent πX πY 𝔘 𝔙 haff hcov p q α β r m' K ⟨(a, b), hab⟩ (s, t))
      = ((-1 : ℤ) ^ r) • (avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) r p hB K.1) O
          * avalD (pullback.snd πX πY) 𝔙 q β (tupB (fun ij => (ofLex ij).2) r b p q hB hb K.1 t.1) O) := by
  unfold ent
  dsimp only
  rw [dif_neg (show ¬ (r + a + 1 = p ∧ b = q) by omega),
    dif_pos (show p ≤ r ∧ a = 0 ∧ r + b + 1 = p + q from ⟨hB, ha, hb⟩)]
  show ((pullback πX πY).presheaf.map (homOfLE hO).op).hom
      (((-1 : ℤ) ^ r) • (aval (pullback.fst πX πY) 𝔘 p α _ _ _ * aval (pullback.snd πX πY) 𝔙 q β _ _ _)) = _
  rw [map_zsmul, map_mul, map_aval, map_aval, ← avalD_eq, ← avalD_eq]

theorem res_ent_zero (r a b : ℕ) {m' : ℕ} (hab : a + b = m') (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) {W : (pullback πX πY).Opens}
    (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx a) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr W).Idx b)
    (O : (pullback πX πY).Opens) (hO : O ≤ OO πX πY 𝔘 𝔙 haff hcov K s t)
    (hnA : ¬ (r + a + 1 = p ∧ b = q)) (hnB : ¬ (p ≤ r ∧ a = 0 ∧ r + b + 1 = p + q)) :
    (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res hO (ent πX πY 𝔘 𝔙 haff hcov p q α β r m' K ⟨(a, b), hab⟩ (s, t)) = 0 := by
  unfold ent
  dsimp only
  rw [dif_neg hnA, dif_neg hnB, map_zero]

theorem res_box {r : ℕ} (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx p) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx q)
    (h : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t) :
    (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res h (show (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).obj ((𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t) from
      (((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
          (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (s.1 j))).symm))).op).hom
        (((pullback.fst πX πY).app (𝔘.inter s)).hom (α s)) *
      ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
          (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (t.1 j))).symm))).op).hom
        (((pullback.snd πX πY).app (𝔙.inter t)).hom (β t))))
      = avalD (pullback.fst πX πY) 𝔘 p α s.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) * avalD (pullback.snd πX πY) 𝔙 q β t.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) := by
  show ((pullback πX πY).presheaf.map (homOfLE h).op).hom (_ * _) = _
  rw [map_mul]
  erw [map_map_app_eq_aval (pullback.fst πX πY) 𝔘, map_map_app_eq_aval (pullback.snd πX πY) 𝔙]
  rw [← avalD_eq, ← avalD_eq]

theorem res_cup {n : ℕ} (hn : p + q = n) (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx n) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx 0)
    (h : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).inter K) :
    (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res h
      ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) p q n hn
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘 (fun ij => (ofLex ij).1) (fun ij => inf_le_left) p α)
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙 (fun ij => (ofLex ij).2) (fun ij => inf_le_right) q β) K)
      = avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) n p (by omega) K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupKB (fun ij => (ofLex ij).2) n p q hn K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t) := by
  rw [OModulePresheaf.cup_apply, OModulePresheaf.res_smul, OModulePresheaf.res_res, OModulePresheaf.unit_smul,
    OModulePresheaf.unit_res_apply, unitPullback_eq_aval, unitPullback_eq_aval, map_aval, map_aval, map_aval,
    ← avalD_eq, ← avalD_eq]
  rfl

end Eval

section Slots

theorem slot_VERT_A (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (β : (unit πY).cochain 𝔙 q)
    (hβ : (unit πY).d 𝔙 q β = 0) (r a : ℕ) (hA : r + a + 1 = p)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx a) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (q + 1)) :
    ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ r) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) r a p hA K.1 s.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupT q q rfl (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) (OO πX πY 𝔘 𝔙 haff hcov K s t))) = 0 := by
  have hO : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (pullback.snd πX πY) ⁻¹ᵁ 𝔙.ointer t.1 :=
    le_preimage_ointer _ 𝔙 _ _ fun j => OO_le_snd πX πY 𝔘 𝔙 haff hcov K s t j
  have key := congrArg (fun z => ((-1 : ℤ) ^ r) • (avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) r a p hA K.1 s.1) (OO πX πY 𝔘 𝔙 haff hcov K s t) * z))
    (sum_avalD_oface (pullback.snd πX πY) 𝔙 q β hβ t.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) hO)
  dsimp only at key
  rw [mul_zero, smul_zero, Finset.mul_sum, Finset.smul_sum] at key
  simp only [tupT_self, Scheme.OrderedOpenFamily.face_val]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans key
  rw [mul_smul_comm]
  exact smul_comm _ _ _

theorem slot_HOR_B (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (β : (unit πY).cochain 𝔙 q)
    (r b : ℕ) (hB : p ≤ r) (hb : r + b + 1 = p + q)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx r) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 1) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx b) :
    ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ r) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) r p hB K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupB (fun ij => (ofLex ij).2) r b p q hB hb K.1 t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t))) = 0 := by
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, add_neg_cancel]

theorem slot_TOP_A (a q : ℕ) (α : (unit πX).cochain 𝔘 (a + 1)) (hα : (unit πX).d 𝔘 (a + 1) α = 0)
    (β : (unit πY).cochain 𝔙 q)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx 0) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx (a + 1)) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx q) :
    ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ 0) •
      (avalD (pullback.fst πX πY) 𝔘 (a + 1) α (tupA (fun ij => (ofLex ij).1) 0 a (a + 1) (by omega) K.1 ((𝔘.preimageFamily (pullback.fst πX πY)).face s j).1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupT q q rfl t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
      = avalD (pullback.fst πX πY) 𝔘 (a + 1) α s.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) * avalD (pullback.snd πX πY) 𝔙 q β t.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) := by
  classical
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set u := tupA (fun ij => (ofLex ij).1) 0 (a + 1) (a + 2) (by omega) K.1 s.1 with hudef
  have hu := sum_avalD_oface (pullback.fst πX πY) 𝔘 (a + 1) α hα u O
    (le_tupA πX πY 𝔘 𝔙 haff hcov K s t (a + 2) (by omega))
  have h1 : ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) • avalD (pullback.fst πX πY) 𝔘 (a + 1) α (u ∘ Fin.succAbove j.succ) O
      = avalD (pullback.fst πX πY) 𝔘 (a + 1) α (u ∘ Fin.succAbove 0) O :=
    cocycle_first (a + 1) (fun v => avalD (pullback.fst πX πY) 𝔘 (a + 1) α v O) u hu Fin.succ (fun j => by simp)
      0 rfl
  have hface0 : u ∘ Fin.succAbove (0 : Fin (a + 3)) = s.1 := by
    funext j
    simp only [hudef, Function.comp_apply, Fin.succAbove_zero, tupA]
    rw [dif_neg (by simp [Fin.val_succ])]
    exact congrArg s.1 (Fin.ext (by simp [Fin.val_succ]))
  have e0 : avalD (pullback.fst πX πY) 𝔘 (a + 1) α (u ∘ Fin.succAbove 0) O
      = avalD (pullback.fst πX πY) 𝔘 (a + 1) α s.1 O := congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 (a + 1) α v O) hface0
  have ej : ∀ j : Fin (a + 2),
      avalD (pullback.fst πX πY) 𝔘 (a + 1) α (tupA (fun ij => (ofLex ij).1) 0 a (a + 1) (by omega) K.1
        ((𝔘.preimageFamily (pullback.fst πX πY)).face s j).1) O
        = avalD (pullback.fst πX πY) 𝔘 (a + 1) α (u ∘ Fin.succAbove j.succ) O :=
    fun j => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 (a + 1) α v O)
      (tupA_face_s (fun ij => (ofLex ij).1) 0 a (a + 1) (by omega) K.1 s.1 j j.succ (by simp only [Fin.val_succ]; omega))
  have hT : avalD (pullback.snd πX πY) 𝔙 q β (tupT q q rfl t.1) O = avalD (pullback.snd πX πY) 𝔙 q β t.1 O :=
    congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 q β v O) (tupT_self q rfl t.1)
  simp only [ej, hT]
  rw [sum_smul_smul_mul_const, h1, e0, pow_zero, one_smul]

theorem slot_TOP_B (b : ℕ) (α : (unit πX).cochain 𝔘 0) (hα : (unit πX).d 𝔘 0 α = 0)
    (β : (unit πY).cochain 𝔙 (b + 1)) (hβ : (unit πY).d 𝔙 (b + 1) β = 0)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx 0) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b + 1)) :
    ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ 0) •
      (avalD (pullback.fst πX πY) 𝔘 0 α (tupK (fun ij => (ofLex ij).1) 0 0 le_rfl K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupB (fun ij => (ofLex ij).2) 0 b 0 (b + 1) le_rfl (by omega) K.1
            (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
      = avalD (pullback.fst πX πY) 𝔘 0 α s.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) * avalD (pullback.snd πX πY) 𝔙 (b + 1) β t.1 (OO πX πY 𝔘 𝔙 haff hcov K s t) := by
  classical
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set w := tupB (fun ij => (ofLex ij).2) 0 (b + 1) 0 (b + 2) le_rfl (by omega) K.1 t.1 with hwdef
  have hs : O ≤ (pullback.fst πX πY) ⁻¹ᵁ 𝔘.ointer s.1 :=
    le_preimage_ointer _ 𝔘 _ _ fun j => OO_le_fst πX πY 𝔘 𝔙 haff hcov K s t j
  have hA : avalD (pullback.fst πX πY) 𝔘 0 α (tupK (fun ij => (ofLex ij).1) 0 0 le_rfl K.1) O
      = avalD (pullback.fst πX πY) 𝔘 0 α s.1 O :=
    avalD_zero_eq _ 𝔘 α hα _ _ _ (le_tupK πX πY 𝔘 𝔙 haff hcov K s t 0 le_rfl) hs
  have hw := sum_avalD_oface (pullback.snd πX πY) 𝔙 (b + 1) β hβ w O
    (le_tupB πX πY 𝔘 𝔙 haff hcov K s t 0 (b + 2) le_rfl (by omega))
  have h1 : ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) • avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove j.succ) O
      = avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove 0) O :=
    cocycle_first (b + 1) (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O) w hw Fin.succ (fun j => by simp)
      0 rfl
  have e0 : avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove 0) O
      = avalD (pullback.snd πX πY) 𝔙 (b + 1) β t.1 O :=
    congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_self_face_zero (fun ij => (ofLex ij).2) (b + 1) 0 K.1 t.1 0 rfl)
  have ej : ∀ j : Fin (b + 2),
      avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupB (fun ij => (ofLex ij).2) 0 b 0 (b + 1) le_rfl (by omega) K.1
        (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) O
        = avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove j.succ) O :=
    fun j => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_face_t (fun ij => (ofLex ij).2) 0 b 0 (b + 1) le_rfl (by omega) K.1 t.1 j j.succ
        (by simp only [Fin.val_succ]; omega))
  simp only [ej, hA]
  rw [sum_smul_smul_const_mul, h1, e0, pow_zero, one_smul]

theorem slot_INT_A (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (hα : (unit πX).d 𝔘 p α = 0)
    (β : (unit πY).cochain 𝔙 q) (r a : ℕ) (hA : r + 1 + a + 1 = p)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (r + 1)) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx (a + 1)) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx q) :
    ∑ l : Fin (r + 2), ((-1 : ℤ) ^ (l : ℕ)) • (((-1 : ℤ) ^ r) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) r (a + 1) p (by omega) (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1 s.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupT q q rfl t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
    + ((-1 : ℤ) ^ (r + 1)) • ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (r + 1)) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) (r + 1) a p hA K.1 ((𝔘.preimageFamily (pullback.fst πX πY)).face s j).1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupT q q rfl t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t))) = 0 := by
  classical
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set u := tupA (fun ij => (ofLex ij).1) (r + 1) (a + 1) (p + 1) (by omega) K.1 s.1 with hudef
  have hu := sum_avalD_oface (pullback.fst πX πY) 𝔘 p α hα u O (le_tupA πX πY 𝔘 𝔙 haff hcov K s t (p + 1) (by omega))
  have hsplit : ∑ l : Fin (r + 2), ((-1 : ℤ) ^ (l : ℕ)) • avalD (pullback.fst πX πY) 𝔘 p α (u ∘ Fin.succAbove (Fin.castLE (by omega) l)) O
      + ((-1 : ℤ) ^ (r + 2)) • ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) • avalD (pullback.fst πX πY) 𝔘 p α (u ∘ Fin.succAbove ⟨r + 2 + j, by omega⟩) O = 0 :=
    cocycle_split p (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O) u hu (r + 2) (a + 2) (by omega)
      (fun l => Fin.castLE (by omega) l) (fun l => rfl) (fun j => ⟨r + 2 + j, by omega⟩) (fun j => rfl)
  have e1 : ∀ l : Fin (r + 2), avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) r (a + 1) p (by omega) (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1 s.1) O
      = avalD (pullback.fst πX πY) 𝔘 p α (u ∘ Fin.succAbove (Fin.castLE (by omega) l)) O :=
    fun l => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupA_face_K (fun ij => (ofLex ij).1) r (a + 1) p (by omega) K.1 s.1 l (Fin.castLE (by omega) l) rfl)
  have e2 : ∀ j : Fin (a + 2), avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) (r + 1) a p hA K.1 ((𝔘.preimageFamily (pullback.fst πX πY)).face s j).1) O
      = avalD (pullback.fst πX πY) 𝔘 p α (u ∘ Fin.succAbove ⟨r + 2 + j, by omega⟩) O :=
    fun j => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupA_face_s (fun ij => (ofLex ij).1) (r + 1) a p (by omega) K.1 s.1 j ⟨r + 2 + j, by omega⟩
        (by show r + 2 + (j : ℕ) = r + 1 + 1 + j; omega))
  have hT : avalD (pullback.snd πX πY) 𝔙 q β (tupT q q rfl t.1) O = avalD (pullback.snd πX πY) 𝔙 q β t.1 O :=
    congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 q β v O) (tupT_self q rfl t.1)
  simp only [e1, e2, hT]
  rw [sum_smul_smul_mul_const, sum_smul_smul_mul_const, smul_smul, ← pow_add,
    (show Even (r + 1 + (r + 1)) from ⟨r + 1, rfl⟩).neg_one_pow, one_smul,
    eq_neg_of_add_eq_zero_left hsplit, neg_mul, smul_neg, smul_mul_assoc, smul_smul, ← pow_add,
    (show Even (r + (r + 2)) from ⟨r + 1, by omega⟩).neg_one_pow, one_smul, neg_add_cancel]

theorem slot_INT_AB (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (hα : (unit πX).d 𝔘 p α = 0)
    (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0) (r b : ℕ) (hA : r + 0 + 1 = p) (hB : p ≤ r + 1)
    (hb : r + 1 + b + 1 = p + q)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (r + 1)) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b + 1)) :
    ∑ l : Fin (r + 2), ((-1 : ℤ) ^ (l : ℕ)) • (((-1 : ℤ) ^ r) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupA (fun ij => (ofLex ij).1) r 0 p hA (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1 s.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupT (b + 1) q (by omega) t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
    + ((-1 : ℤ) ^ (r + 1)) • ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (r + 1)) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (r + 1) p hB K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupB (fun ij => (ofLex ij).2) (r + 1) b p q hB (by omega) K.1
            (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) (OO πX πY 𝔘 𝔙 haff hcov K s t))) = 0 := by
  classical
  obtain rfl : p = r + 1 := by omega
  obtain rfl : q = b + 1 := by omega
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set U := tupA (fun ij => (ofLex ij).1) (r + 1) 0 (r + 2) (by omega) K.1 s.1 with hUdef
  set V := tupB (fun ij => (ofLex ij).2) (r + 1) (b + 1) (r + 1) (b + 2) hB (by omega) K.1 t.1 with hVdef
  set AK := avalD (pullback.fst πX πY) 𝔘 (r + 1) α (tupK (fun ij => (ofLex ij).1) (r + 1) (r + 1) hB K.1) O with hAKdef

  have hu := sum_avalD_oface (pullback.fst πX πY) 𝔘 (r + 1) α hα U O
    (le_tupA πX πY 𝔘 𝔙 haff hcov K s t (r + 2) (by omega))
  have h1 : ∑ l : Fin (r + 2), ((-1 : ℤ) ^ (l : ℕ)) •
        avalD (pullback.fst πX πY) 𝔘 (r + 1) α (U ∘ Fin.succAbove (Fin.castSucc l)) O
      = ((-1 : ℤ) ^ (r + 1)) • avalD (pullback.fst πX πY) 𝔘 (r + 1) α (U ∘ Fin.succAbove (Fin.last (r + 2))) O :=
    cocycle_last (r + 1) (fun v => avalD (pullback.fst πX πY) 𝔘 (r + 1) α v O) U hu Fin.castSucc (fun l => by simp)
      (Fin.last (r + 2)) (by simp)
  have eL : avalD (pullback.fst πX πY) 𝔘 (r + 1) α (U ∘ Fin.succAbove (Fin.last (r + 2))) O = AK :=
    congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 (r + 1) α v O)
      (tupA_zero_face_last (fun ij => (ofLex ij).1) (r + 1) K.1 s.1 (Fin.last (r + 2)) (by simp))
  have ej : ∀ l : Fin (r + 2),
      avalD (pullback.fst πX πY) 𝔘 (r + 1) α (tupA (fun ij => (ofLex ij).1) r 0 (r + 1) hA
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1) s.1) O
        = avalD (pullback.fst πX πY) 𝔘 (r + 1) α (U ∘ Fin.succAbove (Fin.castSucc l)) O :=
    fun l => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 (r + 1) α v O)
      (tupA_face_K (fun ij => (ofLex ij).1) r 0 (r + 1) (by omega) K.1 s.1 l (Fin.castSucc l) (by simp))
  have hT : avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupT (b + 1) (b + 1) (by omega) t.1) O
      = avalD (pullback.snd πX πY) 𝔙 (b + 1) β t.1 O :=
    congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O) (tupT_self (b + 1) (by omega) t.1)

  have hv := sum_avalD_oface (pullback.snd πX πY) 𝔙 (b + 1) β hβ V O
    (le_tupB πX πY 𝔘 𝔙 haff hcov K s t (r + 1) (b + 2) hB (by omega))
  have h2 : ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        avalD (pullback.snd πX πY) 𝔙 (b + 1) β (V ∘ Fin.succAbove j.succ) O
      = avalD (pullback.snd πX πY) 𝔙 (b + 1) β (V ∘ Fin.succAbove 0) O :=
    cocycle_first (b + 1) (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O) V hv Fin.succ (fun j => by simp)
      0 rfl
  have e0 : avalD (pullback.snd πX πY) 𝔙 (b + 1) β (V ∘ Fin.succAbove 0) O
      = avalD (pullback.snd πX πY) 𝔙 (b + 1) β t.1 O :=
    congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_self_face_zero (fun ij => (ofLex ij).2) (b + 1) (r + 1) K.1 t.1 0 rfl)
  have ej2 : ∀ j : Fin (b + 2),
      avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupB (fun ij => (ofLex ij).2) (r + 1) b (r + 1) (b + 1) hB (by omega) K.1
        (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) O
        = avalD (pullback.snd πX πY) 𝔙 (b + 1) β (V ∘ Fin.succAbove j.succ) O :=
    fun j => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_face_t (fun ij => (ofLex ij).2) (r + 1) b (r + 1) (b + 1) hB (by omega) K.1 t.1 j j.succ
        (by simp only [Fin.val_succ]; omega))
  simp only [ej, hT, ej2]
  rw [sum_smul_smul_mul_const, h1, eL, sum_smul_smul_const_mul, h2, e0, smul_mul_assoc, smul_smul, smul_smul,
    ← add_smul, show ((-1 : ℤ) ^ r * (-1) ^ (r + 1) + (-1) ^ (r + 1) * (-1) ^ (r + 1)) = 0 from by ring, zero_smul]

theorem slot_INT_B (p q : ℕ) (α : (unit πX).cochain 𝔘 p) (hα : (unit πX).d 𝔘 p α = 0)
    (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0) (r b : ℕ) (hB : p ≤ r)
    (hb : r + (b + 1) + 1 = p + q) (hB' : p ≤ r + 1) (hb' : r + 1 + b + 1 = p + q)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (r + 1)) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b + 1)) :
    ∑ l : Fin (r + 2), ((-1 : ℤ) ^ (l : ℕ)) • (((-1 : ℤ) ^ r) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) r p hB (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupB (fun ij => (ofLex ij).2) r (b + 1) p q hB hb (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1 t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
    + ((-1 : ℤ) ^ (r + 1)) • ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (r + 1)) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (r + 1) p hB' K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 q β (tupB (fun ij => (ofLex ij).2) (r + 1) b p q hB' hb' K.1
            (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) (OO πX πY 𝔘 𝔙 haff hcov K s t))) = 0 := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, r = p + d := ⟨r - p, by omega⟩
  obtain rfl : q = d + b + 2 := by omega
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set W := tupK (fun ij => (ofLex ij).1) (p + d + 1) (p + 1) (by omega) K.1 with hWdef
  set V := tupB (fun ij => (ofLex ij).2) (p + d + 1) (b + 1) p (d + b + 2 + 1) hB' (by omega) K.1 t.1 with hVdef
  set AK := avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (p + d + 1) p hB' K.1) O with hAKdef
  have hle : d + 2 ≤ d + b + 2 + 2 := by omega

  have hW := sum_avalD_oface (pullback.fst πX πY) 𝔘 p α hα W O
    (le_tupK πX πY 𝔘 𝔙 haff hcov K s t (p + 1) (by omega))
  have hα1 : ∑ l : Fin (p + 1), ((-1 : ℤ) ^ (l : ℕ)) •
        avalD (pullback.fst πX πY) 𝔘 p α (W ∘ Fin.succAbove (Fin.castSucc l)) O = ((-1 : ℤ) ^ p) • AK := by
    refine (cocycle_last p (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O) W hW Fin.castSucc (fun l => by simp)
      (Fin.last (p + 1)) (by simp)).trans ?_
    exact (congrArg _ (congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupK_eq_face_last (fun ij => (ofLex ij).1) (p + d + 1) p hB' (by omega) K.1 (Fin.last (p + 1)) (by simp)))).symm

  have hV := sum_avalD_oface (pullback.snd πX πY) 𝔙 (d + b + 2) β hβ V O
    (le_tupB πX πY 𝔘 𝔙 haff hcov K s t p (d + b + 2 + 1) hB' (by omega))
  have hβ0 := cocycle_split (d + b + 2) (fun v => avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β v O) V hV (d + 2) (b + 2)
    (by omega) (fun i => Fin.castLE hle i) (fun i => by simp) (fun j => ⟨d + 2 + j, by omega⟩) (fun j => rfl)
  have hβ1 : avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (V ∘ Fin.succAbove (Fin.castLE hle 0)) O
      + -(∑ i : Fin (d + 1), ((-1 : ℤ) ^ (i : ℕ)) •
          avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (V ∘ Fin.succAbove (Fin.castLE hle i.succ)) O)
      + ((-1 : ℤ) ^ d) • ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (V ∘ Fin.succAbove (⟨d + 2 + j, by omega⟩ : Fin (d + b + 2 + 2))) O = 0 := by
    have e := hβ0
    rw [Fin.sum_univ_succ] at e
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      Finset.sum_neg_distrib, neg_neg] at e
    exact e

  have hb1 : ∀ l : Fin (p + 1),
      avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (p + d) p hB
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨l, by omega⟩).1)) O
        = avalD (pullback.fst πX πY) 𝔘 p α (W ∘ Fin.succAbove (Fin.castSucc l)) O :=
    fun l => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupK_face_le (fun ij => (ofLex ij).1) (p + d) p hB (by omega) K.1 ⟨l, by omega⟩ (Fin.castSucc l)
        (by simp only [Fin.val_castSucc, Fin.val_mk]))
  have hb1' : ∀ l : Fin (p + 1),
      avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (tupB (fun ij => (ofLex ij).2) (p + d) (b + 1) p (d + b + 2) hB hb
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨l, by omega⟩).1) t.1) O
        = avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (V ∘ Fin.succAbove (Fin.castLE hle 0)) O :=
    fun l => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β v O)
      (tupB_face_K_le (fun ij => (ofLex ij).2) (p + d) (b + 1) p (d + b + 2) hB hb K.1 t.1 ⟨l, by omega⟩
        (by simp only [Fin.val_mk]; omega) (Fin.castLE hle 0) (by simp))
  have hb2 : ∀ j : Fin (d + 1),
      avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (p + d) p hB
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨p + 1 + j, by omega⟩).1)) O
        = AK :=
    fun j => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupK_face_gt (fun ij => (ofLex ij).1) (p + d) p hB (by omega) K.1 ⟨p + 1 + j, by omega⟩
        (by simp only [Fin.val_mk]; omega))
  have hb2' : ∀ j : Fin (d + 1),
      avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (tupB (fun ij => (ofLex ij).2) (p + d) (b + 1) p (d + b + 2) hB hb
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨p + 1 + j, by omega⟩).1) t.1) O
        = avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (V ∘ Fin.succAbove (Fin.castLE hle j.succ)) O :=
    fun j => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β v O)
      (tupB_face_K_ge (fun ij => (ofLex ij).2) (p + d) (b + 1) p (d + b + 2) hB hb K.1 t.1 ⟨p + 1 + j, by omega⟩
        (by simp only [Fin.val_mk]; omega) (Fin.castLE hle j.succ)
        (by simp only [Fin.coe_castLE, Fin.val_succ, Fin.val_mk]; omega))
  have hb3 : ∀ j : Fin (b + 2),
      avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (tupB (fun ij => (ofLex ij).2) (p + d + 1) b p (d + b + 2) hB' hb' K.1
        (((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).face t j).1) O
        = avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β (V ∘ Fin.succAbove (⟨d + 2 + j, by omega⟩ : Fin (d + b + 2 + 2))) O :=
    fun j => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (d + b + 2) β v O)
      (tupB_face_t (fun ij => (ofLex ij).2) (p + d + 1) b p (d + b + 2) hB' hb' K.1 t.1 j ⟨d + 2 + j, by omega⟩
        (by simp only [Fin.val_mk]; omega))

  rw [sum_fin_split (p + 1) (d + 1) (p + d + 2) (by omega)]
  simp only [Fin.val_mk, hb1, hb1', hb2, hb2', hb3]
  rw [sum_smul_smul_mul_const, hα1, sum_negpow_add_smul_smul_const_mul, sum_smul_smul_const_mul]

  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at hβ1 ⊢
  linear_combination ((-1 : Γ(pullback πX πY, O)) ^ p * (-1 : Γ(pullback πX πY, O)) ^ p *
    (-1 : Γ(pullback πX πY, O)) ^ d * AK) * hβ1

theorem slot_BOT_A (m : ℕ) (α : (unit πX).cochain 𝔘 (m + 1)) (hα : (unit πX).d 𝔘 (m + 1) α = 0)
    (β : (unit πY).cochain 𝔙 0) (hβ : (unit πY).d 𝔙 0 β = 0)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (m + 1)) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx 0) :
    ∑ l : Fin (m + 2), ((-1 : ℤ) ^ (l : ℕ)) • (((-1 : ℤ) ^ m) •
      (avalD (pullback.fst πX πY) 𝔘 (m + 1) α (tupA (fun ij => (ofLex ij).1) m 0 (m + 1) (by omega) (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1 s.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 0 β (tupT 0 0 rfl t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
      = -(avalD (pullback.fst πX πY) 𝔘 (m + 1) α (tupK (fun ij => (ofLex ij).1) (m + 1) (m + 1) le_rfl K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
          * avalD (pullback.snd πX πY) 𝔙 0 β (tupKB (fun ij => (ofLex ij).2) (m + 1) (m + 1) 0 rfl K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)) := by
  classical
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set u := tupA (fun ij => (ofLex ij).1) (m + 1) 0 (m + 2) (by omega) K.1 s.1 with hudef
  have hu := sum_avalD_oface (pullback.fst πX πY) 𝔘 (m + 1) α hα u O
    (le_tupA πX πY 𝔘 𝔙 haff hcov K s t (m + 2) (by omega))
  have h1 : ∑ l : Fin (m + 2), ((-1 : ℤ) ^ (l : ℕ)) •
        avalD (pullback.fst πX πY) 𝔘 (m + 1) α (u ∘ Fin.succAbove (Fin.castSucc l)) O
      = ((-1 : ℤ) ^ (m + 1)) • avalD (pullback.fst πX πY) 𝔘 (m + 1) α (u ∘ Fin.succAbove (Fin.last (m + 2))) O :=
    cocycle_last (m + 1) (fun v => avalD (pullback.fst πX πY) 𝔘 (m + 1) α v O) u hu Fin.castSucc (fun l => by simp)
      (Fin.last (m + 2)) (by simp)
  have eL : avalD (pullback.fst πX πY) 𝔘 (m + 1) α (u ∘ Fin.succAbove (Fin.last (m + 2))) O
      = avalD (pullback.fst πX πY) 𝔘 (m + 1) α (tupK (fun ij => (ofLex ij).1) (m + 1) (m + 1) le_rfl K.1) O :=
    congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 (m + 1) α v O)
      (tupA_zero_face_last (fun ij => (ofLex ij).1) (m + 1) K.1 s.1 (Fin.last (m + 2)) (by simp))
  have ej : ∀ l : Fin (m + 2),
      avalD (pullback.fst πX πY) 𝔘 (m + 1) α (tupA (fun ij => (ofLex ij).1) m 0 (m + 1) (by omega)
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1) s.1) O
        = avalD (pullback.fst πX πY) 𝔘 (m + 1) α (u ∘ Fin.succAbove (Fin.castSucc l)) O :=
    fun l => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 (m + 1) α v O)
      (tupA_face_K (fun ij => (ofLex ij).1) m 0 (m + 1) (by omega) K.1 s.1 l (Fin.castSucc l) (by simp))
  have hT : avalD (pullback.snd πX πY) 𝔙 0 β (tupT 0 0 rfl t.1) O
      = avalD (pullback.snd πX πY) 𝔙 0 β (tupKB (fun ij => (ofLex ij).2) (m + 1) (m + 1) 0 rfl K.1) O := by
    refine (congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 0 β v O) (tupT_self 0 rfl t.1)).trans ?_
    exact avalD_zero_eq _ 𝔙 β hβ _ _ _
      (le_preimage_ointer _ 𝔙 _ _ fun j => OO_le_snd πX πY 𝔘 𝔙 haff hcov K s t j)
      (le_preimage_ointer _ 𝔙 _ _ fun j => OO_le_K_snd πX πY 𝔘 𝔙 haff hcov K s t ⟨m + 1 + j, by omega⟩)
  simp only [ej, hT]
  rw [sum_smul_smul_mul_const, h1, eL, smul_mul_assoc, smul_smul, ← pow_add,
    show m + (m + 1) = 2 * m + 1 from by ring, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_smul, one_smul]

theorem slot_BOT_B (p b m : ℕ) (h : p + (b + 1) = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 (b + 1)) (hβ : (unit πY).d 𝔙 (b + 1) β = 0)
    (hB : p ≤ m) (hb : m + 0 + 1 = p + (b + 1))
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (m + 1)) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx 0) :
    ∑ l : Fin (m + 2), ((-1 : ℤ) ^ (l : ℕ)) • (((-1 : ℤ) ^ m) •
      (avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) m p hB (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
        * avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupB (fun ij => (ofLex ij).2) m 0 p (b + 1) hB hb (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K l).1 t.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)))
      = -(avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (m + 1) p (by omega) K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
          * avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupKB (fun ij => (ofLex ij).2) (m + 1) p (b + 1) h K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)) := by
  classical
  have hb' : m = p + b := by omega
  set O := OO πX πY 𝔘 𝔙 haff hcov K s t with hOdef
  set uK := tupK (fun ij => (ofLex ij).1) (m + 1) (p + 1) (by omega) K.1 with huKdef
  set w := tupB (fun ij => (ofLex ij).2) (m + 1) 0 p (b + 2) (by omega) (by omega) K.1 t.1 with hwdef
  set AK := avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (m + 1) p (by omega) K.1) O with hAKdef
  set BK := avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupKB (fun ij => (ofLex ij).2) (m + 1) p (b + 1) h K.1) O with hBKdef

  have hcu := sum_avalD_oface (pullback.fst πX πY) 𝔘 p α hα uK O
    (le_tupK πX πY 𝔘 𝔙 haff hcov K s t (p + 1) (by omega))
  have hα1 : ∑ l : Fin (p + 1), ((-1 : ℤ) ^ (l : ℕ)) •
        avalD (pullback.fst πX πY) 𝔘 p α (uK ∘ Fin.succAbove (Fin.castSucc l)) O = ((-1 : ℤ) ^ p) • AK := by
    refine (cocycle_last p (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O) uK hcu Fin.castSucc (fun l => by simp)
      (Fin.last (p + 1)) (by simp)).trans ?_
    exact (congrArg _ (congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupK_eq_face_last (fun ij => (ofLex ij).1) (m + 1) p (by omega) (by omega) K.1 (Fin.last (p + 1)) (by simp)))).symm

  have hcw := sum_avalD_oface (pullback.snd πX πY) 𝔙 (b + 1) β hβ w O
    (le_tupB πX πY 𝔘 𝔙 haff hcov K s t p (b + 2) (by omega) (by omega))
  have hβ0 := cocycle_split (b + 1) (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O) w hcw 1 (b + 2) (by omega)
    (fun _ => 0) (fun i => by simp) Fin.succ (fun j => by simp only [Fin.val_succ]; omega)
  have eK : avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove (Fin.last (b + 1)).succ) O = BK :=
    congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_zero_face_last (fun ij => (ofLex ij).2) (m + 1) p (b + 1) h K.1 t.1 (Fin.last (b + 1)).succ (by simp))
  have hβ1 : avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove 0) O
      = ∑ j : Fin (b + 1), ((-1 : ℤ) ^ (j : ℕ)) •
          avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove (Fin.castSucc j).succ) O
        + ((-1 : ℤ) ^ (b + 1)) • BK := by
    have e := hβ0
    rw [Fin.sum_univ_one, Fin.sum_univ_castSucc] at e
    simp only [Fin.val_zero, pow_zero, one_smul, pow_one, neg_smul, Fin.val_castSucc, Fin.val_last, eK] at e
    rw [add_neg_eq_zero] at e
    exact e

  have hb1 : ∀ l : Fin (p + 1),
      avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) m p hB
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨l, by omega⟩).1)) O
        = avalD (pullback.fst πX πY) 𝔘 p α (uK ∘ Fin.succAbove (Fin.castSucc l)) O :=
    fun l => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupK_face_le (fun ij => (ofLex ij).1) m p hB (by omega) K.1 ⟨l, by omega⟩ (Fin.castSucc l)
        (by simp only [Fin.val_castSucc, Fin.val_mk]))
  have hb1' : ∀ l : Fin (p + 1),
      avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupB (fun ij => (ofLex ij).2) m 0 p (b + 1) hB hb
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨l, by omega⟩).1) t.1) O
        = avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove 0) O :=
    fun l => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_face_K_le (fun ij => (ofLex ij).2) m 0 p (b + 1) hB hb K.1 t.1 ⟨l, by omega⟩
        (by simp only [Fin.val_mk]; omega) 0 rfl)
  have hb2 : ∀ j : Fin (b + 1),
      avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) m p hB
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨p + 1 + j, by omega⟩).1)) O
        = AK :=
    fun j => congrArg (fun v => avalD (pullback.fst πX πY) 𝔘 p α v O)
      (tupK_face_gt (fun ij => (ofLex ij).1) m p hB (by omega) K.1 ⟨p + 1 + j, by omega⟩
        (by simp only [Fin.val_mk]; omega))
  have hb2' : ∀ j : Fin (b + 1),
      avalD (pullback.snd πX πY) 𝔙 (b + 1) β (tupB (fun ij => (ofLex ij).2) m 0 p (b + 1) hB hb
        ((((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K ⟨p + 1 + j, by omega⟩).1) t.1) O
        = avalD (pullback.snd πX πY) 𝔙 (b + 1) β (w ∘ Fin.succAbove (Fin.castSucc j).succ) O :=
    fun j => congrArg (fun v => avalD (pullback.snd πX πY) 𝔙 (b + 1) β v O)
      (tupB_face_K_ge (fun ij => (ofLex ij).2) m 0 p (b + 1) hB hb K.1 t.1 ⟨p + 1 + j, by omega⟩
        (by simp only [Fin.val_mk]; omega) (Fin.castSucc j).succ
        (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]; omega))

  rw [sum_fin_split (p + 1) (b + 1) (m + 2) (by omega)]
  simp only [Fin.val_mk, hb1, hb1', hb2, hb2']
  rw [sum_smul_smul_mul_const, hα1, sum_negpow_add_smul_smul_const_mul, eq_sub_of_add_eq hβ1.symm, hb', pow_add]

  have h2p := negpow_sq (S := Γ(pullback πX πY, O)) p
  have h2b := negpow_sq (S := Γ(pullback πX πY, O)) b
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  linear_combination (-(AK * BK) * ((-1 : Γ(pullback πX πY, O)) ^ b * (-1 : Γ(pullback πX πY, O)) ^ b)) * h2p
    + (-(AK * BK)) * h2b

end Slots

section Assembly

theorem diag_ne {n : ℕ} (i j : DoubleComplex.Diag n) (h : i.1.1 ≠ j.1.1) : i ≠ j :=
  fun e => h (by rw [e])

theorem leaf_top_v (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx 0) (b' : ℕ) (hab : 0 + (b' + 1) = m + 1) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0)
    (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b' + 1)) (h0 : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t) :
    DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K))) m (ent πX πY 𝔘 𝔙 haff hcov p q α β 0 m K) ⟨(0, b' + 1), hab⟩ (s, t)
      = (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res h0 ((Pi.single ⟨(p, q), hpq⟩ (fun st : 𝔘.Idx p × 𝔙.Idx q =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q) : DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) (m + 1)) ⟨(0, b' + 1), hab⟩ (s, t)) := by
  rw [DoubleComplex.dTot_apply_zero_succ, OModulePresheaf.biCech_dV, OModulePresheaf.BiCech.dV_apply]
  dsimp only
  by_cases hp0 : p = 0
  · subst hp0
    obtain rfl : q = b' + 1 := by omega
    rw [Pi.single_eq_same, res_box]
    conv_lhs => arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov 0 (b' + 1) α β 0 0 b' _ _ _ _ _ _ le_rfl rfl (by omega)]
    exact slot_TOP_B πX πY 𝔘 𝔙 haff hcov b' α hα β hβ K s t
  · by_cases hp1 : p = 1
    · subst hp1
      obtain rfl : q = b' := by omega
      rw [Pi.single_eq_of_ne (diag_ne _ _ (by show (0 : ℕ) ≠ 1; omega))]
      erw [Pi.zero_apply]; rw [map_zero]
      conv_lhs => arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov 1 q α β 0 0 q _ _ _ _ _ _ (by omega) rfl]
      exact slot_VERT_A πX πY 𝔘 𝔙 haff hcov 1 q α β hβ 0 0 (by omega) K s t
    · rw [Pi.single_eq_of_ne (diag_ne _ _ (by show (0 : ℕ) ≠ p; omega))]
      erw [Pi.zero_apply]; rw [map_zero]
      conv_lhs => arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β 0 0 b' _ _ _ _ _ _ (by omega) (by omega)]
      simp only [smul_zero, Finset.sum_const_zero]

theorem leaf_top_h (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx 0) (a' : ℕ) (hab : a' + 1 + 0 = m + 1) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx (a' + 1))
    (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx 0) (h0 : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t) :
    DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K))) m (ent πX πY 𝔘 𝔙 haff hcov p q α β 0 m K) ⟨(a' + 1, 0), hab⟩ (s, t)
      = (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res h0 ((Pi.single ⟨(p, q), hpq⟩ (fun st : 𝔘.Idx p × 𝔙.Idx q =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q) : DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) (m + 1)) ⟨(a' + 1, 0), hab⟩ (s, t)) := by
  rw [DoubleComplex.dTot_apply_succ_zero, OModulePresheaf.biCech_dH, OModulePresheaf.BiCech.dH_apply]
  dsimp only
  by_cases hq0 : q = 0
  · subst hq0
    obtain rfl : p = a' + 1 := by omega
    rw [Pi.single_eq_same, res_box]
    conv_lhs => arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov (a' + 1) 0 α β 0 a' 0 _ _ _ _ _ _ (by omega) rfl]
    exact slot_TOP_A πX πY 𝔘 𝔙 haff hcov a' 0 α hα β K s t
  · by_cases hB : p = 0 ∧ a' = 0
    · obtain ⟨rfl, rfl⟩ := hB
      obtain rfl : q = 1 := by omega
      rw [Pi.single_eq_of_ne (diag_ne _ _ (by show (0 + 1 : ℕ) ≠ 0; omega))]
      erw [Pi.zero_apply]; rw [map_zero]
      conv_lhs => arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov 0 1 α β 0 0 0 _ _ _ _ _ _ le_rfl rfl (by omega)]
      exact slot_HOR_B πX πY 𝔘 𝔙 haff hcov 0 1 α β 0 0 le_rfl (by omega) K s t
    · rw [Pi.single_eq_of_ne (diag_ne _ _ (by show a' + 1 ≠ p; omega))]
      erw [Pi.zero_apply]; rw [map_zero]
      conv_lhs => arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β 0 a' 0 _ _ _ _ _ _ (by omega) (by omega)]
      simp only [smul_zero, Finset.sum_const_zero]

theorem leaf_top_hv (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx 0) (a' b' : ℕ) (hab : a' + 1 + (b' + 1) = m + 1) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx (a' + 1))
    (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b' + 1)) (h0 : OO πX πY 𝔘 𝔙 haff hcov K s t ≤ (𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t) :
    DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K))) m (ent πX πY 𝔘 𝔙 haff hcov p q α β 0 m K)
        ⟨(a' + 1, b' + 1), hab⟩ (s, t)
      = (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res h0 ((Pi.single ⟨(p, q), hpq⟩ (fun st : 𝔘.Idx p × 𝔙.Idx q =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q) : DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) (m + 1)) ⟨(a' + 1, b' + 1), hab⟩ (s, t)) := by
  rw [DoubleComplex.dTot_apply_succ_succ, OModulePresheaf.biCech_dH, OModulePresheaf.biCech_dV]
  erw [Pi.add_apply, Pi.smul_apply]
  rw [OModulePresheaf.BiCech.dH_apply, OModulePresheaf.BiCech.dV_apply]
  dsimp only
  by_cases h1 : p = a' + 1
  · subst h1
    obtain rfl : q = b' + 1 := by omega
    rw [Pi.single_eq_same, res_box]
    conv_lhs => arg 1; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov (a' + 1) (b' + 1) α β 0 a' (b' + 1) _ _ _ _ _ _ (by omega) rfl]
    conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov (a' + 1) (b' + 1) α β 0 (a' + 1) b' _ _ _ _ _ _ (by omega) (by omega)]
    simp only [smul_zero, Finset.sum_const_zero, add_zero]
    exact slot_TOP_A πX πY 𝔘 𝔙 haff hcov a' (b' + 1) α hα β K s t
  · by_cases h2 : p = a' + 2
    · subst h2
      obtain rfl : q = b' := by omega
      rw [Pi.single_eq_of_ne (diag_ne _ _ (by show a' + 1 ≠ a' + 2; omega))]
      erw [Pi.zero_apply]; rw [map_zero]
      conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov (a' + 2) q α β 0 a' (q + 1) _ _ _ _ _ _ (by omega) (by omega)]
      conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov (a' + 2) q α β 0 (a' + 1) q _ _ _ _ _ _ (by omega) rfl]
      simp only [smul_zero, Finset.sum_const_zero, zero_add]
      exact smul_eq_zero_of_right _ (slot_VERT_A πX πY 𝔘 𝔙 haff hcov (a' + 2) q α β hβ 0 (a' + 1) (by omega) K s t)
    · rw [Pi.single_eq_of_ne (diag_ne _ _ (by show a' + 1 ≠ p; omega))]
      erw [Pi.zero_apply]; rw [map_zero]
      by_cases h3 : p = 0 ∧ a' = 0
      · obtain ⟨rfl, rfl⟩ := h3
        conv_lhs => arg 1; arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov 0 q α β 0 0 (b' + 1) _ _ _ _ _ _ le_rfl rfl (by omega)]
        conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov 0 q α β 0 (0 + 1) b' _ _ _ _ _ _ (by omega) (by omega)]
        simp only [smul_zero, Finset.sum_const_zero, add_zero]
        exact slot_HOR_B πX πY 𝔘 𝔙 haff hcov 0 q α β 0 (b' + 1) le_rfl (by omega) K s t
      · conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β 0 a' (b' + 1) _ _ _ _ _ _ (by omega) (by omega)]
        conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β 0 (a' + 1) b' _ _ _ _ _ _ (by omega) (by omega)]
        simp only [smul_zero, Finset.sum_const_zero, add_zero]

theorem leaf_bot (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (m + 1)) (hab : 0 + 0 = 0) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx 0) :
    ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res (inf_le_inf_left _ ((𝔙.preimageFamily (pullback.snd πX πY)).restr_inter_mono (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter_le_inter_face K j) t))
          (ent πX πY 𝔘 𝔙 haff hcov p q α β m 0 (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K j) ⟨(0, 0), hab⟩ (s, t))
      = -(avalD (pullback.fst πX πY) 𝔘 p α (tupK (fun ij => (ofLex ij).1) (m + 1) p (by omega) K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)
          * avalD (pullback.snd πX πY) 𝔙 q β (tupKB (fun ij => (ofLex ij).2) (m + 1) p q hpq K.1) (OO πX πY 𝔘 𝔙 haff hcov K s t)) := by
  by_cases hq0 : q = 0
  · subst hq0
    obtain rfl : p = m + 1 := by omega
    conv_lhs => arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov (m + 1) 0 α β m 0 0 _ _ _ _ _ _ (by omega) rfl]
    exact slot_BOT_A πX πY 𝔘 𝔙 haff hcov m α hα β hβ K s t
  · obtain ⟨b', rfl⟩ : ∃ b', q = b' + 1 := ⟨q - 1, by omega⟩
    conv_lhs => arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov p (b' + 1) α β m 0 0 _ _ _ _ _ _ (by omega) rfl (by omega)]
    exact slot_BOT_B πX πY 𝔘 𝔙 haff hcov p b' m hpq α hα β hβ (by omega) (by omega) K s t

theorem leaf_int_v (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (r' m'' : ℕ) (hrm : r' + 1 + (m'' + 1) = m + 1) (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (r' + 1)) (b' : ℕ)
    (hab : 0 + (b' + 1) = m'' + 1) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx 0) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b' + 1)) :
    ∑ j : Fin (r' + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res (inf_le_inf_left _ ((𝔙.preimageFamily (pullback.snd πX πY)).restr_inter_mono (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter_le_inter_face K j) t))
          (ent πX πY 𝔘 𝔙 haff hcov p q α β r' (m'' + 1) (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K j) ⟨(0, b' + 1), hab⟩ (s, t))
      + ((-1 : ℤ) ^ (r' + 1)) • DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K))) m''
          (ent πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) m'' K) ⟨(0, b' + 1), hab⟩ (s, t) = 0 := by
  rw [DoubleComplex.dTot_apply_zero_succ, OModulePresheaf.biCech_dV, OModulePresheaf.BiCech.dV_apply]
  dsimp only
  by_cases hle : p ≤ r'
  · conv_lhs => arg 1; arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov p q α β r' 0 (b' + 1) _ _ _ _ _ _ hle rfl (by omega)]
    conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) 0 b' _ _ _ _ _ _ (by omega) rfl (by omega)]
    exact slot_INT_B πX πY 𝔘 𝔙 haff hcov p q α hα β hβ r' b' hle (by omega) (by omega) (by omega) K s t
  · by_cases hpe : p = r' + 1
    · conv_lhs => arg 1; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov p q α β r' 0 (b' + 1) _ _ _ _ _ _ (by omega) (by omega)]
      conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) 0 b' _ _ _ _ _ _ (by omega) rfl (by omega)]
      exact slot_INT_AB πX πY 𝔘 𝔙 haff hcov p q α hα β hβ r' b' (by omega) (by omega) (by omega) K s t
    · by_cases hpe2 : p = r' + 2
      · subst hpe2
        obtain rfl : q = b' := by omega
        conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov (r' + 2) q α β r' 0 (q + 1) _ _ _ _ _ _ (by omega) (by omega)]
        conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov (r' + 2) q α β (r' + 1) 0 q _ _ _ _ _ _ (by omega) rfl]
        simp only [smul_zero, Finset.sum_const_zero, zero_add]
        exact smul_eq_zero_of_right _ (slot_VERT_A πX πY 𝔘 𝔙 haff hcov (r' + 2) q α β hβ (r' + 1) 0 (by omega) K s t)
      · conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β r' 0 (b' + 1) _ _ _ _ _ _ (by omega) (by omega)]
        conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) 0 b' _ _ _ _ _ _ (by omega) (by omega)]
        simp only [smul_zero, Finset.sum_const_zero, add_zero]

theorem leaf_int_h (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (r' m'' : ℕ) (hrm : r' + 1 + (m'' + 1) = m + 1) (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (r' + 1)) (a' : ℕ)
    (hab : a' + 1 + 0 = m'' + 1) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx (a' + 1)) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx 0) :
    ∑ j : Fin (r' + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res (inf_le_inf_left _ ((𝔙.preimageFamily (pullback.snd πX πY)).restr_inter_mono (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter_le_inter_face K j) t))
          (ent πX πY 𝔘 𝔙 haff hcov p q α β r' (m'' + 1) (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K j) ⟨(a' + 1, 0), hab⟩ (s, t))
      + ((-1 : ℤ) ^ (r' + 1)) • DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K))) m''
          (ent πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) m'' K) ⟨(a' + 1, 0), hab⟩ (s, t) = 0 := by
  rw [DoubleComplex.dTot_apply_succ_zero, OModulePresheaf.biCech_dH, OModulePresheaf.BiCech.dH_apply]
  dsimp only
  by_cases hq0 : q = 0
  · subst hq0
    conv_lhs => arg 1; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov p 0 α β r' (a' + 1) 0 _ _ _ _ _ _ (by omega) rfl]
    conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov p 0 α β (r' + 1) a' 0 _ _ _ _ _ _ (by omega) rfl]
    exact slot_INT_A πX πY 𝔘 𝔙 haff hcov p 0 α hα β r' a' (by omega) K s t
  · by_cases hB : p ≤ r' + 1 ∧ a' = 0
    · obtain ⟨hle, rfl⟩ := hB
      conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β r' (0 + 1) 0 _ _ _ _ _ _ (by omega) (by omega)]
      conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) 0 0 _ _ _ _ _ _ hle rfl (by omega)]
      simp only [smul_zero, Finset.sum_const_zero, zero_add]
      exact smul_eq_zero_of_right _ (slot_HOR_B πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) 0 hle (by omega) K s t)
    · conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β r' (a' + 1) 0 _ _ _ _ _ _ (by omega) (by omega)]
      conv_lhs => arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) a' 0 _ _ _ _ _ _ (by omega) (by omega)]
      simp only [smul_zero, Finset.sum_const_zero, add_zero]

theorem leaf_int_hv (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0)
    (r' m'' : ℕ) (hrm : r' + 1 + (m'' + 1) = m + 1) (K : ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.Idx (r' + 1)) (a' b' : ℕ)
    (hab : a' + 1 + (b' + 1) = m'' + 1) (s : (𝔘.preimageFamily (pullback.fst πX πY)).Idx (a' + 1)) (t : ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K)).Idx (b' + 1)) :
    ∑ j : Fin (r' + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res (inf_le_inf_left _ ((𝔙.preimageFamily (pullback.snd πX πY)).restr_inter_mono (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter_le_inter_face K j) t))
          (ent πX πY 𝔘 𝔙 haff hcov p q α β r' (m'' + 1) (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.face K j) ⟨(a' + 1, b' + 1), hab⟩ (s, t))
      + ((-1 : ℤ) ^ (r' + 1)) • DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) ((𝔙.preimageFamily (pullback.snd πX πY)).restr (((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily.inter K))) m''
          (ent πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) m'' K) ⟨(a' + 1, b' + 1), hab⟩ (s, t) = 0 := by
  rw [DoubleComplex.dTot_apply_succ_succ, OModulePresheaf.biCech_dH, OModulePresheaf.biCech_dV]
  erw [Pi.add_apply, Pi.smul_apply]
  rw [OModulePresheaf.BiCech.dH_apply, OModulePresheaf.BiCech.dV_apply]
  dsimp only
  by_cases h1 : r' + 1 + a' + 1 = p
  · obtain rfl : q = b' + 1 := by omega
    conv_lhs => arg 1; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov p (b' + 1) α β r' (a' + 1) (b' + 1) _ _ _ _ _ _ (by omega) rfl]
    conv_lhs => arg 2; arg 2; arg 1; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov p (b' + 1) α β (r' + 1) a' (b' + 1) _ _ _ _ _ _ h1 rfl]
    conv_lhs => arg 2; arg 2; arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p (b' + 1) α β (r' + 1) (a' + 1) b' _ _ _ _ _ _ (by omega) (by omega)]
    simp only [smul_zero, Finset.sum_const_zero, add_zero]
    exact slot_INT_A πX πY 𝔘 𝔙 haff hcov p (b' + 1) α hα β r' a' h1 K s t
  · by_cases h2 : r' + 1 + (a' + 1) + 1 = p
    · obtain rfl : q = b' := by omega
      conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β r' (a' + 1) (q + 1) _ _ _ _ _ _ (by omega) (by omega)]
      conv_lhs => arg 2; arg 2; arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) a' (q + 1) _ _ _ _ _ _ (by omega) (by omega)]
      conv_lhs => arg 2; arg 2; arg 2; arg 2; arg 2; ext j; rw [res_ent_A πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) (a' + 1) q _ _ _ _ _ _ h2 rfl]
      simp only [smul_zero, Finset.sum_const_zero, zero_add]
      exact smul_eq_zero_of_right _ (smul_eq_zero_of_right _
        (slot_VERT_A πX πY 𝔘 𝔙 haff hcov p q α β hβ (r' + 1) (a' + 1) h2 K s t))
    · by_cases h3 : p ≤ r' + 1 ∧ a' = 0
      · obtain ⟨hle, rfl⟩ := h3
        conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β r' (0 + 1) (b' + 1) _ _ _ _ _ _ (by omega) (by omega)]
        conv_lhs => arg 2; arg 2; arg 1; arg 2; ext j; rw [res_ent_B πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) 0 (b' + 1) _ _ _ _ _ _ hle rfl (by omega)]
        conv_lhs => arg 2; arg 2; arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) (0 + 1) b' _ _ _ _ _ _ (by omega) (by omega)]
        simp only [smul_zero, Finset.sum_const_zero, zero_add, add_zero]
        exact smul_eq_zero_of_right _ (slot_HOR_B πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) (b' + 1) hle (by omega) K s t)
      · conv_lhs => arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β r' (a' + 1) (b' + 1) _ _ _ _ _ _ (by omega) (by omega)]
        conv_lhs => arg 2; arg 2; arg 1; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) a' (b' + 1) _ _ _ _ _ _ (by omega) (by omega)]
        conv_lhs => arg 2; arg 2; arg 2; arg 2; arg 2; ext j; rw [res_ent_zero πX πY 𝔘 𝔙 haff hcov p q α β (r' + 1) (a' + 1) b' _ _ _ _ _ _ (by omega) (by omega)]
        simp only [smul_zero, Finset.sum_const_zero, add_zero]

theorem staircase (p q m : ℕ) (hpq : p + q = m + 1) (α : (unit πX).cochain 𝔘 p)
    (hα : (unit πX).d 𝔘 p α = 0) (β : (unit πY).cochain 𝔙 q) (hβ : (unit πY).d 𝔙 q β = 0) :
    DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) m (fun rm => ent πX πY 𝔘 𝔙 haff hcov p q α β rm.1.1 rm.1.2)
      = Pi.single (M := fun rm : DoubleComplex.Diag (m + 1) => ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily).C rm.1.1 rm.1.2) ⟨(0, m + 1), by omega⟩
          (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily (m + 1)
            (Pi.single ⟨(p, q), hpq⟩ (fun st : 𝔘.Idx p × 𝔙.Idx q =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q) : DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) (m + 1)))
        - Pi.single (M := fun rm : DoubleComplex.Diag (m + 1) => ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily).C rm.1.1 rm.1.2) ⟨(m + 1, 0), by omega⟩
          (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) (m + 1) ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) p q (m + 1) hpq
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘 (fun ij => (ofLex ij).1) (fun ij => inf_le_left) p α)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙 (fun ij => (ofLex ij).2) (fun ij => inf_le_right) q β))) := by
  funext rm K pq st
  obtain ⟨⟨r, m'⟩, hrm⟩ := rm
  obtain ⟨⟨a, b⟩, hab⟩ := pq
  obtain ⟨s, t⟩ := st
  change r + m' = m + 1 at hrm
  change a + b = m' at hab
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply]
  rcases r with _ | r'
  ·
    obtain rfl : m' = m + 1 := by omega
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (diag_ne _ _ (by show (0 : ℕ) ≠ m + 1; omega)),
      Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_zero, DoubleComplex.dTot_apply_zero_succ,
      OModulePresheaf.iterCech_dV, OModulePresheaf.IterCech.dV_apply, OModulePresheaf.IterCech.augTot_apply,
      OModulePresheaf.IterCech.resTot₀_apply]
    rcases a with _ | a' <;> rcases b with _ | b'
    · exfalso; omega
    · exact leaf_top_v πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ K b' hab s t _
    · exact leaf_top_h πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ K a' hab s t _
    · exact leaf_top_hv πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ K a' b' hab s t _
  · rcases m' with _ | m''
    ·
      obtain rfl : m = r' := by omega
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
      rw [Pi.single_eq_of_ne (diag_ne _ _ (by show m + 1 ≠ 0; omega)), Pi.single_eq_same,
        Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, zero_sub, DoubleComplex.dTot_apply_succ_zero,
        OModulePresheaf.iterCech_dH, dHK_apply, OModulePresheaf.IterCech.augCech_apply, res_cup]
      exact leaf_bot πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ K hab s t
    ·
      rw [Pi.single_eq_of_ne (diag_ne _ _ (by show r' + 1 ≠ 0; omega)),
        Pi.single_eq_of_ne (diag_ne _ _ (by show r' + 1 ≠ m + 1; omega)),
        Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_self,
        DoubleComplex.dTot_apply_succ_succ, Pi.add_apply, Pi.add_apply, Pi.add_apply,
        Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
        OModulePresheaf.iterCech_dH, OModulePresheaf.iterCech_dV, dHK_apply, OModulePresheaf.IterCech.dV_apply]
      rcases a with _ | a' <;> rcases b with _ | b'
      · exfalso; omega
      · exact leaf_int_v πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ r' m'' hrm K b' hab s t
      · exact leaf_int_h πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ r' m'' hrm K a' hab s t
      · exact leaf_int_hv πX πY 𝔘 𝔙 haff hcov p q m hpq α hα β hβ r' m'' hrm K a' b' hab s t

end Assembly

end Main

end AlgebraicGeometry.OModulePresheaf.IterCech.Staircase
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf.IterCech P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf.IterCech.Staircase"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf.IterCech"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry.OModulePresheaf"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.AlgebraicGeometry"

open AlgebraicGeometry.OModulePresheaf.IterCech.Staircase in
theorem solution
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)
    (m : ℕ) (i : DoubleComplex.Diag (m + 1))
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
    (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2))) :
    ∃ h : DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) m,
      DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) m h =
        Pi.single (M := fun rm : DoubleComplex.Diag (m + 1) => (((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily)).C rm.1.1 rm.1.2) ⟨(0, m + 1), by omega⟩
          (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily
            (m + 1)
            (Pi.single i
              (fun st : 𝔘.Idx i.1.1 × 𝔙.Idx i.1.2 =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α.1 st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β.1 st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
                  (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) i.1.1 i.1.2) :
              DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech
                (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) (m + 1)))
        - Pi.single (M := fun rm : DoubleComplex.Diag (m + 1) => (((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily)).C rm.1.1 rm.1.2) ⟨(m + 1, 0), by omega⟩
          (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
            (m + 1)
            ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 (m + 1) i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1))) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  exact ⟨_, AlgebraicGeometry.OModulePresheaf.IterCech.Staircase.staircase πX πY 𝔘 𝔙 haff hcov p q m hpq
    α.1 (LinearMap.mem_ker.1 α.2) β.1 (LinearMap.mem_ker.1 β.2)⟩

end
end S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup (solution)
