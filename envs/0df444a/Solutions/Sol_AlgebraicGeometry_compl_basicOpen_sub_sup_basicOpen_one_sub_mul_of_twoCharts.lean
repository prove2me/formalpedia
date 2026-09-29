-- Prove2me | solution 1 for AlgebraicGeometry.compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1181c519-febe-5f5d-a62d-a59989770c9e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen RingedSpace.isUnit_res_basicOpen Scheme isAffineOpen_of_isAffineOpen_basicOpen Scheme.basicOpen_mul IsAffineOpen RingedSpace"
namespace TwoChartsJne
p2m_open "AlgebraicGeometry"

variable {X : Scheme.{u}}

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom x = _
  rw [← Functor.map_comp]
  rfl

theorem basicOpen_res' {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    X.basicOpen (res h x) = V ⊓ X.basicOpen x :=
  X.basicOpen_res x (homOfLE h).op

theorem isUnit_res_basicOpen' {U : X.Opens} (x : Γ(X, U)) :
    IsUnit (res (X.basicOpen_le x) x) :=
  RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toRingedSpace) x

theorem inv_unique {M : Type*} [CommMonoid M] {a b c : M} (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  calc b = b * (a * c) := by rw [hc, mul_one]
    _ = (a * b) * c := by rw [← mul_assoc, mul_comm b a]
    _ = c := by rw [hb, one_mul]

section Main

variable (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : res (inf_le_left : U ⊓ V ≤ U) f * res (inf_le_right : U ⊓ V ≤ V) g = 1)
    (hUV : U ⊔ V = ⊤)
    (s : Γ(X, ⊤))

include hfg in

theorem res_one_sub_mul :
    res (inf_le_right : U ⊓ V ≤ V) (1 - res (le_top : V ≤ ⊤) s * g) =
      res (inf_le_left : U ⊓ V ≤ U) (f - res (le_top : U ≤ ⊤) s) * res (inf_le_right : U ⊓ V ≤ V) g := by
  rw [map_sub, map_one, map_mul, map_sub, sub_mul, hfg, res_res, res_res]

include hg hfg in

theorem inf_basicOpen_eq :
    (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) =
      (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
  calc (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g)
        = X.basicOpen (res (inf_le_right : U ⊓ V ≤ V) (1 - res (le_top : V ≤ ⊤) s * g)) :=
          (basicOpen_res' _ _).symm
    _ = X.basicOpen (res (inf_le_left : U ⊓ V ≤ U) (f - res (le_top : U ≤ ⊤) s)) ⊓
          X.basicOpen (res (inf_le_right : U ⊓ V ≤ V) g) := by
          rw [res_one_sub_mul U V f g hfg s, Scheme.basicOpen_mul]
    _ = ((U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s)) ⊓ ((U ⊓ V) ⊓ (U ⊓ V)) := by
          rw [basicOpen_res', basicOpen_res', ← hg]
    _ = (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
          rw [inf_idem]
          exact inf_eq_left.mpr inf_le_left

include hg hfg in

theorem basicOpen_inf_basicOpen_eq :
    X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) =
      (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
  have key := inf_basicOpen_eq U V f g hg hfg s
  apply le_antisymm
  · refine le_inf (le_inf ?_ ?_) inf_le_left
    · exact inf_le_left.trans (X.basicOpen_le _)
    · exact inf_le_right.trans (X.basicOpen_le _)
  · refine le_inf inf_le_right ?_
    rw [← key]; exact inf_le_right

include hg in

theorem mem_basicOpen_one_sub_mul {x : X} (hxV : x ∈ V) (hxU : x ∉ U) :
    x ∈ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) := by
  rw [Scheme.mem_basicOpen _ _ _ hxV, map_sub, map_one, map_mul]
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [← IsLocalRing.mem_maximalIdeal]
  apply Ideal.mul_mem_left
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen _ _ _ hxV, ← hg]
  exact fun h => hxU h.1

include hg hfg hUV in

theorem compl_sup_eq :
    ((X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊔ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) : X.Opens) : Set X)ᶜ =
      (U : Set X) ∩ (X.basicOpen (f - res (le_top : U ≤ ⊤) s) : Set X)ᶜ := by
  have hAB := basicOpen_inf_basicOpen_eq U V f g hg hfg s
  ext x
  simp only [Opens.coe_sup, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨?_, hA⟩
    by_contra hxU
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← hUV] at hx
    rcases (show x ∈ (U : Set X) ∪ (V : Set X) by exact hx) with h | h
    · exact hxU h
    · exact hB (mem_basicOpen_one_sub_mul U V g hg s h hxU)
  · rintro ⟨hxU, hA⟩
    refine ⟨hA, fun hB => hA ?_⟩
    have key := inf_basicOpen_eq U V f g hg hfg s
    have : x ∈ (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) := ⟨⟨hxU, X.basicOpen_le _ hB⟩, hB⟩
    rw [key] at this
    exact this.2

include hU hV hf hg hfg in
theorem isAffineOpen_sup :
    IsAffineOpen (X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊔ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g)) := by

  set sU := res (le_top : U ≤ ⊤) s with hsU
  set sV := res (le_top : V ≤ ⊤) s with hsV
  set A : X.Opens := X.basicOpen (f - sU) with hA
  set B : X.Opens := X.basicOpen (1 - sV * g) with hB
  have hAU : A ≤ U := X.basicOpen_le _
  have hBV : B ≤ V := X.basicOpen_le _
  have key : (U ⊓ V) ⊓ B = (U ⊓ V) ⊓ A := inf_basicOpen_eq U V f g hg hfg s

  have huA : IsUnit (res hAU (f - sU)) := isUnit_res_basicOpen' _
  set tA : Γ(X, A) := ↑(huA.unit⁻¹) with htA_def
  have htA : res hAU (f - sU) * tA = 1 := huA.mul_val_inv

  have huB : IsUnit (res hBV (1 - sV * g)) := isUnit_res_basicOpen' _
  set wB : Γ(X, B) := ↑(huB.unit⁻¹) with hwB_def
  have hwB : res hBV (1 - sV * g) * wB = 1 := huB.mul_val_inv
  set tB : Γ(X, B) := res hBV g * wB with htB_def

  have hABUV : A ⊓ B ≤ U ⊓ V := inf_le_inf hAU hBV
  have h1 : res ((inf_le_left : A ⊓ B ≤ A).trans hAU) (f - sU) * res (inf_le_left : A ⊓ B ≤ A) tA = 1 := by
    rw [← res_res hAU (inf_le_left : A ⊓ B ≤ A), ← map_mul, htA, map_one]
  have h2 : res ((inf_le_left : A ⊓ B ≤ A).trans hAU) (f - sU) * res (inf_le_right : A ⊓ B ≤ B) tB = 1 := by
    rw [htB_def, map_mul, ← mul_assoc]
    have e : res ((inf_le_left : A ⊓ B ≤ A).trans hAU) (f - sU) * res (inf_le_right : A ⊓ B ≤ B) (res hBV g) =
        res (inf_le_right : A ⊓ B ≤ B) (res hBV (1 - sV * g)) := by
      rw [res_res, res_res,
        ← res_res (inf_le_left : U ⊓ V ≤ U) hABUV, ← res_res (inf_le_right : U ⊓ V ≤ V) hABUV,
        ← res_res (inf_le_right : U ⊓ V ≤ V) hABUV, ← map_mul, ← res_one_sub_mul U V f g hfg s]
    rw [e, ← map_mul, hwB, map_one]
  have hagree : res (inf_le_left : A ⊓ B ≤ A) tA = res (inf_le_right : A ⊓ B ≤ B) tB := inv_unique h1 h2

  set W : X.Opens := A ⊔ B with hW
  let tt : RingHom.eqLocus
      (RingHom.comp (X.sheaf.1.map (homOfLE inf_le_left : A ⊓ B ⟶ A).op).hom
        (RingHom.fst (X.sheaf.1.obj (op A)) (X.sheaf.1.obj (op B))))
      (RingHom.comp (X.sheaf.1.map (homOfLE inf_le_right : A ⊓ B ⟶ B).op).hom
        (RingHom.snd (X.sheaf.1.obj (op A)) (X.sheaf.1.obj (op B)))) := ⟨(tA, tB), hagree⟩
  set t : Γ(X, W) := (X.sheaf.objSupIsoProdEqLocus A B).inv tt with ht_def
  have htA' : res (le_sup_left : A ≤ W) t = tA := TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf A B tt
  have htB' : res (le_sup_right : B ≤ W) t = tB := TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf A B tt

  have hAt : A ⊓ X.basicOpen t = A := by
    rw [← basicOpen_res' (le_sup_left : A ≤ W), htA', htA_def, X.basicOpen_of_isUnit (Units.isUnit _)]
  have hBt : B ⊓ X.basicOpen t = (U ⊓ V) ⊓ B := by
    rw [← basicOpen_res' (le_sup_right : B ≤ W), htB', htB_def, Scheme.basicOpen_mul, hwB_def, X.basicOpen_of_isUnit (Units.isUnit _),
      basicOpen_res', ← hg]
    rw [inf_comm B (U ⊓ V), inf_assoc, inf_idem]
  have hDt : X.basicOpen t = A := by
    have hle : X.basicOpen t ≤ W := X.basicOpen_le _
    calc X.basicOpen t = W ⊓ X.basicOpen t := (inf_eq_right.mpr hle).symm
      _ = (A ⊓ X.basicOpen t) ⊔ (B ⊓ X.basicOpen t) := inf_sup_right _ _ _
      _ = A ⊔ ((U ⊓ V) ⊓ A) := by rw [hAt, hBt, key]
      _ = A := sup_eq_left.mpr inf_le_right

  set sW := res (le_top : W ≤ ⊤) s with hsW
  set u' : Γ(X, W) := 1 + sW * t with hu'
  have hAu : A ⊓ X.basicOpen u' = (U ⊓ V) ⊓ A := by
    rw [← basicOpen_res' (le_sup_left : A ≤ W), hu', map_add, map_one, map_mul, htA', hsW, res_res]
    have e : (1 : Γ(X, A)) + res ((le_sup_left : A ≤ W).trans (le_top : W ≤ ⊤)) s * tA = res hAU f * tA := by
      have : res hAU (f - sU) = res hAU f - res ((le_sup_left : A ≤ W).trans (le_top : W ≤ ⊤)) s := by
        rw [map_sub, hsU, res_res]
      rw [← htA, this, sub_mul, sub_add_cancel]
    rw [e, Scheme.basicOpen_mul, htA_def, X.basicOpen_of_isUnit (Units.isUnit _), basicOpen_res', ← hf,
      inf_comm A (U ⊓ V), inf_assoc, inf_idem]
  have hBu : B ⊓ X.basicOpen u' = B := by
    rw [← basicOpen_res' (le_sup_right : B ≤ W), hu', map_add, map_one, map_mul, htB', hsW, res_res]
    have e : (1 : Γ(X, B)) + res ((le_sup_right : B ≤ W).trans (le_top : W ≤ ⊤)) s * tB = wB := by
      have : res hBV (1 - sV * g) = 1 - res ((le_sup_right : B ≤ W).trans (le_top : W ≤ ⊤)) s * res hBV g := by
        rw [map_sub, map_one, map_mul, hsV, res_res]
      rw [htB_def]
      calc (1 : Γ(X, B)) + res ((le_sup_right : B ≤ W).trans (le_top : W ≤ ⊤)) s * (res hBV g * wB)
          = res hBV (1 - sV * g) * wB + res ((le_sup_right : B ≤ W).trans (le_top : W ≤ ⊤)) s * (res hBV g * wB) := by
            rw [hwB]
        _ = wB := by rw [this]; ring
    rw [e, hwB_def, X.basicOpen_of_isUnit (Units.isUnit _)]
  have hDu : X.basicOpen u' = B := by
    have hle : X.basicOpen u' ≤ W := X.basicOpen_le _
    calc X.basicOpen u' = W ⊓ X.basicOpen u' := (inf_eq_right.mpr hle).symm
      _ = (A ⊓ X.basicOpen u') ⊔ (B ⊓ X.basicOpen u') := inf_sup_right _ _ _
      _ = ((U ⊓ V) ⊓ A) ⊔ B := by rw [hAu, hBu]
      _ = B := by rw [← key]; exact sup_eq_right.mpr inf_le_right

  refine isAffineOpen_of_isAffineOpen_basicOpen W {t, u'} ?_ ?_
  · rw [Ideal.eq_top_iff_one]
    refine Ideal.mem_span_pair.mpr ⟨-sW, 1, ?_⟩
    rw [hu']; ring
  · intro i hi
    rcases hi with rfl | hi
    · rw [hDt]; exact hU.basicOpen _
    · rw [Set.mem_singleton_iff] at hi
      rw [hi, hDu]; exact hV.basicOpen _

include hg hUV in

theorem left_sup_sup_eq_top :
    U ⊔ (X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊔ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g)) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases hx with hx | hx
  · exact Or.inl hx
  · by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr (Or.inr (mem_basicOpen_one_sub_mul U V g hg s hx hxU))

include hg hfg in

theorem left_inf_sup_eq :
    U ⊓ (X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊔ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g)) =
      X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
  have key := inf_basicOpen_eq U V f g hg hfg s
  rw [inf_sup_left]
  apply le_antisymm
  · refine sup_le inf_le_right ?_
    calc U ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g)
          ≤ (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) :=
            le_inf (le_inf inf_le_left (inf_le_right.trans (X.basicOpen_le _))) inf_le_right
      _ = (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := key
      _ ≤ _ := inf_le_right
  · exact le_sup_of_le_left (le_inf (X.basicOpen_le _) le_rfl)

end Main

end AlgebraicGeometry.TwoChartsJne

end

theorem solution
    {X : Scheme.{u}} (U V : X.Opens)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hUV : U ⊔ V = ⊤) (s : Γ(X, ⊤)) :
    ((X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s * g) : X.Opens) : Set X)ᶜ =
      (U : Set X) ∩ (X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) : Set X)ᶜ :=
  AlgebraicGeometry.TwoChartsJne.compl_sup_eq U V f g hg hfg hUV s

end S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts
end P2MW
export P2MW.S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts (solution)
