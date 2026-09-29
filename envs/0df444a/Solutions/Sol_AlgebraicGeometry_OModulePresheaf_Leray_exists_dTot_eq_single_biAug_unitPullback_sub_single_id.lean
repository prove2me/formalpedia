-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.Leray.exists_dTot_eq_single_biAug_unitPullback_sub_single_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/72032b17-cdab-586f-b874-972a235b367d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_oext
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_oext
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace KDCat
p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover"

variable {X : Scheme.{u}} (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι)

def cat {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m) : Fin m → 𝔓.ι :=
  fun k => if h : (k : ℕ) < a + 1 then σ.1 ⟨k, h⟩ else lam (τ.1 ⟨k - (a + 1), by omega⟩)

theorem cat_apply_lt {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m) (k : Fin m)
    (h : (k : ℕ) < a + 1) : cat 𝔓 𝒲 lam σ τ m hm k = σ.1 ⟨k, h⟩ := by
  simp only [cat, dif_pos h]

theorem cat_apply_ge {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m) (k : Fin m)
    (h : ¬ (k : ℕ) < a + 1) : cat 𝔓 𝒲 lam σ τ m hm k = lam (τ.1 ⟨k - (a + 1), by omega⟩) := by
  simp only [cat, dif_neg h]

omit 𝔓 𝒲 lam in
theorem val_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).1 = if i.1 < p.1 then i.1 else i.1 + 1 := by
  by_cases hi : Fin.castSucc i < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi, if_pos (by simpa [Fin.lt_def] using hi)]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 hi), if_neg (by simpa [Fin.lt_def] using hi)]; rfl

theorem oface_cat_left {a b n : ℕ} (σ : 𝔓.Idx (a + 1)) (τ : 𝒲.Idx b) (hm : a + 1 + b + 2 = n + 3)
    (j : Fin (a + 2)) (hj : (j : ℕ) < n + 3) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (n + 3) hm) ⟨j, hj⟩ = cat 𝔓 𝒲 lam (𝔓.face σ j) τ (n + 2) (by omega) := by
  funext k
  rw [oface_apply]
  have hv : (((⟨j, hj⟩ : Fin (n + 3)).succAbove k) : ℕ) = if (k : ℕ) < j then (k : ℕ) else (k : ℕ) + 1 :=
    val_succAbove _ _
  by_cases hk : (k : ℕ) < a + 1
  · rw [cat_apply_lt _ _ _ _ _ _ _ _ hk, face_val, Function.comp_apply]
    have h1 : ((⟨j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_lt _ _ _ _ _ _ _ _ h1]
    refine congrArg σ.1 (Fin.ext ?_)
    have hv2 := val_succAbove j ⟨(k : ℕ), hk⟩
    simp only [Fin.val_mk] at hv2 ⊢
    split_ifs at hv hv2 <;> omega
  · have h1 : ¬ ((⟨j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_ge _ _ _ _ _ _ _ _ hk, cat_apply_ge _ _ _ _ _ _ _ _ h1]
    refine congrArg lam (congrArg τ.1 (Fin.ext ?_))
    simp only [Fin.val_mk]
    split_ifs at hv <;> omega

theorem oface_cat_right {a b n : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx (b + 1)) (hm : a + (b + 1) + 2 = n + 3)
    (j : Fin (b + 2)) (hj : a + 1 + (j : ℕ) < n + 3) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (n + 3) hm) ⟨a + 1 + j, hj⟩ = cat 𝔓 𝒲 lam σ (𝒲.face τ j) (n + 2) (by omega) := by
  funext k
  rw [oface_apply]
  have hv : (((⟨a + 1 + j, hj⟩ : Fin (n + 3)).succAbove k) : ℕ) = if (k : ℕ) < a + 1 + j then (k : ℕ) else (k : ℕ) + 1 :=
    val_succAbove _ _
  by_cases hk : (k : ℕ) < a + 1
  · have h1 : ((⟨a + 1 + j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_lt _ _ _ _ _ _ _ _ hk, cat_apply_lt _ _ _ _ _ _ _ _ h1]
    refine congrArg σ.1 (Fin.ext ?_)
    simp only [Fin.val_mk]
    split_ifs at hv <;> omega
  · have h1 : ¬ ((⟨a + 1 + j, hj⟩ : Fin (n + 3)).succAbove k : ℕ) < a + 1 := by rw [hv]; split_ifs <;> omega
    rw [cat_apply_ge _ _ _ _ _ _ _ _ hk, cat_apply_ge _ _ _ _ _ _ _ _ h1, face_val, Function.comp_apply]
    refine congrArg lam (congrArg τ.1 (Fin.ext ?_))
    have hv2 := val_succAbove j ⟨(k : ℕ) - (a + 1), by omega⟩
    simp only [Fin.val_mk] at hv2 ⊢
    split_ifs at hv hv2 <;> omega

theorem oface_cat_zero {b : ℕ} (σ : 𝔓.Idx 0) (τ : 𝒲.Idx b) (hm : 0 + b + 2 = b + 2) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (b + 2) hm) 0 = lam ∘ τ.1 := by
  funext k
  rw [oface_apply, Fin.succAbove_zero, cat_apply_ge _ _ _ _ _ _ _ _ (by simp), Function.comp_apply]
  exact congrArg lam (congrArg τ.1 (Fin.ext (by simp)))

theorem oface_cat_last {a : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx 0) (hm : a + 0 + 2 = a + 2) :
    𝔓.oface (cat 𝔓 𝒲 lam σ τ (a + 2) hm) (Fin.last (a + 1)) = σ.1 := by
  funext k
  rw [oface_apply, Fin.succAbove_last, cat_apply_lt _ _ _ _ _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
  rfl

theorem cat_castSucc {a : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx 0) (hm : a + 0 + 2 = a + 2) (k : Fin (a + 1)) :
    cat 𝔓 𝒲 lam σ τ (a + 2) hm (Fin.castSucc k) = σ.1 k := by
  rw [cat_apply_lt _ _ _ _ _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
  rfl

end KDCat

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.Scheme.OrderedAffineCover KDCat

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 0)),
        OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 0 (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) =
          (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 0 0 => (X.presheaf.map (homOfLE ((inf_le_right :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 0 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
              (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1) :
            OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 0 0)) ∧
    ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
      ∃ h : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n,
        DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n h =
          Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(0, n + 1), by omega⟩
              (OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 (n + 1)
                (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1)) -
            Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(n + 1, 0), by omega⟩
              (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 (n + 1) 0 => (X.presheaf.map (homOfLE ((inf_le_right :
                OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
                  (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1)) := by
  classical

  have hle_cat : ∀ {a b : ℕ} (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) (m : ℕ) (hm : a + b + 2 = m + 1),
      biOpen (𝟙 X) 𝔓 𝒲 a b σ τ ≤ 𝔓.ointer (cat 𝔓 𝒲 lam σ τ (m + 1) hm) := by
    intro a b σ τ m hm
    refine le_iInf fun k => ?_
    by_cases hk : (k : ℕ) < a + 1
    · rw [cat_apply_lt _ _ _ _ _ _ _ _ hk]
      exact inf_le_right.trans ((Scheme.Hom.id_preimage _).le.trans (𝔓.inter_le σ ⟨k, hk⟩))
    · rw [cat_apply_ge _ _ _ _ _ _ _ _ hk]
      exact inf_le_left.trans ((𝒲.inter_le τ _).trans ((hlam _).trans (Scheme.Hom.id_preimage _).le))

  have hpb : ∀ (m : ℕ) (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) (τ : 𝒲.Idx m),
      OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m z τ =
        (OModulePresheaf.unit (𝟙 X ≫ π)).res ((𝒲.ointer_le_preimage_ointer_comp (𝟙 X) 𝔓 lam hlam τ.1).trans (Scheme.Hom.id_preimage _).le)
          ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 m z (lam ∘ τ.1)) := by
    intro m z τ
    rw [← ores_ounitPullback_oext (𝟙 X ≫ π) (𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m z, ores_apply, ounitPullback_apply,
      Scheme.Hom.id_app]
    rfl

  have resc : ∀ {m : ℕ} (ζ : (OModulePresheaf.unit (𝟙 X ≫ π)).ocochain 𝔓 m) (t t' : 𝔓.OIdx m) (e : t = t') {U : X.Opens}
      (h : U ≤ 𝔓.ointer t) (h' : U ≤ 𝔓.ointer t'), (OModulePresheaf.unit (𝟙 X ≫ π)).res h (ζ t) = (OModulePresheaf.unit (𝟙 X ≫ π)).res h' (ζ t') := by
    intro m ζ t t' e U h h'; subst e; rfl

  have hcoc : ∀ {m : ℕ} (ζ : (OModulePresheaf.unit (𝟙 X ≫ π)).ocochain 𝔓 m) (hζ : (OModulePresheaf.unit (𝟙 X ≫ π)).od 𝔓 m ζ = 0) (t : 𝔓.OIdx (m + 1)) {U : X.Opens}
      (hU : U ≤ 𝔓.ointer t),
      ∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hU.trans (𝔓.ointer_le_ointer_oface t k)) (ζ (𝔓.oface t k)) = 0 := by
    intro m ζ hζ t U hU
    have h0 := congrArg ((OModulePresheaf.unit (𝟙 X ≫ π)).res hU) (congrFun hζ t)
    rw [od_apply, map_sum, Pi.zero_apply, map_zero] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, OModulePresheaf.res_res]

  have hzσ : ∀ {m : ℕ} (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) (σ : 𝔓.Idx m), z σ = (OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 m z σ.1 := by
    intro m z σ
    conv_lhs => rw [← ores_oext (OModulePresheaf.unit (𝟙 X ≫ π)) 𝔓 m z]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro z
    funext στ
    obtain ⟨σ, τ⟩ := στ
    have hζ : (OModulePresheaf.unit (𝟙 X ≫ π)).od 𝔓 0 ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 0 z.1) = 0 := by
      rw [od_oext, LinearMap.mem_ker.1 z.2, map_zero]
    have hc := hcoc _ hζ (cat 𝔓 𝒲 lam σ τ 2 (by omega)) (hle_cat σ τ 1 (by omega))
    rw [Fin.sum_univ_two] at hc
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul, ← sub_eq_add_neg,
      sub_eq_zero] at hc
    have e0 : 𝔓.oface (cat 𝔓 𝒲 lam σ τ 2 (by omega)) 0 = lam ∘ τ.1 := oface_cat_zero 𝔓 𝒲 lam σ τ (by omega)
    have e1 : 𝔓.oface (cat 𝔓 𝒲 lam σ τ 2 (by omega)) 1 = σ.1 := oface_cat_last 𝔓 𝒲 lam σ τ (by omega)
    have h0' : biOpen (𝟙 X) 𝔓 𝒲 0 0 σ τ ≤ 𝔓.ointer (lam ∘ τ.1) :=
      (inf_le_left.trans (𝒲.ointer_le_preimage_ointer_comp (𝟙 X) 𝔓 lam hlam τ.1)).trans (Scheme.Hom.id_preimage _).le
    have h1' : biOpen (𝟙 X) 𝔓 𝒲 0 0 σ τ ≤ 𝔓.ointer σ.1 := inf_le_right.trans (Scheme.Hom.id_preimage _).le
    rw [resc _ _ _ e0 _ h0', resc _ _ _ e1 _ h1'] at hc
    rw [biAug_apply, hpb, hzσ z.1 σ]
    change (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ _) = (OModulePresheaf.unit (𝟙 X ≫ π)).res _ _
    rw [OModulePresheaf.res_res]
    exact hc
  ·
    intro n z
    have hζ : (OModulePresheaf.unit (𝟙 X ≫ π)).od 𝔓 (n + 1) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1) = 0 := by
      rw [od_oext, LinearMap.mem_ker.1 z.2, map_zero]

    obtain ⟨hh, hhdef⟩ : ∃ hh : DoubleComplex.Tot (LerayDblCpx (𝟙 X) π 𝔓 𝒲) n, ∀ (a b : ℕ) (hab : a + b = n) (σ : 𝔓.Idx a) (τ : 𝒲.Idx b),
        hh ⟨(a, b), hab⟩ (σ, τ) = ((-1 : ℤ) ^ a) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hle_cat σ τ (n + 1) (by omega))
          ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ τ (n + 2) (by omega))) :=
      ⟨fun i στ => ((-1 : ℤ) ^ i.1.1) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hle_cat στ.1 στ.2 (n + 1) (by have := i.2; omega))
          ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam στ.1 στ.2 (n + 2) (by have := i.2; omega))),
        fun _ _ _ _ _ => rfl⟩
    refine ⟨hh, ?_⟩
    have map_hh : ∀ (a b : ℕ) (hab : a + b = n) (σ : 𝔓.Idx a) (τ : 𝒲.Idx b) {U : X.Opens}
        (hU : U ≤ biOpen (𝟙 X) 𝔓 𝒲 a b σ τ),
        (X.presheaf.map (homOfLE hU).op).hom (hh ⟨(a, b), hab⟩ (σ, τ)) =
          ((-1 : ℤ) ^ a) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hU.trans (hle_cat σ τ (n + 1) (by omega)))
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ τ (n + 2) (by omega))) := by
      intro a b hab σ τ U hU
      rw [hhdef]
      show (OModulePresheaf.unit (𝟙 X ≫ π)).res hU (((-1 : ℤ) ^ a) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hle_cat σ τ (n + 1) (by omega))
        ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ τ (n + 2) (by omega)))) = _
      rw [map_zsmul, OModulePresheaf.res_res]

    have hsq : ∀ m : ℕ, ((-1 : ℤ) ^ m) * ((-1 : ℤ) ^ m) = 1 := fun m => by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    have hpq' : p + q = n + 1 := by simpa using hpq
    funext στ
    change BiIdx 𝔓 𝒲 p q at στ
    obtain ⟨σ', τ'⟩ := στ
    rw [Pi.sub_apply]
    erw [Pi.sub_apply]

    have hc := hcoc _ hζ (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (hle_cat σ' τ' (n + 2) (by omega))
    rcases p with _ | p' <;> rcases q with _ | q'
    · exact absurd hpq (by simp)
    ·
      obtain rfl : n = q' := by omega
      have hne : (⟨(0, n + 1), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(n + 1, 0), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.1) h; simp at this
      rw [DoubleComplex.dTot_apply_zero_succ, Pi.single_eq_same, Pi.single_eq_of_ne hne]
      erw [Pi.zero_apply, sub_zero]
      rw [biAug_apply, hpb]

      have e0 : 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) 0 = lam ∘ τ'.1 := oface_cat_zero 𝔓 𝒲 lam σ' τ' (by omega)
      have es : ∀ j : Fin (n + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) j.succ =
          cat 𝔓 𝒲 lam σ' (𝒲.face τ' j) (n + 2) (by omega) := by
        intro j
        rw [← oface_cat_right 𝔓 𝒲 lam σ' τ' (by omega) j (by omega)]
        congr 1
        exact Fin.ext (by simp [Fin.val_succ]; omega)
      have h0' : biOpen (𝟙 X) 𝔓 𝒲 0 (n + 1) σ' τ' ≤ 𝔓.ointer (lam ∘ τ'.1) :=
        (inf_le_left.trans (𝒲.ointer_le_preimage_ointer_comp (𝟙 X) 𝔓 lam hlam τ'.1)).trans (Scheme.Hom.id_preimage _).le
      have hs' : ∀ j : Fin (n + 2), biOpen (𝟙 X) 𝔓 𝒲 0 (n + 1) σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam σ' (𝒲.face τ' j) (n + 2) (by omega)) := fun j =>
        (inf_le_inf_right _ (𝒲.inter_le_inter_face τ' j)).trans (hle_cat σ' (𝒲.face τ' j) (n + 1) (by omega))
      have hc' : (OModulePresheaf.unit (𝟙 X ≫ π)).res h0' ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (lam ∘ τ'.1)) +
          ∑ j : Fin (n + 2), -(((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' j) (n + 2) (by omega)))) = 0 := by
        rw [Fin.sum_univ_succ] at hc
        rw [← hc]
        congr 1
        · rw [Fin.val_zero, pow_zero, one_smul]; exact resc _ _ _ e0.symm _ _
        · exact Finset.sum_congr rfl fun j _ => by
            rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]; congr 2; exact resc _ _ _ (es j).symm _ _
      rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at hc'
      show dV (𝟙 X) π 𝔓 𝒲 0 n (hh ⟨(0, n), by omega⟩) (σ', τ') = _
      rw [dV_apply']
      simp only [map_hh, pow_zero, one_smul]
      show _ = (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ _)
      rw [OModulePresheaf.res_res]
      exact hc'.symm
    ·
      obtain rfl : n = p' := by omega
      have hne : (⟨(n + 1, 0), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(0, n + 1), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.2) h; simp at this
      rw [DoubleComplex.dTot_apply_succ_zero, Pi.single_eq_of_ne hne, Pi.single_eq_same]
      erw [Pi.zero_apply, zero_sub]
      rw [hzσ z.1 σ']
      have eL : 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (Fin.last (n + 2)) = σ'.1 :=
        oface_cat_last 𝔓 𝒲 lam σ' τ' (by omega)
      have ec : ∀ j : Fin (n + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (Fin.castSucc j) =
          cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega) := fun j =>
        oface_cat_left 𝔓 𝒲 lam σ' τ' (by omega) j (by omega)
      have hL' : biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 σ' τ' ≤ 𝔓.ointer σ'.1 := inf_le_right.trans (Scheme.Hom.id_preimage _).le
      have hs' : ∀ j : Fin (n + 2), biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega)) := fun j =>
        (inf_le_inf_left _ (Scheme.Hom.preimage_mono (𝟙 X) (𝔓.inter_le_inter_face σ' j))).trans
          (hle_cat (𝔓.face σ' j) τ' (n + 1) (by omega))
      have hc' : ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega))) +
          ((-1 : ℤ) ^ n) • (OModulePresheaf.unit (𝟙 X ≫ π)).res hL' ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 σ'.1) = 0 := by
        rw [Fin.sum_univ_castSucc] at hc
        rw [← hc]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by
            rw [Fin.val_castSucc]; congr 1; exact resc _ _ _ (ec j).symm _ _
        · rw [Fin.val_last, pow_succ, pow_succ, mul_neg_one, mul_neg_one, neg_neg]; congr 1
          exact resc _ _ _ eL.symm _ _
      rw [← eq_neg_iff_add_eq_zero] at hc'
      show dH (𝟙 X) π 𝔓 𝒲 n 0 (hh ⟨(n, 0), by omega⟩) (σ', τ') = _
      rw [dH_apply']
      simp only [map_hh]
      have key : ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ n) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega)))) =
          -((OModulePresheaf.unit (𝟙 X ≫ π)).res hL' ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 σ'.1)) := by
        rw [show (∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ n) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega))))) =
            ((-1 : ℤ) ^ n) • ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hs' j) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' j) τ' (n + 2) (by omega))) from by
              rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _,
          hc', smul_neg, smul_smul, hsq, one_smul]
      exact key
    ·
      have hne0 : (⟨(p' + 1, q' + 1), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(0, n + 1), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.1) h; simp at this
      have hne1 : (⟨(p' + 1, q' + 1), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(n + 1, 0), by omega⟩ := fun h => by
        have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.2) h; simp at this
      rw [DoubleComplex.dTot_apply_succ_succ, Pi.single_eq_of_ne hne0, Pi.single_eq_of_ne hne1]
      erw [Pi.zero_apply, sub_zero, Pi.add_apply, Pi.smul_apply]

      let e : Fin (p' + 2) ⊕ Fin (q' + 2) ≃ Fin (n + 3) := finSumFinEquiv.trans (finCongr (by omega))
      have he_inl : ∀ x : Fin (p' + 2), ((e (Sum.inl x) : Fin (n + 3)) : ℕ) = x := fun x => by simp [e]
      have he_inr : ∀ y : Fin (q' + 2), ((e (Sum.inr y) : Fin (n + 3)) : ℕ) = p' + 2 + y := fun y => by simp [e]
      have ecL : ∀ x : Fin (p' + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (e (Sum.inl x)) =
          cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega) := fun x =>
        (congrArg (𝔓.oface _) (Fin.ext (he_inl x))).trans (oface_cat_left 𝔓 𝒲 lam σ' τ' (by omega) x (by omega))
      have ecR : ∀ y : Fin (q' + 2), 𝔓.oface (cat 𝔓 𝒲 lam σ' τ' (n + 3) (by omega)) (e (Sum.inr y)) =
          cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega) := fun y =>
        (congrArg (𝔓.oface _) (Fin.ext (show ((e (Sum.inr y) : Fin (n + 3)) : ℕ) = p' + 1 + 1 + y by
          have := he_inr y; omega))).trans (oface_cat_right 𝔓 𝒲 lam σ' τ' (by omega) y (by omega))
      have hsL : ∀ x : Fin (p' + 2), biOpen (𝟙 X) 𝔓 𝒲 (p' + 1) (q' + 1) σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega)) := fun x =>
        (inf_le_inf_left _ (Scheme.Hom.preimage_mono (𝟙 X) (𝔓.inter_le_inter_face σ' x))).trans
          (hle_cat (𝔓.face σ' x) τ' (n + 1) (by omega))
      have hsR : ∀ y : Fin (q' + 2), biOpen (𝟙 X) 𝔓 𝒲 (p' + 1) (q' + 1) σ' τ' ≤
          𝔓.ointer (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega)) := fun y =>
        (inf_le_inf_right _ (𝒲.inter_le_inter_face τ' y)).trans (hle_cat σ' (𝒲.face τ' y) (n + 1) (by omega))

      have hc' : ∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega))) +
          ((-1 : ℤ) ^ p') • ∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y)
            ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega))) = 0 := by
        rw [← e.sum_comp, Fintype.sum_sum_type] at hc
        rw [← hc]
        congr 1
        · exact Finset.sum_congr rfl fun x _ => by rw [he_inl]; congr 1; exact resc _ _ _ (ecL x).symm _ _
        · rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => by
            rw [smul_smul, he_inr]
            congr 1
            · rw [show p' + 2 + (y : ℕ) = (p' + (y : ℕ)) + 2 by omega, pow_add, pow_add, neg_one_sq, mul_one]
            · exact resc _ _ _ (ecR y).symm _ _
      rw [← eq_neg_iff_add_eq_zero] at hc'
      show dH (𝟙 X) π 𝔓 𝒲 p' (q' + 1) (hh ⟨(p', q' + 1), by omega⟩) (σ', τ') +
          ((-1 : ℤ) ^ (p' + 1)) • dV (𝟙 X) π 𝔓 𝒲 (p' + 1) q' (hh ⟨(p' + 1, q'), by omega⟩) (σ', τ') = 0
      rw [dH_apply', dV_apply']
      simp only [map_hh]
      have key : ∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (((-1 : ℤ) ^ p') • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega)))) +
          ((-1 : ℤ) ^ (p' + 1)) • ∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (((-1 : ℤ) ^ (p' + 1)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega)))) = 0 := by
        rw [show (∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (((-1 : ℤ) ^ p') • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega))))) =
            ((-1 : ℤ) ^ p') • ∑ x : Fin (p' + 2), ((-1 : ℤ) ^ (x : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsL x) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam (𝔓.face σ' x) τ' (n + 2) (by omega))) from by
              rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _,
          show (∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (((-1 : ℤ) ^ (p' + 1)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega))))) =
            ((-1 : ℤ) ^ (p' + 1)) • ∑ y : Fin (q' + 2), ((-1 : ℤ) ^ (y : ℕ)) • (OModulePresheaf.unit (𝟙 X ≫ π)).res (hsR y) ((OModulePresheaf.unit (𝟙 X ≫ π)).oext 𝔓 (n + 1) z.1 (cat 𝔓 𝒲 lam σ' (𝒲.face τ' y) (n + 2) (by omega))) from by
              rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _,
          hc', smul_neg, smul_smul, smul_smul, hsq, hsq, one_smul, neg_add_cancel]
      exact key

end S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id (solution)
