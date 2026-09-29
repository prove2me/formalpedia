-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_inf_cocycle_of_face_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e23b68d8-e5d0-569b-a437-ade3cc537f7f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace B26

abbrev rO {Y : Scheme.{u}} {A B : Y.Opens} (h : B ≤ A) : Γ(Y, A) →+* Γ(Y, B) :=
  (Y.presheaf.map (homOfLE h).op).hom

theorem rO_rO {Y : Scheme.{u}} {A B C : Y.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(Y, A)) :
    rO hCB (rO hBA g) = rO (hCB.trans hBA) g := by
  change (Y.presheaf.map (homOfLE hBA).op ≫ Y.presheaf.map (homOfLE hCB).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rO_refl {Y : Scheme.{u}} {A : Y.Opens} (g : Γ(Y, A)) : rO (le_refl A) g = g := by
  change (Y.presheaf.map (homOfLE (le_refl A)).op).hom g = g
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, Y.presheaf.map_id]; rfl

variable {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)

def pr (a b : 𝒱.ι) (h : a < b) : 𝒱.Idx 1 :=
  ⟨![a, b], Fin.strictMono_iff_lt_succ.2 (by intro i; fin_cases i; simpa using h)⟩

def tr (a b c : 𝒱.ι) (hab : a < b) (hbc : b < c) : 𝒱.Idx 2 :=
  ⟨![a, b, c], Fin.strictMono_iff_lt_succ.2 (by
    intro i; fin_cases i
    · simpa using hab
    · simpa using hbc)⟩

theorem pr_val_zero (a b : 𝒱.ι) (h : a < b) : (pr 𝒱 a b h).1 0 = a := rfl
theorem pr_val_one (a b : 𝒱.ι) (h : a < b) : (pr 𝒱 a b h).1 1 = b := rfl

theorem le_inter_pr (a b : 𝒱.ι) (h : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    W ≤ 𝒱.inter (pr 𝒱 a b h) := by
  unfold Scheme.OrderedAffineCover.inter
  apply le_iInf; intro j; fin_cases j
  · exact ha
  · exact hb

theorem le_inter_tr (a b c : 𝒱.ι) (hab : a < b) (hbc : b < c) {W : Y.Opens} (ha : W ≤ 𝒱.U a)
    (hb : W ≤ 𝒱.U b) (hc : W ≤ 𝒱.U c) : W ≤ 𝒱.inter (tr 𝒱 a b c hab hbc) := by
  unfold Scheme.OrderedAffineCover.inter
  apply le_iInf; intro j; fin_cases j
  · exact ha
  · exact hb
  · exact hc

theorem face_tr_two (a b c : 𝒱.ι) (hab : a < b) (hbc : b < c) :
    𝒱.face (tr 𝒱 a b c hab hbc) 2 = pr 𝒱 a b hab := by
  apply Subtype.ext; funext i; fin_cases i <;> rfl

theorem face_tr_zero (a b c : 𝒱.ι) (hab : a < b) (hbc : b < c) :
    𝒱.face (tr 𝒱 a b c hab hbc) 0 = pr 𝒱 b c hbc := by
  apply Subtype.ext; funext i; fin_cases i <;> rfl

theorem face_tr_one (a b c : 𝒱.ι) (hab : a < b) (hbc : b < c) :
    𝒱.face (tr 𝒱 a b c hab hbc) 1 = pr 𝒱 a c (hab.trans hbc) := by
  apply Subtype.ext; funext i; fin_cases i <;> rfl

theorem pr_eq (s : 𝒱.Idx 1) : pr 𝒱 (s.1 0) (s.1 1) (s.2 (by decide)) = s := by
  apply Subtype.ext; funext i; fin_cases i <;> rfl

theorem res_congr {I : Type*} (O : I → Y.Opens) (x : ∀ s, Γ(Y, O s)) {s s' : I} (e : s = s')
    {W : Y.Opens} (h : W ≤ O s) (h' : W ≤ O s') : rO h (x s) = rO h' (x s') := by
  subst e; rfl

section cocycle

variable (u u' : ∀ s : 𝒱.Idx 1, Γ(Y, 𝒱.inter s)) (huu' : ∀ s : 𝒱.Idx 1, u s * u' s = 1)
  (hcoc : ∀ r : 𝒱.Idx 2,
    (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (u (𝒱.face r 2)) *
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (u (𝒱.face r 0)) =
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (u (𝒱.face r 1)))

def uW (a b : 𝒱.ι) (h : a < b) (W : Y.Opens) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) : Γ(Y, W) :=
  rO (le_inter_pr 𝒱 a b h ha hb) (u (pr 𝒱 a b h))

include hcoc in
theorem uW_mul_uW (a b c : 𝒱.ι) (hab : a < b) (hbc : b < c) (W : Y.Opens) (ha : W ≤ 𝒱.U a)
    (hb : W ≤ 𝒱.U b) (hc : W ≤ 𝒱.U c) :
    uW 𝒱 u a b hab W ha hb * uW 𝒱 u b c hbc W hb hc = uW 𝒱 u a c (hab.trans hbc) W ha hc := by
  have h := congrArg (rO (le_inter_tr 𝒱 a b c hab hbc ha hb hc)) (hcoc (tr 𝒱 a b c hab hbc))
  rw [map_mul] at h
  change rO _ (rO _ _) * rO _ (rO _ _) = rO _ (rO _ _) at h
  rw [rO_rO, rO_rO, rO_rO] at h
  unfold uW
  rw [res_congr 𝒱.inter u (face_tr_two 𝒱 a b c hab hbc) _ (le_inter_pr 𝒱 a b hab ha hb),
    res_congr 𝒱.inter u (face_tr_zero 𝒱 a b c hab hbc) _ (le_inter_pr 𝒱 b c hbc hb hc),
    res_congr 𝒱.inter u (face_tr_one 𝒱 a b c hab hbc) _ (le_inter_pr 𝒱 a c (hab.trans hbc) ha hc)] at h
  exact h

include huu' in
theorem uW_mul_u'W (a b : 𝒱.ι) (h : a < b) (W : Y.Opens) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    uW 𝒱 u a b h W ha hb * uW 𝒱 u' a b h W ha hb = 1 := by
  unfold uW
  rw [← map_mul, huu', map_one]

def θ (i j : 𝒱.ι) (W : Y.Opens) (hi : W ≤ 𝒱.U i) (hj : W ≤ 𝒱.U j) : Γ(Y, W) :=
  if h : i < j then uW 𝒱 u' i j h W hi hj else if h' : j < i then uW 𝒱 u j i h' W hj hi else 1

theorem rO_uW (a b : 𝒱.ι) (h : a < b) (W : Y.Opens) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b)
    {W' : Y.Opens} (hW : W' ≤ W) :
    rO hW (uW 𝒱 u a b h W ha hb) = uW 𝒱 u a b h W' (hW.trans ha) (hW.trans hb) := by
  unfold uW; rw [rO_rO]

theorem rO_θ (i j : 𝒱.ι) (W : Y.Opens) (hi : W ≤ 𝒱.U i) (hj : W ≤ 𝒱.U j) {W' : Y.Opens} (hW : W' ≤ W) :
    rO hW (θ 𝒱 u u' i j W hi hj) = θ 𝒱 u u' i j W' (hW.trans hi) (hW.trans hj) := by
  unfold θ
  split_ifs <;> first | exact rO_uW 𝒱 _ _ _ _ _ _ _ hW | exact map_one _

include huu' hcoc in
theorem θ_mul_θ (i j k : 𝒱.ι) (W : Y.Opens) (hi : W ≤ 𝒱.U i) (hj : W ≤ 𝒱.U j) (hk : W ≤ 𝒱.U k) :
    θ 𝒱 u u' i j W hi hj * θ 𝒱 u u' j k W hj hk = θ 𝒱 u u' i k W hi hk := by
  have T := uW_mul_uW 𝒱 u hcoc
  have I := uW_mul_u'W 𝒱 u u' huu'
  unfold θ
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j k with hjk | rfl | hkj
    ·
      have hik := hij.trans hjk
      rw [dif_pos hij, dif_pos hjk, dif_pos hik]
      have e := T i j k hij hjk W hi hj hk
      have e1 := I i j hij W hi hj
      have e2 := I j k hjk W hj hk
      have e3 := I i k hik W hi hk
      calc _ = uW 𝒱 u' i j hij W hi hj * uW 𝒱 u' j k hjk W hj hk *
            (uW 𝒱 u i k hik W hi hk * uW 𝒱 u' i k hik W hi hk) := by rw [e3, mul_one]
        _ = uW 𝒱 u' i j hij W hi hj * uW 𝒱 u' j k hjk W hj hk *
            (uW 𝒱 u i j hij W hi hj * uW 𝒱 u j k hjk W hj hk * uW 𝒱 u' i k hik W hi hk) := by rw [e]
        _ = (uW 𝒱 u i j hij W hi hj * uW 𝒱 u' i j hij W hi hj) *
            (uW 𝒱 u j k hjk W hj hk * uW 𝒱 u' j k hjk W hj hk) * uW 𝒱 u' i k hik W hi hk := by ring
        _ = _ := by rw [e1, e2, one_mul, one_mul]
    ·
      rw [dif_pos hij, dif_neg (lt_irrefl j), dif_neg (lt_irrefl j), mul_one]
    · rcases lt_trichotomy i k with hik | rfl | hki
      ·
        rw [dif_pos hij, dif_neg (not_lt_of_gt hkj), dif_pos hkj, dif_pos hik]
        have e := T i k j hik hkj W hi hk hj
        calc _ = uW 𝒱 u' i j hij W hi hj * uW 𝒱 u k j hkj W hk hj *
              (uW 𝒱 u i k hik W hi hk * uW 𝒱 u' i k hik W hi hk) := by rw [I i k hik W hi hk, mul_one]
          _ = (uW 𝒱 u i k hik W hi hk * uW 𝒱 u k j hkj W hk hj) * uW 𝒱 u' i j hij W hi hj *
              uW 𝒱 u' i k hik W hi hk := by ring
          _ = _ := by rw [e, I i j hij W hi hj, one_mul]
      ·
        rw [dif_pos hij, dif_neg (not_lt_of_gt hij), dif_pos hij, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i),
          mul_comm, I i j hij W hi hj]
      ·
        rw [dif_pos hij, dif_neg (not_lt_of_gt hkj), dif_pos hkj, dif_neg (not_lt_of_gt hki), dif_pos hki]
        have e := T k i j hki hij W hk hi hj
        calc _ = uW 𝒱 u' i j hij W hi hj * (uW 𝒱 u k i hki W hk hi * uW 𝒱 u i j hij W hi hj) := by rw [e]
          _ = _ := by rw [mul_comm, mul_assoc, I i j hij W hi hj, mul_one]
  ·
    rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i), one_mul]
  · rcases lt_trichotomy j k with hjk | rfl | hkj
    · rcases lt_trichotomy i k with hik | rfl | hki
      ·
        rw [dif_neg (not_lt_of_gt hji), dif_pos hji, dif_pos hjk, dif_pos hik]
        have e := T j i k hji hik W hj hi hk
        calc _ = uW 𝒱 u j i hji W hj hi * uW 𝒱 u' j k hjk W hj hk *
              (uW 𝒱 u i k hik W hi hk * uW 𝒱 u' i k hik W hi hk) := by rw [I i k hik W hi hk, mul_one]
          _ = (uW 𝒱 u j i hji W hj hi * uW 𝒱 u i k hik W hi hk) * uW 𝒱 u' j k hjk W hj hk *
              uW 𝒱 u' i k hik W hi hk := by ring
          _ = _ := by rw [e, I j k hjk W hj hk, one_mul]
      ·
        rw [dif_neg (not_lt_of_gt hji), dif_pos hji, dif_pos hji, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i),
          I j i hji W hj hi]
      ·
        rw [dif_neg (not_lt_of_gt hji), dif_pos hji, dif_pos hjk, dif_neg (not_lt_of_gt hki), dif_pos hki]
        have e := T j k i hjk hki W hj hk hi
        calc _ = uW 𝒱 u j k hjk W hj hk * uW 𝒱 u k i hki W hk hi * uW 𝒱 u' j k hjk W hj hk := by rw [e]
          _ = _ := by rw [mul_assoc, mul_comm (uW 𝒱 u k i hki W hk hi), ← mul_assoc, I j k hjk W hj hk, one_mul]
    ·
      rw [dif_neg (not_lt_of_gt hji), dif_pos hji, dif_neg (lt_irrefl j), dif_neg (lt_irrefl j), mul_one]
    ·
      have hki := hkj.trans hji
      rw [dif_neg (not_lt_of_gt hji), dif_pos hji, dif_neg (not_lt_of_gt hkj), dif_pos hkj,
        dif_neg (not_lt_of_gt hki), dif_pos hki, mul_comm]
      exact T k j i hkj hji W hk hj hi

include huu' hcoc in
theorem θ_mul_θ_swap (a b : 𝒱.ι) (W : Y.Opens) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    θ 𝒱 u u' a b W ha hb * θ 𝒱 u u' b a W hb ha = 1 := by
  rw [θ_mul_θ 𝒱 u u' huu' hcoc]
  unfold θ; rw [dif_neg (lt_irrefl a), dif_neg (lt_irrefl a)]

theorem θ_pair (s : 𝒱.Idx 1) (h0 : 𝒱.inter s ≤ 𝒱.U (s.1 0)) (h1 : 𝒱.inter s ≤ 𝒱.U (s.1 1)) :
    θ 𝒱 u u' (s.1 1) (s.1 0) (𝒱.inter s) h1 h0 = u s := by
  have hs : s.1 0 < s.1 1 := s.2 (by decide)
  unfold θ
  rw [dif_neg (not_lt_of_gt hs), dif_pos hs]
  unfold uW
  rw [res_congr 𝒱.inter u (pr_eq 𝒱 s) _ le_rfl]
  exact rO_refl _

end cocycle

end B26
end

theorem solution
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
    (u u' : ∀ s : 𝒱.Idx 1, Γ(Y, 𝒱.inter s)) (huu' : ∀ s : 𝒱.Idx 1, u s * u' s = 1)
    (hcoc : ∀ r : 𝒱.Idx 2,
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (u (𝒱.face r 2)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (u (𝒱.face r 0)) =
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (u (𝒱.face r 1))) :
    ∃ W : ∀ a b : 𝒱.ι, Γ(Y, 𝒱.U a ⊓ 𝒱.U b),
      (∀ a : 𝒱.ι, W a a = 1) ∧ (∀ a b : 𝒱.ι, IsUnit (W a b)) ∧
      (∀ a b c : 𝒱.ι,
        (Y.presheaf.map (homOfLE (inf_le_left : 𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U b)).op).hom (W a b) *
            (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U b ⊓ 𝒱.U c)).op).hom (W b c) =
          (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U c)).op).hom (W a c)) ∧
      (∀ s : 𝒱.Idx 1,
        (Y.presheaf.map (homOfLE (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1) :
          𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).op).hom (W (s.1 0) (s.1 1)) = u s) := by
  refine ⟨fun a b => B26.θ 𝒱 u u' b a (𝒱.U a ⊓ 𝒱.U b) inf_le_right inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro a
    show B26.θ 𝒱 u u' a a _ _ _ = 1
    unfold B26.θ; rw [dif_neg (lt_irrefl a), dif_neg (lt_irrefl a)]
  · intro a b
    show IsUnit (B26.θ 𝒱 u u' b a (𝒱.U a ⊓ 𝒱.U b) inf_le_right inf_le_left)
    exact IsUnit.of_mul_eq_one _ (B26.θ_mul_θ_swap 𝒱 u u' huu' hcoc b a (𝒱.U a ⊓ 𝒱.U b) inf_le_right inf_le_left)
  · intro a b c
    change B26.rO _ _ * B26.rO _ _ = B26.rO _ _
    rw [B26.rO_θ, B26.rO_θ, B26.rO_θ, mul_comm]
    exact B26.θ_mul_θ 𝒱 u u' huu' hcoc c b a _ _ _ _
  · intro s
    change B26.rO _ _ = _
    rw [B26.rO_θ]
    exact B26.θ_pair 𝒱 u u' s _ _

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle (solution)
