-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:13.545244+00:00
-- url     : https://prove2.me/theorems/c889fa2a-f27a-4459-b25e-62593f6301a2
-- title:
--   Prod Iso
-- statement:
--   Definitions and structural lemmas for Prod Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
section TU
variable {X Y Z : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (u : ∀ p, Γ(X, U p)ˣ)
def tu (V : Y.Opens) (ψ : Y ⟶ X) (p : ι) : Γ(Y, V)ˣ :=
  @dite _ (V ≤ ψ ⁻¹ᵁ U p) (Classical.dec _) (fun h => res h (pullU ψ _ (u p))) (fun _ => 1)
variable {U u}
lemma rs_rs' {T : Scheme.{0}} {O1 O2 O3 : T.Opens} (h1 : O2 ≤ O1) (h2 : O3 ≤ O2)
    (x : Γ(T, O1)) : rs h2 (rs h1 x) = rs (h2.trans h1) x := by
  first
    | (simp only [rs]; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
    | (change _ = (T.presheaf.map ((homOfLE h1).op ≫ (homOfLE h2).op)).hom x
       rw [Functor.map_comp]; rfl)
lemma res_res_eq_res_trans' {T : Scheme.{0}} {O1 O2 O3 : T.Opens} (h1 : O2 ≤ O1) (h2 : O3 ≤ O2)
    (z : Γ(T, O1)ˣ) : res h2 (res h1 z) = res (h2.trans h1) z := by
  ext1
  exact rs_rs' h1 h2 (z : Γ(T, O1))
lemma app_rs_eq_rs_app' {T S : Scheme.{0}} (f : S ⟶ T) {O1 O2 : T.Opens} (e : O2 ≤ O1)
    (x : Γ(T, O1)) :
    (f.app O2).hom (rs e x) = rs (leOfHom ((Opens.map f.base).map (homOfLE e))) ((f.app O1).hom x) := by
  have h1 := congrArg (fun g => g.hom x) (f.naturality (homOfLE e).op)
  exact h1
lemma pullU_res_eq_res_map_homOfLE {T S : Scheme.{0}} (f : S ⟶ T) {O1 O2 : T.Opens} (e : O2 ≤ O1)
    (z : Γ(T, O1)ˣ) :
    pullU f O2 (res e z) = res (leOfHom ((Opens.map f.base).map (homOfLE e))) (pullU f O1 z) := by
  ext1
  exact app_rs_eq_rs_app' f e (z : Γ(T, O1))
end TU
section TrPull
variable {X Y Z : Scheme.{0}} (L : LB X)
end TrPull
section IsoUnits
variable {X Y : Scheme.{0}} {L M : LB X}
abbrev wu (w : LB.Iso L M) (V : Y.Opens) (ψ : Y ⟶ X) (a : M.ι) (b : L.ι) : Γ(Y, V)ˣ :=
  tu (LB.div M L).U w.s V ψ (a, b)
lemma preimage_le_preimage_of_le {T S : Scheme.{0}} (f : S ⟶ T) {O1 O2 : T.Opens} (e : O2 ≤ O1) :
    f ⁻¹ᵁ O2 ≤ f ⁻¹ᵁ O1 := leOfHom ((Opens.map f.base).map (homOfLE e))
end IsoUnits
section LinCombIsoGen
variable {X Y : Scheme.{0}} {L M : LB X}
lemma res_linComb_g_eq_prod_tr_zpow (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a b : K → L.ι) {V : Y.Opens} (h : V ≤ LB.wchart L φ a ⊓ LB.wchart L φ b) :
    res h ((LB.LinComb L φ ε).g a b) = ∏ k, tr L V (φ k) (a k) (b k) ^ ε k := by
  refine (map_prod (res h) _ Finset.univ).trans (Finset.prod_congr rfl (fun k _ => ?_))
  refine (map_zpow (res h) _ (ε k)).trans ?_
  congr 1
  have c : V ≤ φ k ⁻¹ᵁ (L.U (a k) ⊓ L.U (b k)) :=
    h.trans (le_inf (inf_le_left.trans (LB.wchart_le L φ a k)) (inf_le_right.trans (LB.wchart_le L φ b k)))
  refine (res_res_eq_res_trans' _ _ _).trans ?_
  simp only [tr, dif_pos c]
  all_goals exact rfl
end LinCombIsoGen
section SecIso
variable {Y : Scheme.{0}} {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B)
lemma g_self_res (hA : A.IsLB) (a : A.ι) {V : Y.Opens} (h : V ≤ A.U a ⊓ A.U a) : res h (A.g a a) = 1 := by
  have h1 := congrArg (res (h.trans inf_le_left)) (hA.g_self a)
  rw [res_res_eq_res_trans', map_one] at h1
  exact h1
lemma divLe (a : A.ι) (b : B.ι) : A.U a ⊓ B.U b ≤ (LB.div B A).U (b, a) := by
  first
    | exact le_inf inf_le_right inf_le_left
    | (show A.U a ⊓ B.U b ≤ B.U b ⊓ A.U a; exact le_inf inf_le_right inf_le_left)
def isoCand (a : A.ι) (b : B.ι) : Γ(Y, A.U a ⊓ B.U b) :=
  (((res (divLe a b) (u.s (b, a)))⁻¹ : Γ(Y, A.U a ⊓ B.U b)ˣ) : Γ(Y, A.U a ⊓ B.U b)) *
    rs (inf_le_right : A.U a ⊓ B.U b ≤ B.U b) (t.f b)
lemma isoCand_rs (a : A.ι) (b : B.ι) {V : Y.Opens} (hV : V ≤ A.U a ⊓ B.U b) :
    rs hV (isoCand u t a b) = (((res (hV.trans (divLe a b)) (u.s (b, a)))⁻¹ : Γ(Y, V)ˣ) : Γ(Y, V)) *
      rs (hV.trans inf_le_right) (t.f b) := by
  have hm : ∀ x y : Γ(Y, A.U a ⊓ B.U b), rs hV (x * y) = rs hV x * rs hV y :=
    fun x y => map_mul _ x y
  have e : res hV ((res (divLe a b) (u.s (b, a)))⁻¹) = (res (hV.trans (divLe a b)) (u.s (b, a)))⁻¹ := by
    rw [map_inv, res_res_eq_res_trans']
  unfold isoCand
  rw [hm, rs_rs']
  congr 1
  exact congrArg Units.val e
variable {u}
lemma res_trans_eq_mul_of_res_eq_one_right {T : Scheme.{0}} {O P Q R S' W : T.Opens}
    (hP : O ≤ P) (hQ : O ≤ Q) (hR : O ≤ R) (hS : O ≤ S') (hW : W ≤ O)
    (s : Γ(T, P)ˣ) (m : Γ(T, Q)ˣ) (l : Γ(T, R)ˣ) (s' : Γ(T, S')ˣ)
    (H : res hP s = res hQ m * (res hR l)⁻¹ * res hS s')
    (hl : res (hW.trans hR) l = 1) :
    res (hW.trans hP) s = res (hW.trans hQ) m * res (hW.trans hS) s' := by
  have H2 := congrArg (res hW) H
  simp only [map_mul, map_inv, res_res_eq_res_trans', hl, inv_one, mul_one] at H2
  exact H2
lemma rs_trans_eq_res_mul_rs_of_rs_eq {T : Scheme.{0}} {P Q R W : T.Opens} (hP : Q ≤ P) (hR : Q ≤ R) (hW : W ≤ Q)
    (x : Γ(T, P)) (g : Γ(T, Q)ˣ) (y : Γ(T, R))
    (H : rs hP x = (g : Γ(T, Q)) * rs hR y) :
    rs (hW.trans hP) x = ((res hW g : Γ(T, W)ˣ) : Γ(T, W)) * rs (hW.trans hR) y := by
  have hm : ∀ p q : Γ(T, Q), rs hW (p * q) = rs hW p * rs hW q := fun p q => map_mul _ p q
  have H2 := congrArg (rs hW) H
  rw [rs_rs', hm, rs_rs'] at H2
  exact H2
lemma isoCand_compat (hu : u.IsGen) (hA : A.IsLB) (a : A.ι) (b b' : B.ι) :
    rs (inf_le_left : (A.U a ⊓ B.U b) ⊓ (A.U a ⊓ B.U b') ≤ _) (isoCand u t a b) =
      rs (inf_le_right : (A.U a ⊓ B.U b) ⊓ (A.U a ⊓ B.U b') ≤ _) (isoCand u t a b') := by
  have hWD : (A.U a ⊓ B.U b) ⊓ (A.U a ⊓ B.U b') ≤ (LB.div B A).U (b, a) ⊓ (LB.div B A).U (b', a) :=
    le_inf (inf_le_left.trans (le_inf inf_le_right inf_le_left))
      (inf_le_right.trans (le_inf inf_le_right inf_le_left))
  have hWB : (A.U a ⊓ B.U b) ⊓ (A.U a ⊓ B.U b') ≤ B.U b ⊓ B.U b' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have HU := res_trans_eq_mul_of_res_eq_one_right (O := (LB.div B A).U (b, a) ⊓ (LB.div B A).U (b', a)) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) inf_le_right hWD
    (u.s (b, a)) (B.g b b') (A.g a a) (u.s (b', a)) (hu (b, a) (b', a)) (g_self_res hA a _)
  have HT := rs_trans_eq_res_mul_rs_of_rs_eq inf_le_left inf_le_right hWB (t.f b) (B.g b b') (t.f b') (t.compat b b')
  refine (isoCand_rs u t a b inf_le_left).trans (Eq.trans ?_ (isoCand_rs u t a b' inf_le_right).symm)
  rw [HU, HT, mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
lemma cover_inf (hB : B.IsLB) (a : A.ι) : A.U a ≤ ⨆ b, A.U a ⊓ B.U b := by
  calc A.U a = A.U a ⊓ ⨆ b, B.U b := by rw [hB.cover, inf_top_eq]
    _ ≤ ⨆ b, A.U a ⊓ B.U b := (inf_iSup_eq _ _).le
def secOfIsoF (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) (a : A.ι) : Γ(Y, A.U a) :=
  Classical.choose (sec_glue (A.U a) (fun b => A.U a ⊓ B.U b) (fun _ => inf_le_left) (cover_inf hB a)
    (isoCand u t a) (fun b b' => isoCand_compat t hu hA a b b'))
lemma secOfIsoF_spec (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) (a : A.ι) (b : B.ι) :
    rs (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) (secOfIsoF t hu hA hB a) = isoCand u t a b :=
  (Classical.choose_spec (sec_glue (A.U a) (fun b => A.U a ⊓ B.U b) (fun _ => inf_le_left)
    (cover_inf hB a) (isoCand u t a) (fun b b' => isoCand_compat t hu hA a b b'))).1 b
lemma inf_le_iSup_inf_cover (hB : B.IsLB) (a a' : A.ι) : A.U a ⊓ A.U a' ≤ ⨆ b, (A.U a ⊓ A.U a') ⊓ B.U b := by
  calc A.U a ⊓ A.U a' = (A.U a ⊓ A.U a') ⊓ ⨆ b, B.U b := by rw [hB.cover, inf_top_eq]
    _ ≤ ⨆ b, (A.U a ⊓ A.U a') ⊓ B.U b := (inf_iSup_eq _ _).le
set_option maxHeartbeats 1000000 in
lemma res_trans_eq_inv_mul_of_res_eq_one_left {T : Scheme.{0}} {O P Q R S' W : T.Opens}
    (hP : O ≤ P) (hQ : O ≤ Q) (hR : O ≤ R) (hS : O ≤ S') (hW : W ≤ O)
    (s : Γ(T, P)ˣ) (m : Γ(T, Q)ˣ) (l : Γ(T, R)ˣ) (s' : Γ(T, S')ˣ)
    (H : res hP s = res hQ m * (res hR l)⁻¹ * res hS s')
    (hm : res (hW.trans hQ) m = 1) :
    res (hW.trans hP) s = (res (hW.trans hR) l)⁻¹ * res (hW.trans hS) s' := by
  have H2 := congrArg (res hW) H
  simp only [map_mul, map_inv, res_res_eq_res_trans', hm, one_mul] at H2
  exact H2
lemma secOfIsoF_compat (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) (a a' : A.ι) :
    rs (inf_le_left : A.U a ⊓ A.U a' ≤ A.U a) (secOfIsoF t hu hA hB a) =
      ((A.g a a' : Γ(Y, A.U a ⊓ A.U a')ˣ) : Γ(Y, A.U a ⊓ A.U a')) *
        rs (inf_le_right : A.U a ⊓ A.U a' ≤ A.U a') (secOfIsoF t hu hA hB a') := by
  have hF : ∀ (a0 : A.ι) (b0 : B.ι) {Vv : Y.Opens} (hv : Vv ≤ A.U a0 ⊓ B.U b0),
      rs (hv.trans inf_le_left) (secOfIsoF t hu hA hB a0) =
        (((res (hv.trans (divLe a0 b0)) (u.s (b0, a0)))⁻¹ : Γ(Y, Vv)ˣ) : Γ(Y, Vv)) *
          rs (hv.trans inf_le_right) (t.f b0) := by
    intro a0 b0 Vv hv
    rw [← rs_rs' (inf_le_left : A.U a0 ⊓ B.U b0 ≤ A.U a0) hv, secOfIsoF_spec t hu hA hB a0 b0]
    exact isoCand_rs u t a0 b0 hv
  have key : ∀ b, rs (inf_le_left : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ A.U a')
      (((A.g a a' : Γ(Y, A.U a ⊓ A.U a')ˣ) : Γ(Y, A.U a ⊓ A.U a')) *
        rs (inf_le_right : A.U a ⊓ A.U a' ≤ A.U a') (secOfIsoF t hu hA hB a')) =
      rs (inf_le_left : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ A.U a')
        (rs (inf_le_left : A.U a ⊓ A.U a' ≤ A.U a) (secOfIsoF t hu hA hB a)) := by
    intro b
    have hv1 : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ B.U b := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hv2 : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a' ⊓ B.U b := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hWO : (A.U a ⊓ A.U a') ⊓ B.U b ≤ (LB.div B A).U (b, a) ⊓ (LB.div B A).U (b, a') :=
      le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
        (le_inf inf_le_right (inf_le_left.trans inf_le_right))
    have HU := res_trans_eq_inv_mul_of_res_eq_one_left (O := (LB.div B A).U (b, a) ⊓ (LB.div B A).U (b, a')) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) inf_le_right hWO
      (u.s (b, a)) (B.g b b) (A.g a a') (u.s (b, a')) (hu (b, a) (b, a')) (g_self_res hB b _)
    have hm : ∀ p q : Γ(Y, A.U a ⊓ A.U a'),
        rs (inf_le_left : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ A.U a') (p * q) =
          rs inf_le_left p * rs inf_le_left q := fun p q => map_mul _ p q
    have hval : rs (inf_le_left : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ A.U a')
        ((A.g a a' : Γ(Y, A.U a ⊓ A.U a')ˣ) : Γ(Y, A.U a ⊓ A.U a')) =
        ((res (inf_le_left : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ A.U a') (A.g a a') :
          Γ(Y, (A.U a ⊓ A.U a') ⊓ B.U b)ˣ) : Γ(Y, (A.U a ⊓ A.U a') ⊓ B.U b)) := rfl
    rw [hm, hval, rs_rs', rs_rs', hF a b hv1, hF a' b hv2, HU]
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    ring
  obtain ⟨g, -, huniq⟩ := sec_glue (A.U a ⊓ A.U a') (fun b => (A.U a ⊓ A.U a') ⊓ B.U b)
    (fun _ => inf_le_left) (inf_le_iSup_inf_cover hB a a')
    (fun b => rs (inf_le_left : (A.U a ⊓ A.U a') ⊓ B.U b ≤ A.U a ⊓ A.U a')
      (rs (inf_le_left : A.U a ⊓ A.U a' ≤ A.U a) (secOfIsoF t hu hA hB a)))
    (fun b b' => by
      first
        | (simp only [rs_rs']; done)
        | (simp only [rs_rs']; rfl)
        | rfl)
  exact (huniq (rs (inf_le_left : A.U a ⊓ A.U a' ≤ A.U a) (secOfIsoF t hu hA hB a)) (fun b => rfl)).trans
    (huniq (((A.g a a' : Γ(Y, A.U a ⊓ A.U a')ˣ) : Γ(Y, A.U a ⊓ A.U a')) *
      rs (inf_le_right : A.U a ⊓ A.U a' ≤ A.U a') (secOfIsoF t hu hA hB a')) key).symm
def secOfIso (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) : LB.Sec A where
  f a := secOfIsoF t hu hA hB a
  compat a a' := secOfIsoF_compat t hu hA hB a a'
end SecIso
section BoxSec
variable {X X' : Scheme.{0}} (L : LB X) {j : ℕ} (pr : Fin j → (X' ⟶ X)) (k : ℤ)
lemma box_le_pr (jN : Fin 1 → (Fin j → L.ι)) (i : Fin j) :
    LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN ≤
      pr i ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => jN 0 i) := by
  intro x hx
  have h2 : (pr i).base x ∈ (L.U (jN 0 i) : Set X) :=
    Set.mem_iInter.mp (Set.mem_iInter.mp hx 0) i
  exact Set.mem_iInter.mpr (fun _ => h2)
def boxSecF (σ : Fin j → LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k)))
    (jN : Fin 1 → (Fin j → L.ι)) :
    Γ(X', LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN) :=
  ∏ i, rs (box_le_pr L pr jN i) (((pr i).app _).hom ((σ i).f (fun _ => jN 0 i)))
set_option maxHeartbeats 1000000 in
lemma res_pullU_res_pullU_id {T S : Scheme.{0}} (h : S ⟶ T) {O Q : T.Opens} {W : S.Opens}
    (e : O ≤ (𝟙 T) ⁻¹ᵁ Q) (hW : W ≤ h ⁻¹ᵁ O) (c : W ≤ h ⁻¹ᵁ Q) (z : Γ(T, Q)ˣ) :
    res hW (pullU h O (res e (pullU (𝟙 T) Q z))) = res c (pullU h Q z) := by
  rw [pullU_res_eq_res_map_homOfLE, res_res_eq_res_trans']
  first
    | rfl
    | (ext1; rfl)
    | (ext1; simp [res, pullU, Scheme.id_app])
lemma linComb_fin_one_g (L : LB X) (k : ℤ) (a b : Fin 1 → L.ι) :
    (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k)).g a b =
      (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => 𝟙 X) a 0))
        (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => 𝟙 X) b 0)))
        (pullU (𝟙 X) _ (L.g (a 0) (b 0)))) ^ k := by
  first
    | (unfold LB.LinComb; exact Fin.prod_univ_one _)
    | (simp only [LB.LinComb, Fin.prod_univ_one]; done)
    | (simp only [LB.LinComb, Fin.prod_univ_one]; rfl)
lemma res_pullU_id_eq_res {T : Scheme.{0}} {Q W : T.Opens} (c : W ≤ (𝟙 T) ⁻¹ᵁ Q) (z : Γ(T, Q)ˣ) :
    res c (pullU (𝟙 T) Q z) = res (c : W ≤ Q) z := by
  first
    | rfl
    | (ext1; rfl)
    | (ext1; simp [res, pullU, Scheme.id_app])
lemma res_zpow_res_pullU_id {T : Scheme.{0}} {O Q V : T.Opens} (hV : V ≤ O) (e : O ≤ (𝟙 T) ⁻¹ᵁ Q)
    (c : V ≤ Q) (z : Γ(T, Q)ˣ) (k : ℤ) :
    res hV ((res e (pullU (𝟙 T) Q z)) ^ k) = (res c z) ^ k := by
  rw [map_zpow, res_res_eq_res_trans', res_pullU_id_eq_res]
  all_goals rfl
lemma box_g_res (jN jN' : Fin 1 → (Fin j → L.ι)) {V : X'.Opens}
    (h : V ≤ LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN ⊓
      LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN') :
    res h ((LB.LinComb (LB.LinComb L pr (fun _ => 1)) (K := Fin 1) (fun _ => 𝟙 X') (fun _ => k)).g jN jN') =
      ∏ i, tr L V (pr i) (jN 0 i) (jN' 0 i) ^ k := by
  have c0 : V ≤ LB.wchart L pr (jN 0) ⊓ LB.wchart L pr (jN' 0) :=
    h.trans (le_inf
      (inf_le_left.trans (LB.wchart_le (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN 0))
      (inf_le_right.trans (LB.wchart_le (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN' 0)))
  refine (congrArg (res h) (linComb_fin_one_g (LB.LinComb L pr (fun _ => 1)) k jN jN')).trans ?_
  refine (res_zpow_res_pullU_id h _ c0 _ k).trans ?_
  refine (congrArg (· ^ k) (res_linComb_g_eq_prod_tr_zpow L pr (fun _ => 1) (jN 0) (jN' 0) c0)).trans ?_
  simp only [zpow_one, Finset.prod_zpow]
set_option maxHeartbeats 1000000 in
lemma g_pull_one {Z : Scheme.{0}} (h : Z ⟶ X) (a b : Fin 1 → L.ι) {W : Z.Opens}
    (hW : W ≤ h ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => 𝟙 X) a ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) b)) :
    res hW (pullU h _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k)).g a b)) =
      tr L W h (a 0) (b 0) ^ k := by
  have c : W ≤ h ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
    hW.trans (preimage_le_preimage_of_le h (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => 𝟙 X) a 0))
      (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => 𝟙 X) b 0))))
  have e3 : tr L W h (a 0) (b 0) = res c (pullU h _ (L.g (a 0) (b 0))) := by
    unfold tr
    exact dif_pos c
  refine (congrArg (fun z => res hW (pullU h _ z)) (linComb_fin_one_g L k a b)).trans ?_
  refine (congrArg (res hW) (map_zpow (pullU h _) _ k)).trans ((map_zpow (res hW) _ k).trans ?_)
  congr 1
  exact (res_pullU_res_pullU_id h _ hW c _).trans e3.symm
set_option maxHeartbeats 1000000 in
lemma boxSecF_compat (σ : Fin j → LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k)))
    (jN jN' : Fin 1 → (Fin j → L.ι)) :
    rs (inf_le_left : LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN ⊓
        LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN' ≤
        LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN) (boxSecF L pr k σ jN) =
      @Units.val (Γ(X', LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN ⊓
            LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN')) _
          ((LB.LinComb (LB.LinComb L pr (fun _ => 1)) (K := Fin 1) (fun _ => 𝟙 X') (fun _ => k)).g jN jN') *
        rs (inf_le_right : LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN ⊓
          LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN' ≤
          LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN') (boxSecF L pr k σ jN') := by
  set W := LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN ⊓
    LB.wchart (LB.LinComb L pr (fun _ => 1)) (fun _ : Fin 1 => 𝟙 X') jN' with hWdef
  have hfac : ∀ i, rs (inf_le_left : W ≤ _) (rs (box_le_pr L pr jN i) (((pr i).app _).hom ((σ i).f (fun _ => jN 0 i)))) =
      ((tr L W (pr i) (jN 0 i) (jN' 0 i) ^ k : Γ(X', W)ˣ) : Γ(X', W)) *
        rs (inf_le_right : W ≤ _) (rs (box_le_pr L pr jN' i) (((pr i).app _).hom ((σ i).f (fun _ => jN' 0 i)))) :=
    fun i => app_compat_generic (pr i) (box_le_pr L pr jN i) (box_le_pr L pr jN' i) _ _ _ ((σ i).compat _ _) _
      (g_pull_one L k (pr i) (fun _ => jN 0 i) (fun _ => jN' 0 i) _).symm
  have hg := box_g_res L pr k jN jN' (le_refl W)
  erw [res_refl'] at hg
  simp only [boxSecF, map_prod]
  refine Eq.trans (Finset.prod_congr rfl (fun i _ => hfac i)) ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  erw [hg, Units.coe_prod]
def boxSec (σ : Fin j → LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k))) :
    LB.Sec (LB.LinComb (LB.LinComb L pr (fun _ => 1)) (K := Fin 1) (fun _ => 𝟙 X') (fun _ => k)) where
  f jN := boxSecF L pr k σ jN
  compat jN jN' := boxSecF_compat L pr k σ jN jN'
end BoxSec
end ReciprocityTheory.ChartRestriction.G.DVR


