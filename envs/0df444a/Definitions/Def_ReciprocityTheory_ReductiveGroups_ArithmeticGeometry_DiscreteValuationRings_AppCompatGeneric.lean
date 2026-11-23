-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:58.621616+00:00
-- url     : https://prove2.me/theorems/597d666c-c896-4553-a9f3-1a31a02c304d
-- title:
--   App Compat Generic
-- statement:
--   Definitions and structural lemmas for App Compat Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/AppCompatGeneric.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
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
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
lemma app_rs (h : Z ⟶ Y) {U V : Y.Opens} (hle : V ≤ U) (x : Γ(Y, U)) :
    (h.app V).hom (rs hle x) = rs ((Opens.map h.base).monotone hle) ((h.app U).hom x) := by
  show (Y.presheaf.map (homOfLE hle).op ≫ h.app V).hom x =
    (h.app U ≫ Z.presheaf.map (homOfLE ((Opens.map h.base).monotone hle)).op).hom x
  rw [Scheme.Hom.naturality]
  rfl
lemma wchart_comp_le (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  intro z hz
  show h.base z ∈ (LB.wchart L φ j : Set Y)
  have hz' : z ∈ (LB.wchart L (fun k => h ≫ φ k) j : Set Z) := hz
  simp only [LB.wchart, TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage] at hz' ⊢
  intro k
  first
  | exact hz' k
  | simpa using hz' k
lemma res_pullU_comp' (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens} {V : Z.Opens}
    (hC : W ≤ ψ ⁻¹ᵁ U) (hB : V ≤ h ⁻¹ᵁ W) (hA : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res hA (pullU (h ≫ ψ) U x) = res hB (pullU h W (res hC (pullU ψ U x))) := by
  ext
  show ((h ≫ ψ).appLE U V hA).hom x.val = (h.appLE W V hB).hom ((ψ.appLE U W hC).hom x.val)
  rw [← CommRingCat.comp_apply]
  first
  | rw [Scheme.Hom.appLE_comp_appLE]
  | rw [Scheme.appLE_comp_appLE]
  | simp [Scheme.Hom.appLE_comp_appLE]
  | rfl
lemma prod_pull_generic (h : Z ⟶ Y) (ψ : K → (Y ⟶ X)) (a b : K → L.ι) (W : Y.Opens)
    (hW : ∀ k, W ≤ ψ k ⁻¹ᵁ (L.U (a k) ⊓ L.U (b k))) (V : Z.Opens) (hV : V ≤ h ⁻¹ᵁ W)
    (hV' : ∀ k, V ≤ (h ≫ ψ k) ⁻¹ᵁ (L.U (a k) ⊓ L.U (b k))) (ε : K → ℤ) :
    ∏ k, res (hV' k) (pullU (h ≫ ψ k) _ (L.g (a k) (b k))) ^ ε k =
      res hV (pullU h W (∏ k, res (hW k) (pullU (ψ k) _ (L.g (a k) (b k))) ^ ε k)) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow, res_pullU_comp' h (ψ k) (hW k) hV (hV' k)]
lemma linComb_g_comp (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (i j : K → L.ι) :
    (LB.LinComb L (fun k => h ≫ φ k) ε).g i j =
      res (le_inf (inf_le_left.trans (wchart_comp_le φ h i)) (inf_le_right.trans (wchart_comp_le φ h j)) :
        LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j))
        (pullU h _ ((LB.LinComb L φ ε).g i j)) := by
  exact prod_pull_generic h φ i j (LB.wchart L φ i ⊓ LB.wchart L φ j)
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))
    (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j)
    (le_inf (inf_le_left.trans (wchart_comp_le φ h i)) (inf_le_right.trans (wchart_comp_le φ h j)))
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L (fun k => h ≫ φ k) i k))
      (inf_le_right.trans (LB.wchart_le L (fun k => h ≫ φ k) j k))) ε
lemma app_compat_generic (h : Z ⟶ Y) {Ui Uj : Y.Opens} {Wi Wj : Z.Opens} (hi : Wi ≤ h ⁻¹ᵁ Ui)
    (hj : Wj ≤ h ⁻¹ᵁ Uj) (fi : Γ(Y, Ui)) (fj : Γ(Y, Uj)) (g : Γ(Y, Ui ⊓ Uj)ˣ)
    (hc : rs (inf_le_left : Ui ⊓ Uj ≤ Ui) fi = (g : Γ(Y, Ui ⊓ Uj)) * rs (inf_le_right : Ui ⊓ Uj ≤ Uj) fj)
    (g' : Γ(Z, Wi ⊓ Wj)ˣ)
    (hg' : g' = res (le_inf (inf_le_left.trans hi) (inf_le_right.trans hj) : Wi ⊓ Wj ≤ h ⁻¹ᵁ (Ui ⊓ Uj))
      (pullU h _ g)) :
    rs (inf_le_left : Wi ⊓ Wj ≤ Wi) (rs hi ((h.app Ui).hom fi)) =
      (g' : Γ(Z, Wi ⊓ Wj)) * rs (inf_le_right : Wi ⊓ Wj ≤ Wj) (rs hj ((h.app Uj).hom fj)) := by
  have hrr : ∀ {A B C : Z.Opens} (h1 : C ≤ B) (h2 : B ≤ A) (x : Γ(Z, A)),
      rs h1 (rs h2 x) = rs (h1.trans h2) x := by
    intro A B C h1 h2 x
    show (Z.presheaf.map (homOfLE h2).op ≫ Z.presheaf.map (homOfLE h1).op).hom x = _
    rw [← Functor.map_comp]
    try rfl
  have hm : ∀ {A B : Z.Opens} (h1 : B ≤ A) (x y : Γ(Z, A)), rs h1 (x * y) = rs h1 x * rs h1 y := by
    intro A B h1 x y
    show (Z.presheaf.map (homOfLE h1).op).hom (x * y) = _
    rw [map_mul]
    try rfl
  have hl : (Wi ⊓ Wj) ≤ h ⁻¹ᵁ (Ui ⊓ Uj) := le_inf (inf_le_left.trans hi) (inf_le_right.trans hj)
  have e1 : rs (inf_le_left : Wi ⊓ Wj ≤ Wi) (rs hi ((h.app Ui).hom fi)) =
      rs hl ((h.app (Ui ⊓ Uj)).hom (rs (inf_le_left : Ui ⊓ Uj ≤ Ui) fi)) := by
    rw [app_rs, hrr, hrr]
  have e2 : rs (inf_le_right : Wi ⊓ Wj ≤ Wj) (rs hj ((h.app Uj).hom fj)) =
      rs hl ((h.app (Ui ⊓ Uj)).hom (rs (inf_le_right : Ui ⊓ Uj ≤ Uj) fj)) := by
    rw [app_rs, hrr, hrr]
  rw [e1, e2, hc, map_mul, hm, hg']
  rfl
variable (L) in

def pullSec (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) :
    LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε) where
  f j := rs (wchart_comp_le φ h j) ((h.app (LB.wchart L φ j)).hom (s.f j))
  compat i j :=
    app_compat_generic h (wchart_comp_le φ h i) (wchart_comp_le φ h j) (s.f i) (s.f j) _ (s.compat i j) _
      (linComb_g_comp φ ε h i j)
def genSec {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M where
  f j := (t.s j : Γ(Y, M.U j))
  compat i j := congrArg Units.val (ht i j)
lemma prod_sum_generic (ψ : K ⊕ K' → (Y ⟶ X)) (a b : K ⊕ K' → L.ι) (ε : K ⊕ K' → ℤ) (V W W' : Y.Opens)
    (hV : ∀ k, V ≤ ψ k ⁻¹ᵁ (L.U (a k) ⊓ L.U (b k)))
    (hW : ∀ k, W ≤ ψ (Sum.inl k) ⁻¹ᵁ (L.U (a (Sum.inl k)) ⊓ L.U (b (Sum.inl k))))
    (hW' : ∀ k, W' ≤ ψ (Sum.inr k) ⁻¹ᵁ (L.U (a (Sum.inr k)) ⊓ L.U (b (Sum.inr k))))
    (hVW : V ≤ W) (hVW' : V ≤ W') :
    ∏ k, res (hV k) (pullU (ψ k) _ (L.g (a k) (b k))) ^ ε k =
      res hVW (∏ k, res (hW k) (pullU (ψ (Sum.inl k)) _ (L.g (a (Sum.inl k)) (b (Sum.inl k)))) ^ ε (Sum.inl k)) *
      res hVW' (∏ k, res (hW' k) (pullU (ψ (Sum.inr k)) _ (L.g (a (Sum.inr k)) (b (Sum.inr k)))) ^ ε (Sum.inr k)) := by
  have hrU : ∀ {A B C : Y.Opens} (h1 : C ≤ B) (h2 : B ≤ A) (x : Γ(Y, A)ˣ),
      res h1 (res h2 x) = res (h1.trans h2) x := by
    intro A B C h1 h2 x
    ext
    show (Y.presheaf.map (homOfLE h2).op ≫ Y.presheaf.map (homOfLE h1).op).hom x.val = _
    rw [← Functor.map_comp]
    try rfl
  rw [Fintype.prod_sum_type, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, hrU]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, hrU]
lemma wchart_inl (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K ⊕ K' → L.ι) :
    LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) := by
  intro z hz
  have hz' : z ∈ (LB.wchart L (Sum.elim φ φ') j : Set Y) := hz
  show z ∈ (LB.wchart L φ (j ∘ Sum.inl) : Set Y)
  simp only [LB.wchart, TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage] at hz' ⊢
  intro k
  exact hz' (Sum.inl k)
lemma wchart_inr (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K ⊕ K' → L.ι) :
    LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) := by
  intro z hz
  have hz' : z ∈ (LB.wchart L (Sum.elim φ φ') j : Set Y) := hz
  show z ∈ (LB.wchart L φ' (j ∘ Sum.inr) : Set Y)
  simp only [LB.wchart, TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage] at hz' ⊢
  intro k
  exact hz' (Sum.inr k)
lemma linComb_g_sum (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (i j : K ⊕ K' → L.ι) :
    (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
      res (le_inf (inf_le_left.trans (wchart_inl φ φ' i)) (inf_le_right.trans (wchart_inl φ φ' j)) :
          LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤
            LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl))
        ((LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl)) *
      res (le_inf (inf_le_left.trans (wchart_inr φ φ' i)) (inf_le_right.trans (wchart_inr φ φ' j)) :
          LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤
            LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr))
        ((LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr)) := by
  refine (prod_sum_generic (Sum.elim φ φ') i j (Sum.elim ε ε') _ _ _
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L (Sum.elim φ φ') i k))
      (inf_le_right.trans (LB.wchart_le L (Sum.elim φ φ') j k)))
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ (i ∘ Sum.inl) k))
      (inf_le_right.trans (LB.wchart_le L φ (j ∘ Sum.inl) k)))
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ' (i ∘ Sum.inr) k))
      (inf_le_right.trans (LB.wchart_le L φ' (j ∘ Sum.inr) k)))
    (le_inf (inf_le_left.trans (wchart_inl φ φ' i)) (inf_le_right.trans (wchart_inl φ φ' j)))
    (le_inf (inf_le_left.trans (wchart_inr φ φ' i)) (inf_le_right.trans (wchart_inr φ φ' j)))).trans ?_
  rfl
lemma mul_compat_generic {Ui Uj Ui' Uj' Wi Wj : Y.Opens} (hi : Wi ≤ Ui) (hi' : Wi ≤ Ui') (hj : Wj ≤ Uj)
    (hj' : Wj ≤ Uj') (fi : Γ(Y, Ui)) (fj : Γ(Y, Uj)) (fi' : Γ(Y, Ui')) (fj' : Γ(Y, Uj'))
    (g : Γ(Y, Ui ⊓ Uj)ˣ) (g' : Γ(Y, Ui' ⊓ Uj')ˣ)
    (hc : rs (inf_le_left : Ui ⊓ Uj ≤ Ui) fi = (g : Γ(Y, Ui ⊓ Uj)) * rs (inf_le_right : Ui ⊓ Uj ≤ Uj) fj)
    (hc' : rs (inf_le_left : Ui' ⊓ Uj' ≤ Ui') fi' = (g' : Γ(Y, Ui' ⊓ Uj')) * rs (inf_le_right : Ui' ⊓ Uj' ≤ Uj') fj')
    (G : Γ(Y, Wi ⊓ Wj)ˣ)
    (hG : G = res (le_inf (inf_le_left.trans hi) (inf_le_right.trans hj) : Wi ⊓ Wj ≤ Ui ⊓ Uj) g *
      res (le_inf (inf_le_left.trans hi') (inf_le_right.trans hj') : Wi ⊓ Wj ≤ Ui' ⊓ Uj') g') :
    rs (inf_le_left : Wi ⊓ Wj ≤ Wi) (rs hi fi * rs hi' fi') =
      (G : Γ(Y, Wi ⊓ Wj)) * rs (inf_le_right : Wi ⊓ Wj ≤ Wj) (rs hj fj * rs hj' fj') := by
  have hrr : ∀ {A B C : Y.Opens} (h1 : C ≤ B) (h2 : B ≤ A) (x : Γ(Y, A)),
      rs h1 (rs h2 x) = rs (h1.trans h2) x := by
    intro A B C h1 h2 x
    show (Y.presheaf.map (homOfLE h2).op ≫ Y.presheaf.map (homOfLE h1).op).hom x = _
    rw [← Functor.map_comp]
    try rfl
  have hm : ∀ {A B : Y.Opens} (h1 : B ≤ A) (x y : Γ(Y, A)), rs h1 (x * y) = rs h1 x * rs h1 y := by
    intro A B h1 x y
    show (Y.presheaf.map (homOfLE h1).op).hom (x * y) = _
    rw [map_mul]
    try rfl
  have hres : ∀ {A B : Y.Opens} (h1 : B ≤ A) (u : Γ(Y, A)ˣ),
      ((res h1 u : Γ(Y, B)ˣ) : Γ(Y, B)) = rs h1 (u : Γ(Y, A)) := fun _ _ => rfl
  have hl : Wi ⊓ Wj ≤ Ui ⊓ Uj := le_inf (inf_le_left.trans hi) (inf_le_right.trans hj)
  have hl' : Wi ⊓ Wj ≤ Ui' ⊓ Uj' := le_inf (inf_le_left.trans hi') (inf_le_right.trans hj')
  have e1 : rs (inf_le_left : Wi ⊓ Wj ≤ Wi) (rs hi fi) = rs hl (rs (inf_le_left : Ui ⊓ Uj ≤ Ui) fi) := by
    rw [hrr, hrr]
  have e2 : rs (inf_le_left : Wi ⊓ Wj ≤ Wi) (rs hi' fi') =
      rs hl' (rs (inf_le_left : Ui' ⊓ Uj' ≤ Ui') fi') := by
    rw [hrr, hrr]
  have e3 : rs (inf_le_right : Wi ⊓ Wj ≤ Wj) (rs hj fj) =
      rs hl (rs (inf_le_right : Ui ⊓ Uj ≤ Uj) fj) := by
    rw [hrr, hrr]
  have e4 : rs (inf_le_right : Wi ⊓ Wj ≤ Wj) (rs hj' fj') =
      rs hl' (rs (inf_le_right : Ui' ⊓ Uj' ≤ Uj') fj') := by
    rw [hrr, hrr]
  rw [hm, hm, e1, e2, e3, e4, hc, hc', hm, hm, hG, Units.val_mul, hres, hres]
  ring
variable (L) in

def mulSec (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) :
    LB.Sec (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) where
  f j := rs (wchart_inl φ φ' j) (s.f (j ∘ Sum.inl)) * rs (wchart_inr φ φ' j) (s'.f (j ∘ Sum.inr))
  compat i j :=
    mul_compat_generic (wchart_inl φ φ' i) (wchart_inr φ φ' i) (wchart_inl φ φ' j) (wchart_inr φ φ' j)
      (s.f (i ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) (s'.f (i ∘ Sum.inr)) (s'.f (j ∘ Sum.inr)) _ _
      (s.compat _ _) (s'.compat _ _) _ (linComb_g_sum φ ε φ' ε' i j)
end ReciprocityTheory.ChartRestriction.G.DVR


