-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:07.328504+00:00
-- url     : https://prove2.me/theorems/477ae2a0-0b45-43e5-9914-f085bf382908
-- title:
--   Canon Gen Is Gen
-- statement:
--   Definitions and structural lemmas for Canon Gen Is Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
namespace Canon
variable {X Y : Scheme.{0}} (L : LB X)
lemma res_res' {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(Y, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  apply Units.ext
  change (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom (u : Γ(Y, U))) =
    (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom u
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
lemma pullU_res (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) (h' : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) : pullU f W (res h u) = res h' (pullU f U u) := by
  apply Units.ext
  have e := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE h).op)
    (u : Γ(X, U))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e
  exact e
lemma res_pullU_eq (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (hZ : Z ≤ f ⁻¹ᵁ U) (hZ' : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res hZ (pullU f U x) = res hZ' (pullU f W (res h x)) := by
  rw [pullU_res f h (f.preimage_mono h), res_res']
def gW {W : Y.Opens} (ψ : Y ⟶ X) (a b : L.ι) (h : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) : Γ(Y, W)ˣ :=
  res h (pullU ψ _ (L.g a b))
variable {L}
lemma lePI {W : Y.Opens} {ψ : Y ⟶ X} {A B : X.Opens} (ha : W ≤ ψ ⁻¹ᵁ A) (hb : W ≤ ψ ⁻¹ᵁ B) :
    W ≤ ψ ⁻¹ᵁ (A ⊓ B) :=
  le_inf ha hb
lemma gW_res {V W : Y.Opens} (ψ : Y ⟶ X) (a b : L.ι) (h : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b))
    (hVW : V ≤ W) : res hVW (gW L ψ a b h) = gW L ψ a b (hVW.trans h) :=
  res_res' _ _ _
lemma gW_mul (hL : L.IsLB) {W : Y.Opens} (ψ : Y ⟶ X) (a b c : L.ι)
    (hT : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) (h1 : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b))
    (h2 : W ≤ ψ ⁻¹ᵁ (L.U b ⊓ L.U c)) (h3 : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U c)) :
    gW L ψ a b h1 * gW L ψ b c h2 = gW L ψ a c h3 := by
  unfold gW
  rw [res_pullU_eq ψ (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) h1 hT,
    res_pullU_eq ψ (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) h2 hT,
    res_pullU_eq ψ (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) h3 hT, ← map_mul, ← map_mul, hL.cocycle]
lemma wchart_le_of {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι) {ψ : Y ⟶ X} {c : K}
    (hc : φ c = ψ) : LB.wchart L φ j ≤ ψ ⁻¹ᵁ L.U (j c) := by
  subst hc; exact LB.wchart_le L φ j c
lemma res_g {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : (LB.LinComb L φ ε).ι)
    {W : Y.Opens} (hW : W ≤ (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') :
    res hW ((LB.LinComb L φ ε).g j j') = ∏ k, gW L (φ k) (j k) (j' k)
      (lePI (hW.trans (inf_le_left.trans (LB.wchart_le L φ j k)))
        (hW.trans (inf_le_right.trans (LB.wchart_le L φ j' k)))) ^ ε k := by
  refine (map_prod (res hW) _ Finset.univ).trans (Finset.prod_congr rfl fun k _ => ?_)
  refine (map_zpow (res hW) _ _).trans ?_
  congr 1
  exact res_res' _ _ _
lemma prod_sameSum {M : Type*} [CommGroup M] {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (hs : LB.SameSum φ ε φ' ε') (F : (Y ⟶ X) → M) :
    ∏ k, F (φ k) ^ ε k = ∏ k', F (φ' k') ^ ε' k' := by
  classical
  have zs : ∀ {K : Type} (a : M) (s : Finset K) (e : K → ℤ),
      a ^ (∑ k ∈ s, e k) = ∏ k ∈ s, a ^ e k := by
    intro K a s e
    induction s using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add, ih]
  have key : ∀ {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (T : Finset (Y ⟶ X)),
      (∀ k, φ k ∈ T) →
      ∏ k, F (φ k) ^ ε k = ∏ ψ ∈ T, F ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
    intro K _ φ ε T hT
    rw [← Finset.prod_fiberwise_of_maps_to (g := φ) (t := T) (fun k _ => hT k)]
    refine Finset.prod_congr rfl fun ψ _ => ?_
    rw [← Finset.sum_filter, zs]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  rw [key φ ε (Finset.univ.image φ ∪ Finset.univ.image φ') (fun k => by simp),
    key φ' ε' (Finset.univ.image φ ∪ Finset.univ.image φ') (fun k => by simp)]
  refine Finset.prod_congr rfl fun ψ _ => ?_
  congr 1
  exact hs ψ
lemma res_refl {U : Y.Opens} (h : U ≤ U) (u : Γ(Y, U)ˣ) : res h u = u := by
  apply Units.ext
  change (Y.presheaf.map (homOfLE h).op).hom (u : Γ(Y, U)) = u
  rw [show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl
lemma gW_mul' (hL : L.IsLB) {W : Y.Opens} (ψ : Y ⟶ X) (a b c : L.ι) (ha : W ≤ ψ ⁻¹ᵁ L.U a)
    (hb : W ≤ ψ ⁻¹ᵁ L.U b) (hc : W ≤ ψ ⁻¹ᵁ L.U c) :
    gW L ψ a b (lePI ha hb) * gW L ψ b c (lePI hb hc) = gW L ψ a c (lePI ha hc) :=
  gW_mul hL ψ a b c (lePI (lePI ha hb) hc) _ _ _
variable {K K' : Type} [Fintype K] [Fintype K']
lemma lcle (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j : (LB.LinComb L φ ε).ι) (k : K) :
    (LB.LinComb L φ ε).U j ≤ φ k ⁻¹ᵁ L.U (j k) :=
  LB.wchart_le L φ j k
def R (φ' : K' → (Y ⟶ X)) (j' : K' → L.ι) (ψ : Y ⟶ X) (h : ∃ k', φ' k' = ψ) : L.ι :=
  j' h.choose
lemma lcle_R (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (j' : (LB.LinComb L φ' ε').ι) (ψ : Y ⟶ X)
    (h : ∃ k', φ' k' = ψ) : (LB.LinComb L φ' ε').U j' ≤ ψ ⁻¹ᵁ L.U (R φ' j' ψ h) :=
  wchart_le_of φ' j' h.choose_spec
def jhat (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (hsub : ∀ k, ∃ k', φ' k' = φ k)
    (j' : K' → L.ι) : (LB.LinComb L φ ε).ι :=
  fun k => R φ' j' (φ k) (hsub k)
lemma wchart_le_jhat (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (hsub : ∀ k, ∃ k', φ' k' = φ k) (j' : (LB.LinComb L φ' ε').ι) :
    (LB.LinComb L φ' ε').U j' ≤ (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j') := by
  intro y hy
  exact Set.mem_iInter.2 fun k => lcle_R φ' ε' j' (φ k) (hsub k) hy
def corrU (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (j' : (LB.LinComb L φ' ε').ι) :
    Γ(Y, (LB.LinComb L φ' ε').U j')ˣ :=
  ∏ k', gW L (φ' k') (j' k') (R φ' j' (φ' k') ⟨k', rfl⟩)
    (lePI (lcle φ' ε' j' k') (lcle_R φ' ε' j' _ _)) ^ ε' k'
lemma res_corrU (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (j' : (LB.LinComb L φ' ε').ι) {W : Y.Opens}
    (hW : W ≤ (LB.LinComb L φ' ε').U j') :
    res hW (corrU φ' ε' j') = ∏ k', gW L (φ' k') (j' k') (R φ' j' (φ' k') ⟨k', rfl⟩)
      (lePI (hW.trans (lcle φ' ε' j' k')) (hW.trans (lcle_R φ' ε' j' _ _))) ^ ε' k' := by
  refine (map_prod (res hW) _ Finset.univ).trans (Finset.prod_congr rfl fun k' _ => ?_)
  refine (map_zpow (res hW) _ _).trans ?_
  rw [gW_res]
variable (L)
def canonGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (hsub : ∀ k, ∃ k', φ' k' = φ k) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb L φ' ε') where
  s j' := res (wchart_le_jhat φ ε φ' ε' hsub j') (t.s (jhat φ ε φ' hsub j')) * corrU φ' ε' j'
variable {L}
theorem canon_key (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (hs : LB.SameSum φ ε φ' ε') (hsub : ∀ k, ∃ k', φ' k' = φ k)
    (j1 j2 : (LB.LinComb L φ' ε').ι)
    (hW : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
      (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j1) ⊓ (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j2)) :
    res hW ((LB.LinComb L φ ε).g (jhat φ ε φ' hsub j1) (jhat φ ε φ' hsub j2)) *
        res inf_le_left (corrU φ' ε' j1) =
      (LB.LinComb L φ' ε').g j1 j2 * res inf_le_right (corrU φ' ε' j2) := by
  classical
  have eg : (LB.LinComb L φ' ε').g j1 j2 = ∏ k', gW L (φ' k') (j1 k') (j2 k')
      (lePI (inf_le_left.trans (lcle φ' ε' j1 k')) (inf_le_right.trans (lcle φ' ε' j2 k')))
        ^ ε' k' :=
    (res_refl le_rfl _).symm.trans (res_g φ' ε' j1 j2 le_rfl)
  let F : (Y ⟶ X) → Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)ˣ := fun ψ =>
    if h : ∃ k', φ' k' = ψ then
      gW L ψ (R φ' j1 ψ h) (R φ' j2 ψ h)
        (lePI (inf_le_left.trans (lcle_R φ' ε' j1 ψ h))
          (inf_le_right.trans (lcle_R φ' ε' j2 ψ h)))
    else 1
  have hP : (∏ k, gW L (φ k) (jhat φ ε φ' hsub j1 k) (jhat φ ε φ' hsub j2 k)
      (lePI (hW.trans (inf_le_left.trans (LB.wchart_le L φ _ k)))
        (hW.trans (inf_le_right.trans (LB.wchart_le L φ _ k)))) ^ ε k) =
      ∏ k', F (φ' k') ^ ε' k' := by
    rw [← prod_sameSum φ ε φ' ε' hs F]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [F, dif_pos (hsub k)]
    rfl
  have key : ∀ k', F (φ' k') * gW L (φ' k') (j1 k') (R φ' j1 (φ' k') ⟨k', rfl⟩)
      (lePI (inf_le_left.trans (lcle φ' ε' j1 k')) (inf_le_left.trans (lcle_R φ' ε' j1 _ _))) =
      gW L (φ' k') (j1 k') (j2 k')
        (lePI (inf_le_left.trans (lcle φ' ε' j1 k')) (inf_le_right.trans (lcle φ' ε' j2 k'))) *
      gW L (φ' k') (j2 k') (R φ' j2 (φ' k') ⟨k', rfl⟩)
        (lePI (inf_le_right.trans (lcle φ' ε' j2 k')) (inf_le_right.trans (lcle_R φ' ε' j2 _ _))) := by
    intro k'
    simp only [F, dif_pos (⟨k', rfl⟩ : ∃ c, φ' c = φ' k')]
    have h1 : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤ φ' k' ⁻¹ᵁ L.U (j1 k') :=
      inf_le_left.trans (lcle φ' ε' j1 k')
    have h2 : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤ φ' k' ⁻¹ᵁ L.U (j2 k') :=
      inf_le_right.trans (lcle φ' ε' j2 k')
    have r1 : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
        φ' k' ⁻¹ᵁ L.U (R φ' j1 (φ' k') ⟨k', rfl⟩) :=
      inf_le_left.trans (lcle_R φ' ε' j1 _ _)
    have r2 : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
        φ' k' ⁻¹ᵁ L.U (R φ' j2 (φ' k') ⟨k', rfl⟩) :=
      inf_le_right.trans (lcle_R φ' ε' j2 _ _)
    rw [gW_mul' hL _ _ _ _ h1 h2 r2, mul_comm, gW_mul' hL _ _ _ _ h1 r1 r2]
  have hprod : (∏ k', F (φ' k') ^ ε' k') * (∏ k', gW L (φ' k') (j1 k') (R φ' j1 (φ' k') ⟨k', rfl⟩)
      (lePI (inf_le_left.trans (lcle φ' ε' j1 k')) (inf_le_left.trans (lcle_R φ' ε' j1 _ _)))
        ^ ε' k') =
      (∏ k', gW L (φ' k') (j1 k') (j2 k')
        (lePI (inf_le_left.trans (lcle φ' ε' j1 k')) (inf_le_right.trans (lcle φ' ε' j2 k')))
          ^ ε' k') *
      ∏ k', gW L (φ' k') (j2 k') (R φ' j2 (φ' k') ⟨k', rfl⟩)
        (lePI (inf_le_right.trans (lcle φ' ε' j2 k')) (inf_le_right.trans (lcle_R φ' ε' j2 _ _)))
          ^ ε' k' := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k' _ => ?_
    rw [← mul_zpow, ← mul_zpow, key]
  exact (congrArg₂ (· * ·) ((res_g φ ε _ _ hW).trans hP) (res_corrU φ' ε' j1 _)).trans
    (hprod.trans (congrArg₂ (· * ·) eg (res_corrU φ' ε' j2 _)).symm)
abbrev rO {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →+* Γ(Y, V) :=
  (Y.presheaf.map (homOfLE h).op).hom
lemma rO_rO {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    rO h2 (rO h1 x) = rO (h2.trans h1) x := by
  change (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
    (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
variable (L)
def canonSec (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (hs : LB.SameSum φ ε φ' ε') (hsub : ∀ k, ∃ k', φ' k' = φ k)
    (sc : LB.Sec (LB.LinComb L φ ε)) : LB.Sec (LB.LinComb L φ' ε') where
  f j' := rO (wchart_le_jhat φ ε φ' ε' hsub j') (sc.f (jhat φ ε φ' hsub j')) *
    (corrU φ' ε' j' : Γ(Y, (LB.LinComb L φ' ε').U j'))
  compat j1 j2 := by
    have hW : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
        (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j1) ⊓ (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j2) :=
      inf_le_inf (wchart_le_jhat φ ε φ' ε' hsub j1) (wchart_le_jhat φ ε φ' ε' hsub j2)
    have key := congrArg Units.val (canon_key hL φ ε φ' ε' hs hsub j1 j2 hW)
    simp only [Units.val_mul] at key
    have e := congrArg (rO hW) (sc.compat (jhat φ ε φ' hsub j1) (jhat φ ε φ' hsub j2))
    have e' : rO (hW.trans inf_le_left) (sc.f (jhat φ ε φ' hsub j1)) =
        ((res hW ((LB.LinComb L φ ε).g (jhat φ ε φ' hsub j1) (jhat φ ε φ' hsub j2)) :
          Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)ˣ) :
          Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)) *
        rO (hW.trans inf_le_right) (sc.f (jhat φ ε φ' hsub j2)) :=
      (rO_rO _ _ _).symm.trans (e.trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) rfl (rO_rO _ _ _))))
    have l1 : rO (inf_le_left : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
          (LB.LinComb L φ' ε').U j1)
        (rO (wchart_le_jhat φ ε φ' ε' hsub j1) (sc.f (jhat φ ε φ' hsub j1)) *
          (corrU φ' ε' j1 : Γ(Y, (LB.LinComb L φ' ε').U j1))) =
        rO (hW.trans inf_le_left) (sc.f (jhat φ ε φ' hsub j1)) *
          ((res inf_le_left (corrU φ' ε' j1) :
            Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)ˣ) :
            Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)) :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (rO_rO _ _ _) rfl)
    have l2 : rO (inf_le_right : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
          (LB.LinComb L φ' ε').U j2)
        (rO (wchart_le_jhat φ ε φ' ε' hsub j2) (sc.f (jhat φ ε φ' hsub j2)) *
          (corrU φ' ε' j2 : Γ(Y, (LB.LinComb L φ' ε').U j2))) =
        rO (hW.trans inf_le_right) (sc.f (jhat φ ε φ' hsub j2)) *
          ((res inf_le_right (corrU φ' ε' j2) :
            Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)ˣ) :
            Γ(Y, (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2)) :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (rO_rO _ _ _) rfl)
    refine l1.trans (Eq.trans ?_ (congrArg (_ * ·) l2).symm)
    rw [e']
    linear_combination (rO (hW.trans inf_le_right) (sc.f (jhat φ ε φ' hsub j2))) * key
end Canon
end ReciprocityTheory.ChartRestriction.G.Out


