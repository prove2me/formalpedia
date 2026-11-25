-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:00.87353+00:00
-- url     : https://prove2.me/theorems/51949613-a117-424a-98f4-4e9eadb7b863
-- title:
--   Psi Weight Zero Linear Combination
-- statement:
--   Definitions and structural lemmas for Psi Weight Zero Linear Combination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData
section Const
variable {Z Y W : Scheme.{0}} {J J' : Type} [Fintype J] [Fintype J']
theorem wchart_triv (φ : J → (Y ⟶ Z)) (j : J → (Inh.trivLB Z).ι) : LB.wchart (Inh.trivLB Z) φ j = ⊤ := by
  apply eq_top_iff.2
  intro x _
  simp [LB.wchart, Inh.trivLB]
theorem res_self {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)ˣ) : res h x = x := by
  unfold res
  ext
  simp
theorem gv_inj {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)ˣ} (h : gv a V = gv b V) : a = b := by
  subst hV
  unfold gv at h
  rwa [res_self, res_self] at h
theorem res_res_lemma {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  change (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom (x : Γ(Y, U))) =
    (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem linComb_trivLB_U_eq_univ (φ : J → (Y ⟶ Z)) (ε : J → ℤ) (j : ((Inh.trivLB Z).LinComb φ ε).ι) :
    ((Inh.trivLB Z).LinComb φ ε).U j = ⊤ :=
  wchart_triv φ j
theorem exists_isConst {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (t : LB.Gen (LB.LinComb (Inh.trivLB Z) φ ε)) :
    ∃ a : Γ(Y, ⊤)ˣ, IsConst t a := by
  obtain ⟨j0, -⟩ : ∃ j : ((Inh.trivLB Z).LinComb φ ε).ι, True := ⟨fun _ => PUnit.unit, trivial⟩
  refine ⟨res (linComb_trivLB_U_eq_univ φ ε j0).ge (t.s j0), fun j => ?_⟩
  obtain rfl : j = j0 := funext fun _ => rfl
  exact ((res_res_lemma _ _ _).trans (res_self _ _)).symm
theorem isConst_unique {φ : J → (Y ⟶ Z)} {ε : J → ℤ} {t : LB.Gen (LB.LinComb (Inh.trivLB Z) φ ε)}
    {a b : Γ(Y, ⊤)ˣ} (ha : IsConst t a) (hb : IsConst t b) : a = b := by
  have j : J → (Inh.trivLB Z).ι := fun _ => PUnit.unit
  exact gv_inj (wchart_triv φ j) ((ha j).symm.trans (hb j))
theorem gen_eq_of_isConst {L : LB Y} {t t' : LB.Gen L} {a : Γ(Y, ⊤)ˣ} (h : IsConst t a) (h' : IsConst t' a) :
    t = t' := by
  cases t
  cases t'
  congr 1
  funext j
  exact (h j).trans (h' j).symm
theorem eq_of_corr {φ : J → (Y ⟶ Z)} {ε : J → ℤ} {φ' : J' → (Y ⟶ Z)} {ε' : J' → ℤ}
    {t : LB.Gen (LB.LinComb (Inh.trivLB Z) φ ε)} {t' : LB.Gen (LB.LinComb (Inh.trivLB Z) φ' ε')}
    {a b : Γ(Y, ⊤)ˣ} (ha : IsConst t a) (hb : IsConst t' b)
    (h : LB.Gen.Corr (Inh.trivLB Z) φ ε φ' ε' t t') : a = b := by
  obtain ⟨j0, -⟩ : ∃ j : ((Inh.trivLB Z).LinComb φ ε).ι, True := ⟨fun _ => PUnit.unit, trivial⟩
  obtain ⟨j1, -⟩ : ∃ j : ((Inh.trivLB Z).LinComb φ' ε').ι, True := ⟨fun _ => PUnit.unit, trivial⟩
  have e := h j0 j1 (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [ha j0, hb j1] at e
  unfold gv at e
  refine gv_inj ?_ ((res_res_lemma _ _ a).symm.trans (e.trans (res_res_lemma _ _ b)))
  simp
  exact ⟨wchart_triv φ j0, wchart_triv φ' j1⟩
theorem corr_iff_eq {φ : J → (Y ⟶ Z)} {ε : J → ℤ} {φ' : J' → (Y ⟶ Z)} {ε' : J' → ℤ}
    {t : LB.Gen (LB.LinComb (Inh.trivLB Z) φ ε)} {t' : LB.Gen (LB.LinComb (Inh.trivLB Z) φ' ε')}
    {a b : Γ(Y, ⊤)ˣ} (ha : IsConst t a) (hb : IsConst t' b) :
    LB.Gen.Corr (Inh.trivLB Z) φ ε φ' ε' t t' ↔ a = b := ⟨eq_of_corr ha hb, fun e => by subst e; exact corr_of_isConst ha hb⟩
theorem pullTop_injective (f : W ⟶ Y) [IsIso f] : Function.Injective (pullTop f) := by
  have : IsIso (Scheme.Hom.appTop f) := inferInstanceAs (IsIso (f.app ⊤))
  intro a b h
  ext1
  have h' := congrArg Units.val h
  simp only [pullTop, Units.coe_map, MonoidHom.coe_coe] at h'
  exact (asIso (Scheme.Hom.appTop f)).commRingCatIsoToRingEquiv.injective h'
theorem isConst_one_of_corr_oneGen {φ : J → (Y ⟶ Z)} {ε : J → ℤ}
    (u : LB.Gen (LB.LinComb (Inh.trivLB Z) φ ε)) (f : W ⟶ Y) [IsIso f]
    (h : LB.Gen.Corr (Inh.trivLB Z) _ _ _ _ (LB.pullGen _ φ ε u f) (LB.oneGen _)) : IsConst u 1 := by
  obtain ⟨a, ha⟩ := exists_isConst u
  have e := eq_of_corr (isConst_pullGen ha f) (isConst_oneGen _) h
  have : a = 1 := pullTop_injective f (e.trans (map_one _).symm)
  rwa [this] at ha
instance isIso_zero2 (S : Scheme.{0}) : IsIso (zero2 (zeroPolAV S).A) := by
  have : (lift η[(zeroPolAV S).A] η[(zeroPolAV S).A] : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S)) =
      (λ_ (𝟙_ (Over S))).inv :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (toUnit_unique _ _)
  change IsIso ((Over.forget S).map
    (lift η[(zeroPolAV S).A] η[(zeroPolAV S).A] : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S)))
  rw [this]
  infer_instance
end Const
section UnitOn
variable {A B : Type} [CommRing A] [CommRing B]
theorem unitOn_one : unitOn (1 : Aˣ) = 1 := by
  unfold unitOn
  exact map_one _
theorem unitOn_mul (u v : Aˣ) : unitOn (u * v) = unitOn u * unitOn v := by
  unfold unitOn
  exact map_mul _ _ _
theorem unitOn_inv (u : Aˣ) : unitOn u⁻¹ = (unitOn u)⁻¹ := by
  unfold unitOn
  exact map_inv _ _
theorem unitOn_bijective : Function.Bijective (unitOn : Aˣ → Γ(Sp A, ⊤)ˣ) := by
  have e : (unitOn : Aˣ → Γ(Sp A, ⊤)ˣ) =
      Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv := by
    funext u
    ext
    rfl
  rw [e]
  exact (Units.mapEquiv _).bijective
theorem unitOn_inj {u v : Aˣ} : unitOn u = unitOn v ↔ u = v := unitOn_bijective.injective.eq_iff
end UnitOn
variable (K : Type) [CommRing K] [IsDomain K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
def toricPre (q : X → (FractionRing K)ˣ) : DegPre K where
  P := zeroPolAV _
  rig := cg _ _ 1
  rig_gen := cg_isGen _ _ 1
  cub :=
    { t := cg _ _ 1
      isGen := cg_isGen _ _ 1
      face := fun _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)
      cubeSymmetric_swap_first := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      cubeSymmetric_swap_last := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      cocycle := corr_of_isConst
        ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))
        ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _)) }
  sym := cg _ _ 1
  sym_gen := cg_isGen _ _ 1
  sym_rig := corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)
  X := X
  c := fun _ => toUnit _ ≫ η[(zeroPolAV _).A]
  c_add := fun _ _ => toUnit_unique _ _
  psi := fun y => cg _ _ (unitOn (q y))
  psi_gen := fun _ => cg_isGen _ _ _
variable {K X}
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

def polar (q : X → (FractionRing K)ˣ) (a b : X) : (FractionRing K)ˣ := q (a + b) * (q a)⁻¹ * (q b)⁻¹
instance (q : X → (FractionRing K)ˣ) (O : Type) [Ring O] [Module O X] : Module O (toricPre K X q).X :=
  inferInstanceAs (Module O X)
variable (q : X → (FractionRing K)ˣ)
theorem psi_isConst (y : X) : IsConst ((toricPre K X q).psi y) (unitOn (q y)) := cg_isConst _ _ _
theorem rigK_isConst : IsConst (toricPre K X q).rigK 1 := (isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)
theorem tau_isConst (a b : X) : IsConst ((toricPre K X q).tau a b) (unitOn (polar q a b)) := (isConst_mulGen (isConst_mulGen (isConst_mulGen (psi_isConst q _) (isConst_invGen (psi_isConst q _)))
    (isConst_invGen (psi_isConst q _))) (isConst_invGen (rigK_isConst q))).of_eq
  (by simp only [polar, unitOn_mul, unitOn_inv, inv_one]; exact _root_.mul_one _)
theorem psiEven_iff : (toricPre K X q).PsiEven ↔ ∀ y, q (-y) = q y := by
  unfold DegPre.PsiEven
  refine forall_congr' fun y => (corr_iff_eq (isConst_mulGen (psi_isConst q _)
    (isConst_pullGen (cg_isConst _ _ 1) _)) (psi_isConst q y)).trans ?_
  rw [map_one]
  exact ⟨fun e => unitOn_inj.1 ((_root_.mul_one _).symm.trans e), fun e => (_root_.mul_one _).trans (congrArg unitOn e)⟩
theorem psiEven (h : ∀ y, q (-y) = q y) : (toricPre K X q).PsiEven := (psiEven_iff q).2 h
theorem tauBimult_iff :
    (toricPre K X q).TauBimult ↔ ∀ a a' b, polar q (a + a') b = polar q a b * polar q a' b := by
  unfold DegPre.TauBimult
  refine forall_congr' fun a => forall_congr' fun a' => forall_congr' fun b =>
    (corr_iff_eq (isConst_mulGen (tau_isConst q _ _) (isConst_pullGen (cg_isConst _ _ 1) _))
      (isConst_mulGen (tau_isConst q _ _) (tau_isConst q _ _))).trans ?_
  rw [map_one, ← unitOn_mul]
  exact ⟨fun e => unitOn_inj.1 ((_root_.mul_one _).symm.trans e), fun e => (_root_.mul_one _).trans (congrArg unitOn e)⟩
theorem tauBimult (h : ∀ a a' b, polar q (a + a') b = polar q a b * polar q a' b) : (toricPre K X q).TauBimult := (tauBimult_iff q).2 h
theorem isConst_one_of_zero2 {J : Type} [Fintype J]
    {φ : J → (((toricPre K X q).P.A ⊗ (toricPre K X q).P.A).left ⟶ (toricPre K X q).P.A.left)} {ε : J → ℤ}
    (u : LB.Gen (LB.LinComb (toricPre K X q).P.L φ ε))
    (h : LB.Gen.Corr (toricPre K X q).P.L _ _ _ _ (LB.pullGen _ φ ε u (zero2 (toricPre K X q).P.A))
      (LB.oneGen _)) : IsConst u 1 := by
  have : IsIso (zero2 (toricPre K X q).P.A) := isIso_zero2 _
  exact isConst_one_of_corr_oneGen u _ h
def toricOAct (O : Type) [Ring O] [StarRing O] [Module O X]
    (h : ∀ (a : O) y z, polar q (a • y) z = polar q y (star a • z)) :
    (toricPre K X q).OAct O where
  onB := zeroOAct O _
  c_lin := fun _ _ => toUnit_unique _ _
  tau_bal := fun a u _ hu (y y' : X) =>
    corr_of_isConst
      ((isConst_mulGen (tau_isConst q (a • y) y') (isConst_pullGen (isConst_one_of_zero2 q u hu) _)).of_eq
        (b := unitOn (polar q y (star a • y'))) (by rw [map_one, _root_.mul_one, h]))
      (tau_isConst q y (star a • y'))
theorem jK_toOpen (V : (Sp K).Opens) (x : K) :
    ((jK K).app V).hom (DegPre.toOpen V x) =
      ((TK K).left.presheaf.map (homOfLE le_top).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing K))).inv.hom (algebraMap K (FractionRing K) x)) := by
  unfold DegPre.toOpen jK
  have e1 := congrArg (fun g => g.hom x)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K (FractionRing K))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1 ⊢
  rw [e1, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl
theorem psi_eq_toOpen (y : X) (r : K) (hq : (q y : FractionRing K) = algebraMap K _ r)
    (j : PUnit → (toricPre K X q).P.L.ι) (V : (Sp K).Opens)
    (h : jK K ⁻¹ᵁ V ≤ (LB.LinComb (toricPre K X q).P.L (K := PUnit) (fun _ => (toricPre K X q).xK y)
      (fun _ => -1)).U j) :
    ((jK K).app V).hom (DegPre.toOpen V r) =
      ((TK K).left.presheaf.map (homOfLE h).op).hom (((toricPre K X q).psi y).s j).val := by
  rw [show ((toricPre K X q).psi y).s j = gv (unitOn (q y)) _ from cg_isConst _ _ _ j, jK_toOpen]
  unfold gv res unitOn
  simp only [Units.coe_map, MonoidHom.coe_coe, hq]
  conv_rhs => rw [← CommRingCat.comp_apply]
  erw [← Functor.map_comp]
  rfl
theorem psiIn (y : X) (J : Ideal K) (r : K) (hr : r ∈ J) (h : (q y : FractionRing K) = algebraMap K _ r) :
    (toricPre K X q).PsiIn y J := by
  intro j V _ _ h'
  exact ⟨DegPre.toOpen V r, Ideal.mem_map_of_mem _ hr, psi_eq_toOpen q y r h j V h'⟩
variable (F : Type) [Field F] [Algebra (FractionRing K) F]
theorem cubAt_isConst (x x' y : TF (R := K) F ⟶ (toricPre K X q).P.A) :
    IsConst (DegPre.cubAt (toricPre K X q) F x x' y) 1 := (isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)
def pt (t : Multiplicative X →* Fˣ) : GtPtF (toricPre K X q) F where
  b := DegPre.zeroF _ F
  s := fun χ => cg _ _ (unitOn (t (Multiplicative.ofAdd (show X from χ))))
  isGen := fun _ => cg_isGen _ _ _
  s_zero := corr_of_isConst ((cg_isConst _ _ _).of_eq ((congrArg unitOn (map_one t)).trans unitOn_one))
    (isConst_oneGen _)
  mult := fun (a a' : X) => corr_of_isConst
    ((isConst_mulGen (cg_isConst _ _ _) (cubAt_isConst q F _ _ _)).of_eq
      ((_root_.mul_one _).trans ((congrArg unitOn
        (map_mul t (Multiplicative.ofAdd a) (Multiplicative.ofAdd a'))).trans (unitOn_mul _ _))))
    (isConst_mulGen (cg_isConst _ _ _) (cg_isConst _ _ _))
theorem pt_isConst (t : Multiplicative X →* Fˣ) (χ : X) :
    IsConst ((pt q F t).s χ) (unitOn (t (Multiplicative.ofAdd χ))) := cg_isConst _ _ _
theorem pt_bijective : Function.Bijective (pt q F) := by
  constructor
  · intro t t' e
    refine MonoidHom.ext fun χ => ?_
    have h4 := pt_isConst q F t' (Multiplicative.toAdd χ)
    rw [← e] at h4
    exact unitOn_inj.1 (isConst_unique (pt_isConst q F t _) h4)
  · rintro ⟨b, s, hs, s0, sm⟩
    obtain rfl : b = DegPre.zeroF _ F := toUnit_unique _ _
    choose a ha using fun χ => exists_isConst (s χ)
    have h0 := eq_of_corr (ha 0) (isConst_oneGen _) s0
    have hm := fun χ χ' => eq_of_corr (isConst_mulGen (ha (χ + χ')) (cubAt_isConst q F _ _ _))
      (isConst_mulGen (ha χ) (ha χ')) (sm χ χ')
    let u := fun χ => Function.surjInv (unitOn_bijective (A := F)).2 (a χ)
    have hu : ∀ χ, unitOn (u χ) = a χ := fun χ => Function.surjInv_eq _ _
    refine ⟨{ toFun := fun χ => u (Multiplicative.toAdd χ)
              map_one' := unitOn_inj.1 ((hu _).trans (h0.trans unitOn_one.symm))
              map_mul' := fun χ χ' => unitOn_inj.1 ((hu _).trans ((_root_.mul_one _).symm.trans
                ((hm _ _).trans (by rw [unitOn_mul, hu, hu] <;> rfl)))) }, ?_⟩
    unfold pt
    congr 1
    first
      | exact funext fun χ => gen_eq_of_isConst (cg_isConst _ _ _) ((ha χ).of_eq (hu χ).symm)
      | exact heq_of_eq (funext fun χ => gen_eq_of_isConst (cg_isConst _ _ _) ((ha χ).of_eq (hu χ).symm))
theorem eq_of_map_eq_of_eq_univ {Y : Scheme.{0}} {W : Y.Opens} (hW : W = ⊤) (h : W ≤ ⊤) {a b : Γ(Y, ⊤)}
    (e : (Y.presheaf.map (homOfLE h).op).hom a = (Y.presheaf.map (homOfLE h).op).hom b) : a = b := by
  subst hW
  simpa using e
theorem psiIn_iff (y : X) (J : Ideal K) :
    (toricPre K X q).PsiIn y J ↔ ∃ r ∈ J, (q y : FractionRing K) = algebraMap K _ r := by
  refine ⟨fun hP => ?_, fun ⟨r, hr, h⟩ => psiIn q y J r hr h⟩
  have hs : Function.Surjective (DegPre.toOpen (⊤ : (Spec (CommRingCat.of K)).Opens)) := by
    intro z
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom z, ?_⟩
    unfold DegPre.toOpen
    simp
  obtain ⟨r', hr', e⟩ := hP (fun _ => PUnit.unit) ⊤ (isAffineOpen_top _) (by intro x _; exact trivial)
    (le_top.trans (wchart_triv _ _).ge)
  obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hr'
  refine ⟨r, hr, ?_⟩
  rw [show ((toricPre K X q).psi y).s (fun _ => PUnit.unit) = gv (unitOn (q y)) _ from cg_isConst _ _ _ _, jK_toOpen] at e
  unfold gv res unitOn at e
  simp only [Units.coe_map, MonoidHom.coe_coe] at e
  conv_rhs at e => rw [← CommRingCat.comp_apply]
  erw [← Functor.map_comp] at e
  have e2 := eq_of_map_eq_of_eq_univ (by simp) _ e
  exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing K))).symm.commRingCatIsoToRingEquiv.injective e2).symm
section Examples
theorem polar_zpow_sq (u : (FractionRing K)ˣ) (a b : ℤ) :
    polar (fun n : ℤ => u ^ (n ^ 2)) a b = u ^ (2 * a * b) := by
  simp only [polar]
  rw [← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add]
  congr 1
  ring
example (u : (FractionRing K)ˣ) :
    (toricPre K ℤ (fun n => u ^ (n ^ 2))).PsiEven ∧ (toricPre K ℤ (fun n => u ^ (n ^ 2))).TauBimult ∧
      Nonempty ((toricPre K ℤ (fun n => u ^ (n ^ 2))).OAct ℤ) :=
  ⟨psiEven _ fun y => by rw [neg_sq],
    tauBimult _ fun a a' b => by
      rw [polar_zpow_sq, polar_zpow_sq, polar_zpow_sq, ← zpow_add]
      congr 1
      ring,
    ⟨toricOAct _ ℤ fun a y z => by
      rw [polar_zpow_sq, polar_zpow_sq, star_trivial, smul_eq_mul, smul_eq_mul]
      congr 1
      ring⟩⟩
example (u : (FractionRing K)ˣ) (hu : u * u ≠ 1) : ¬ (toricPre K ℤ (fun n => u ^ n)).PsiEven := by
  rw [psiEven_iff]
  intro h
  have h1 := h 1
  rw [zpow_neg, zpow_one] at h1
  exact hu (by nth_rw 1 [← h1]; exact inv_mul_cancel u)
example (y : X) (J : Ideal K) (hJ : J ≠ ⊤) :
    ¬ (toricPre K X q).PsiIn y ⊥ ∧ ¬ (toricPre K X (fun _ => 1)).PsiIn y J := by
  constructor
  · rw [psiIn_iff]
    rintro ⟨r, hr, h⟩
    rw [Ideal.mem_bot.1 hr, map_zero] at h
    exact (q y).ne_zero h
  · rw [psiIn_iff]
    rintro ⟨r, hr, h⟩
    have : r = 1 := IsFractionRing.injective K (FractionRing K) (by rw [← h, map_one, Units.val_one])
    exact hJ ((Ideal.eq_top_iff_one J).2 (this ▸ hr))
example (q : ℤ → (FractionRing K)ˣ) (u v : Fˣ) (h : u ≠ v) :
    pt q F (zpowersHom Fˣ u) ≠ pt q F (zpowersHom Fˣ v) :=
  fun e => h ((zpowersHom Fˣ).injective ((pt_bijective q F).1 e))
end Examples
end GlobalTheory.ToricData


