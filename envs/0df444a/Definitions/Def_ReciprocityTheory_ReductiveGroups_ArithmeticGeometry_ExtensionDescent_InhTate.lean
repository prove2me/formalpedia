-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:35.846976+00:00
-- url     : https://prove2.me/theorems/5c27aea0-2795-40d4-9de0-3d8d07557c22
-- title:
--   Inh Tate
-- statement:
--   Definitions and structural lemmas for Inh Tate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.InhTate
open Semi Inh
def gv {Y : Scheme.{0}} (a : Γ(Y, ⊤)ˣ) (V : Y.Opens) : Γ(Y, V)ˣ := res le_top a
theorem map_map_lemma {Y : Scheme.{0}} {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U)
    (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE h').op).hom y) =
      (Y.presheaf.map (homOfLE (h.trans h')).op).hom y := by
  first
    | (show ((Y.presheaf.map (homOfLE h').op) ≫ (Y.presheaf.map (homOfLE h).op)).hom y = _; rw [← Functor.map_comp] <;> rfl)
    | (rw [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl)
theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(Y, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  exact map_map_lemma h h' _
theorem res_gv {Y : Scheme.{0}} (a : Γ(Y, ⊤)ˣ) {V W : Y.Opens} (h : W ≤ V) :
    res h (gv a V) = gv a W := by
  first
    | exact res_res h le_top a
    | (ext; exact map_map_lemma h le_top _)
def pullTop {X Y : Scheme.{0}} (f : Y ⟶ X) : Γ(X, ⊤)ˣ →* Γ(Y, ⊤)ˣ := Units.map f.appTop.hom
theorem app_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Γ(X, ⊤)) (V : X.Opens) :
    (f.app V).hom ((X.presheaf.map (homOfLE le_top).op).hom y) =
      (Y.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom y) := by
  first
    | (show ((X.presheaf.map (homOfLE le_top).op) ≫ f.app V).hom y = (f.appTop ≫ Y.presheaf.map (homOfLE le_top).op).hom y; rw [Scheme.Hom.naturality] <;> rfl)
    | (rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply] <;> rfl)
    | simp [← CommRingCat.comp_apply, Scheme.Hom.naturality]
theorem pullU_gv {X Y : Scheme.{0}} (f : Y ⟶ X) (a : Γ(X, ⊤)ˣ) (V : X.Opens) :
    pullU f V (gv a V) = gv (pullTop f a) (f ⁻¹ᵁ V) := by
  ext
  exact app_res_lemma_2 f (a : Γ(X, ⊤)) V
def IsConst {Y : Scheme.{0}} {L : LB Y} (t : LB.Gen L) (a : Γ(Y, ⊤)ˣ) : Prop :=
  ∀ j, t.s j = gv a (L.U j)
theorem IsConst.of_eq {Y : Scheme.{0}} {L : LB Y} {t : LB.Gen L} {a b : Γ(Y, ⊤)ˣ}
    (h : IsConst t a) (e : a = b) : IsConst t b := by
  subst e
  exact h
section Ops
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
theorem isConst_pullGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {a : Γ(Y, ⊤)ˣ} (ht : IsConst t a) (h : Z ⟶ Y) :
    IsConst (LB.pullGen L φ ε t h) (pullTop h a) := by
  intro j
  have e1 : t.s j = gv a (LB.wchart L φ j) := ht j
  show res _ (pullU h (LB.wchart L φ j) (t.s j)) = gv (pullTop h a) (LB.wchart L (fun k => h ≫ φ k) j)
  rw [e1, pullU_gv]
  exact res_gv _ _
theorem isConst_mulGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} {a b : Γ(Y, ⊤)ˣ}
    (ht : IsConst t a) (ht' : IsConst t' b) :
    IsConst (LB.mulGen L φ ε φ' ε' t t') (a * b) := by
  intro j
  have e1 : t.s (j ∘ Sum.inl) = gv a (LB.wchart L φ (j ∘ Sum.inl)) := ht _
  have e2 : t'.s (j ∘ Sum.inr) = gv b (LB.wchart L φ' (j ∘ Sum.inr)) := ht' _
  show res (U := LB.wchart L φ (j ∘ Sum.inl)) _ (t.s (j ∘ Sum.inl)) *
      res (U := LB.wchart L φ' (j ∘ Sum.inr)) _ (t'.s (j ∘ Sum.inr)) =
    gv (a * b) (LB.wchart L (Sum.elim φ φ') j)
  rw [e1, e2]
  exact (congrArg₂ (· * ·) (res_gv _ _) (res_gv _ _)).trans (map_mul (res le_top) a b).symm
theorem isConst_invGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {a : Γ(Y, ⊤)ˣ} (ht : IsConst t a) : IsConst (LB.invGen L φ ε t) a⁻¹ := by
  intro j
  have e1 : t.s j = gv a (LB.wchart L φ j) := ht j
  show (t.s j)⁻¹ = gv a⁻¹ (LB.wchart L φ j)
  rw [e1]
  first
    | exact (map_inv (res le_top) a).symm
    | simp [gv, map_inv]
theorem isConst_oneGen (L : LB X) : IsConst (LB.oneGen L (Y := Y)) 1 := by
  intro j
  first
    | exact (map_one (res le_top)).symm
    | (show (1 : Γ(Y, _)ˣ) = res le_top 1; simp)
theorem corr_of_isConst {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} {a : Γ(Y, ⊤)ˣ}
    (ht : IsConst t a) (ht' : IsConst t' a) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' _ _ _
  have e1 : t.s j = gv a (LB.wchart L φ j) := ht j
  have e2 : t'.s j' = gv a (LB.wchart L φ' j') := ht' j'
  rw [e1, e2]
  exact (res_gv _ _).trans (res_gv _ _).symm
end Ops
def cg {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb (trivLB X) φ ε) :=
  ⟨fun _ => gv a _⟩
theorem cg_isConst {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : Γ(Y, ⊤)ˣ) : IsConst (cg φ ε a) a := fun _ => rfl
theorem linComb_g_lemma_3 {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (hL : ∀ i j, L.g i j = 1) (i j : (LB.LinComb L φ ε).ι) :
    (LB.LinComb L φ ε).g i j = 1 := by
  first
    | (simp only [LB.LinComb, hL, map_one]; refine Finset.prod_eq_one fun k _ => ?_; erw [map_one]; exact one_zpow _)
    | (refine Finset.prod_eq_one fun k _ => ?_; rw [hL]; erw [map_one, map_one]; exact one_zpow _)
    | (simp only [LB.LinComb, hL, map_one]; refine Finset.prod_eq_one fun k _ => ?_; simp [res])
theorem cg_isGen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : Γ(Y, ⊤)ˣ) : (cg φ ε a).IsGen := by
  intro i j
  have hg : (LB.LinComb (trivLB X) φ ε).g i j = 1 := by
    exact linComb_g_lemma_3 φ ε (fun _ _ => rfl) i j
  rw [hg, _root_.one_mul]
  show res _ (gv a _) = res _ (gv a _)
  exact (res_gv _ _).trans (res_gv _ _).symm
abbrev R : Type := PowerSeries ℚ
abbrev S : Scheme.{0} := Spec (CommRingCat.of R)
def piK : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R (FractionRing R) PowerSeries.X)
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 PowerSeries.X_ne_zero)
def pi0 : Γ((TK R).left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom piK
abbrev P0 : PolAV S := zeroPolAV S
def tatePre : DegPre R where
  P := P0
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
  X := ℤ
  c := fun _ => toUnit _ ≫ η[P0.A]
  c_add := fun _ _ => toUnit_unique _ _
  psi := fun n => cg _ _ (pi0 ^ (n ^ 2))
  psi_gen := fun _ => cg_isGen _ _ _
theorem psi_isConst (n : ℤ) : IsConst (tatePre.psi n) (pi0 ^ (n ^ 2)) := by
  first
    | exact fun _ => rfl
    | exact cg_isConst _ _ _
theorem rigK_isConst : IsConst tatePre.rigK 1 := by
  first
    | exact (isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)
    | (intro j; show res _ (pullU _ _ (gv 1 _)) = gv 1 _; rw [pullU_gv, res_gv, map_one] <;> rfl)
theorem tau_isConst (a b : ℤ) : IsConst (tatePre.tau a b) (pi0 ^ (2 * a * b)) := by
  have h := isConst_mulGen (isConst_mulGen (isConst_mulGen (psi_isConst (a + b))
    (isConst_invGen (psi_isConst a))) (isConst_invGen (psi_isConst b)))
    (isConst_invGen rigK_isConst)
  refine h.of_eq ?_
  first
    | (rw [inv_one, _root_.mul_one, ← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add]; congr 1; ring)
    | group
theorem psiEven : tatePre.PsiEven := by
  intro χ
  have h1 : IsConst tatePre.sym 1 := cg_isConst _ _ 1
  have h2 := (isConst_pullGen h1 (tatePre.xK χ)).of_eq (map_one _)
  have h3 := isConst_mulGen (psi_isConst (-χ)) h2
  have key : ∀ z : ℤ, pi0 ^ ((-z) ^ 2) * 1 = pi0 ^ (z ^ 2) := fun z => by
    rw [_root_.mul_one, neg_sq]
  exact corr_of_isConst (h3.of_eq (key χ)) (psi_isConst χ)
theorem tauBimult : tatePre.TauBimult := by
  intro a a' b
  have h1 : IsConst tatePre.cub.t 1 := cg_isConst _ _ 1
  have h2 := (isConst_pullGen h1 (tatePre.pt3 a a' b)).of_eq (map_one _)
  have h3 := isConst_mulGen (tau_isConst (a + a') b) h2
  have h4 := isConst_mulGen (tau_isConst a b) (tau_isConst a' b)
  have key : ∀ x y z : ℤ,
      pi0 ^ (2 * (x + y) * z) * 1 = pi0 ^ (2 * x * z) * pi0 ^ (2 * y * z) := fun x y z => by
    rw [_root_.mul_one, ← zpow_add]
    congr 1
    ring
  exact corr_of_isConst (h3.of_eq (key a a' b)) h4
theorem jK_toOpen (V : S.Opens) (x : R) :
    ((jK R).app V).hom (DegPre.toOpen V x) =
      ((TK R).left.presheaf.map (homOfLE le_top).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
          (algebraMap R (FractionRing R) x)) := by
  have e : (jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) x) := by
    first
      | (show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (jK R).appTop).hom x = ((CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).hom x; rw [Scheme.ΓSpecIso_inv_naturality] <;> rfl)
      | (rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality] <;> rfl)
  show ((jK R).app V).hom ((S.presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) = _
  rw [app_res_lemma_2, e] <;> rfl
abbrev I : Ideal R := Ideal.span {PowerSeries.X}
theorem psiIn (n : ℤ) (m : ℕ) (hm : m ≤ n.natAbs ^ 2) : tatePre.PsiIn n (I ^ m) := by
  intro j V _ _ h
  have hk : n ^ 2 = ((n.natAbs ^ 2 : ℕ) : ℤ) := by
    first
      | (push_cast; exact (sq_abs n).symm)
      | (rw [Nat.cast_pow]; exact (Int.natAbs_sq n).symm)
  refine ⟨DegPre.toOpen V (PowerSeries.X ^ (n.natAbs ^ 2)), Ideal.mem_map_of_mem _ ?_, ?_⟩
  · exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _)
  · have e2 : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
          (algebraMap R (FractionRing R) (PowerSeries.X ^ (n.natAbs ^ 2))) =
        ((pi0 ^ (n ^ 2) : Γ((TK R).left, ⊤)ˣ) : Γ((TK R).left, ⊤)) := by
      rw [hk, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, map_pow]
      rfl
    have hv : ((tatePre.psi n).s j).val = ((TK R).left.presheaf.map (homOfLE le_top).op).hom
        ((pi0 ^ (n ^ 2) : Γ((TK R).left, ⊤)ˣ) : Γ((TK R).left, ⊤)) := rfl
    rw [jK_toOpen, hv, map_map_lemma, ← e2] <;> rfl
def tateData : DegData R I where
  toPre := tatePre
  psi_even := psiEven
  tau_bimult := tauBimult
  psi_pos := fun (n : ℤ) hn => by
    have h1 : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hn)
    have := psiIn n 1 (by nlinarith)
    simpa using this
  psi_tendsto := fun m => by
    refine (Set.finite_Icc (-(m : ℤ)) m).subset ?_
    intro n hn
    by_contra hc
    apply hn
    apply psiIn n m
    simp only [Set.mem_Icc, not_and_or, not_le] at hc
    have : m < n.natAbs := by omega
    nlinarith
end ReciprocityTheory.ChartRestriction.G.Out.InhTate


