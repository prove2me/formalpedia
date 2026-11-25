-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:04.517865+00:00
-- url     : https://prove2.me/theorems/4bc99d59-7cfa-5631-b024-5a5b7a519fb7
-- title:
--   Is Nsmul Iff Eq
-- statement:
--   Definitions and structural lemmas for Is Nsmul Iff Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsNsmulIffEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_zero_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cubAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem gen_ext_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  refine unit_ext (V := LB.wchart L φ j) fun y hy => ?_
  choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
  exact (gen_trans ht (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans
    (gen_trans ht' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
abbrev charVal (g : GtPtF D F) (χ : D.X) (y : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι) :
    ((TF (R := R) F).left.presheaf.stalk y)ˣ := val (g.s χ) (𝟙 (TF (R := R) F).left) y J
abbrev tauVal (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (x χ : D.X) (y : (TF (R := R) F).left)
    (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι) : ((TF (R := R) F).left.presheaf.stalk y)ˣ :=
  val (D.tau x χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) y J
theorem gt_ext_val {g g' : GtPtF D F} (hb : g.b = g'.b)
    (h : ∀ χ y J, Good D.P.L y J → charVal g χ y J = charVal g' χ y J) : g = g' := by
  obtain ⟨b, s, hs, h₀, hm⟩ := g
  obtain ⟨b', s', hs', h₀', hm'⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => gen_ext_val D.P.isLB (hs χ) (hs' χ) (h χ)
  rfl
theorem charVal_zero (g : GtPtF D F) {y J} (hJ : Good D.P.L y J) : charVal g 0 y J = 1 :=
  (val_corr hJ g.s_zero _).trans (val_one _)
theorem charVal_add (g : GtPtF D F) {y J} (hJ : Good D.P.L y J) (χ χ' : D.X) :
    charVal g (χ + χ') y J * th D y J (cP D _ χ) (cP D _ χ') g.b = charVal g χ y J * charVal g χ' y J := by
  have e := gt_mul (𝟙 (TF (R := R) F)) hJ g χ χ'
  rw [Category.id_comp] at e
  exact e
theorem isAdd_iff_val (g g' g'' : GtPtF D F) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    charVal g'' χ y J * th D y J (cP D _ χ) g.b g'.b = charVal g χ y J * charVal g' χ y J := isAdd_iff g g' g''
theorem isZero_iff_val (g : GtPtF D F) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → charVal g χ y J = 1 :=
  isZero_iff g
theorem isIota_iff_val (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g.b = cP D _ x ∧ ∀ χ y J, Good D.P.L y J →
    charVal g χ y J = tauVal D F x χ y J := isIota_iff x g
theorem cubAt_isGen (x x' w : TF (R := R) F ⟶ D.P.A) : (DegPre.cubAt D F x x' w).IsGen :=
  pullGen_isGen _ _ _ _ D.cub.isGen _
theorem exists_add (g g' : GtPtF D F) : ∃ g'', g.IsAdd g' g'' := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))
      (LB.invGen D.P.L _ _ (DegPre.cubAt D F (cP D _ χ) g.b g'.b))) (𝟙 (TF (R := R) F).left) y J =
      charVal g χ y J * charVal g' χ y J * (th D y J (cP D _ χ) g.b g'.b)⁻¹ := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cubAt hJ _ _ _))))
  obtain ⟨g'', hb, hv⟩ := exists_gt (g.b * g'.b) (fun χ => LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ)) (LB.invGen D.P.L _ _ (DegPre.cubAt D F (cP D _ χ) g.b g'.b)))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (g'.isGen _))
      (invGen_isGen _ _ _ _ (cubAt_isGen _ _ _))) (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt g.b χ h) (prod_gt g'.b χ h))
        (prod_neg _ _ (prod_cub (cP D _ χ) g.b g'.b h))).trans ?_
      rw [prod_gt, _root_.mul_assoc (cP D _ χ)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      refine (vv 0 y J hJ).trans ?_
      rw [charVal_zero g hJ, charVal_zero g' hJ, cPoint_zero, C.face]; simp) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      have e₁ := congrArg Additive.ofMul (charVal_add g hJ χ χ')
      have e₂ := congrArg Additive.ofMul (charVal_add g' hJ χ χ')
      have e₃ := congrArg Additive.ofMul (C.compat (cP D _ χ) (cP D _ χ') g.b g'.b)
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ ⊢
      linear_combination (norm := abel) e₁ + e₂ - e₃)
  exact ⟨g'', (isAdd_iff_val _ _ _).2 ⟨hb, fun χ y J hJ =>
    (congrArg₂ (· * ·) ((hv χ y J hJ).trans (vv χ y J hJ)) rfl).trans (inv_mul_cancel_right _ _)⟩⟩
theorem isAdd_unique {g g' h h' : GtPtF D F} (e : g.IsAdd g' h) (e' : g.IsAdd g' h') : h = h' := by
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 e
  obtain ⟨b', v'⟩ := (isAdd_iff_val _ _ _).1 e'
  exact gt_ext_val (b.trans b'.symm) fun χ y J hJ => mul_right_cancel ((v χ y J hJ).trans (v' χ y J hJ).symm)
theorem exists_neg (g : GtPtF D F) : ∃ g' : GtPtF D F, g'.b = g.b⁻¹ ∧ ∀ χ y J, Good D.P.L y J →
    charVal g' χ y J = (charVal g χ y J)⁻¹ * th D y J (cP D _ χ) g.b g.b⁻¹ := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.s χ))
      (DegPre.cubAt D F (cP D _ χ) g.b g.b⁻¹)) (𝟙 (TF (R := R) F).left) y J =
      (charVal g χ y J)⁻¹ * th D y J (cP D _ χ) g.b g.b⁻¹ := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _) (val_cubAt hJ _ _ _))
  obtain ⟨g', hb, hv⟩ := exists_gt g.b⁻¹ (fun χ => LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.s χ))
      (DegPre.cubAt D F (cP D _ χ) g.b g.b⁻¹))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (g.isGen _)) (cubAt_isGen _ _ _)) (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_neg _ _ (prod_gt g.b χ h))
        (prod_cub (cP D _ χ) g.b g.b⁻¹ h)).trans ?_
      rw [prod_gt, mul_inv_cancel_right, mul_inv_cancel]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      refine (vv 0 y J hJ).trans ?_
      rw [charVal_zero g hJ, cPoint_zero, C.face]; simp) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      have e₁ := congrArg Additive.ofMul (charVal_add g hJ χ χ')
      have e₃ := C.compat (cP D _ χ) (cP D _ χ') g.b g.b⁻¹
      rw [mul_inv_cancel, C.face₃, _root_.one_mul] at e₃
      have e₄ := congrArg Additive.ofMul e₃
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e₁ e₄ ⊢
      linear_combination (norm := abel) e₄ - e₁)
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
def gtAdd (g g' : GtPtF D F) : GtPtF D F := (exists_add g g').choose
def gtZero (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] : GtPtF D F :=
  (exists_zero_gt (D := D) (F := F)).choose
def gtNeg (g : GtPtF D F) : GtPtF D F := (exists_neg g).choose
theorem isAdd_gtAdd (g g' : GtPtF D F) : g.IsAdd g' (gtAdd g g') := (exists_add g g').choose_spec
theorem isZero_gtZero : (gtZero D F).IsZero := (exists_zero_gt (D := D) (F := F)).choose_spec
theorem gtAdd_b (g g' : GtPtF D F) : (gtAdd g g').b = g.b * g'.b := (isAdd_gtAdd g g').1
theorem gtAdd_val (g g' : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (gtAdd g g') χ y J * th D y J (cP D _ χ) g.b g'.b = charVal g χ y J * charVal g' χ y J :=
  ((isAdd_iff_val _ _ _).1 (isAdd_gtAdd g g')).2 χ y J hJ
theorem gtAdd_comm (g g' : GtPtF D F) : gtAdd g g' = gtAdd g' g :=
  isAdd_unique (isAdd_gtAdd g g') ((isAdd_iff_val _ _ _).2 ⟨(gtAdd_b g' g).trans (mul_comm _ _), fun χ y J hJ => by
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [C.s12, gtAdd_val g' g χ hJ, mul_comm]⟩)
theorem gtAdd_assoc (g g' g'' : GtPtF D F) : gtAdd (gtAdd g g') g'' = gtAdd g (gtAdd g' g'') :=
  gt_ext_val (by rw [gtAdd_b, gtAdd_b, gtAdd_b, gtAdd_b, _root_.mul_assoc]) fun χ y J hJ => by
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have s : ∀ a b c : TF (R := R) F ⟶ D.P.A, th D y J a b c = th D y J c a b := fun a b c => by
      rw [C.s12, C.s01]
    have c := C.coc g.b g'.b g''.b (cP D _ χ)
    rw [s _ _ (cP D _ χ), s _ _ (cP D _ χ), s _ _ (cP D _ χ), s _ _ (cP D _ χ)] at c
    have e₁ := gtAdd_val (gtAdd g g') g'' χ hJ
    have e₃ := gtAdd_val g (gtAdd g' g'') χ hJ
    rw [gtAdd_b] at e₁ e₃
    have a₁ := congrArg Additive.ofMul e₁
    have a₂ := congrArg Additive.ofMul (gtAdd_val g g' χ hJ)
    have a₃ := congrArg Additive.ofMul e₃
    have a₄ := congrArg Additive.ofMul (gtAdd_val g' g'' χ hJ)
    have a₅ := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a₁ a₂ a₃ a₄ a₅ ⊢
    linear_combination (norm := abel) a₁ + a₂ - a₃ - a₄ - a₅
theorem gtZero_add (g : GtPtF D F) : gtAdd (gtZero D F) g = g := by
  obtain ⟨b, v⟩ := (isZero_iff_val _).1 (isZero_gtZero (D := D) (F := F))
  exact isAdd_unique (isAdd_gtAdd _ g) ((isAdd_iff_val _ _ _).2 ⟨by rw [b, _root_.one_mul], fun χ y J hJ => by
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [b, C.face₂, v χ y J hJ, mul_comm]⟩)
theorem gtAdd_neg (g : GtPtF D F) : gtAdd g (gtNeg g) = gtZero D F := by
  obtain ⟨b, v⟩ := (isZero_iff_val _).1 (isZero_gtZero (D := D) (F := F))
  obtain ⟨b', v'⟩ : (gtNeg g).b = g.b⁻¹ ∧ ∀ χ y J, Good D.P.L y J →
    charVal (gtNeg g) χ y J = (charVal g χ y J)⁻¹ * th D y J (cP D _ χ) g.b g.b⁻¹ := (exists_neg g).choose_spec
  exact isAdd_unique (isAdd_gtAdd _ _) ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', mul_inv_cancel], fun χ y J hJ => by
    rw [v χ y J hJ, v' χ y J hJ, b', _root_.one_mul, mul_inv_cancel_left]⟩)
@[reducible] def gtGroup (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] : AddCommGroup (GtPtF D F) :=
  letI : Add (GtPtF D F) := ⟨gtAdd⟩
  letI : Zero (GtPtF D F) := ⟨gtZero D F⟩
  letI : Neg (GtPtF D F) := ⟨gtNeg⟩
  { add_assoc := gtAdd_assoc
    zero_add := gtZero_add
    add_zero := fun g => (gtAdd_comm _ _).trans (gtZero_add g)
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun g => (gtAdd_comm _ _).trans (gtAdd_neg g)
    add_comm := gtAdd_comm }
attribute [local instance] gtGroup
theorem isAdd_iff_eq (g g' g'' : GtPtF D F) : g.IsAdd g' g'' ↔ g'' = g + g' :=
  ⟨fun h => isAdd_unique h (isAdd_gtAdd g g'), fun h => h ▸ isAdd_gtAdd g g'⟩
theorem add_b (g g' : GtPtF D F) : (g + g').b = g.b * g'.b := gtAdd_b g g'
def gtProj (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    GtPtF D F →+ Additive (TF (R := R) F ⟶ D.P.A) :=
  AddMonoidHom.mk' (fun g => Additive.ofMul g.b) fun g g' => congrArg Additive.ofMul (add_b g g')
theorem exists_iota (hB : D.TauBimult) (x : D.X) : ∃ g : GtPtF D F, GtPtF.IsIota x g := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F))
      (𝟙 (TF (R := R) F).left) y J = tauVal D F x χ y J := fun χ y J hJ => val_pull hJ _ _ _
  have sy : ∀ {y J}, Good D.P.L y J → ∀ a b, tauVal D F a b y J = tauVal D F b a y J := fun hJ a b =>
    tau_symm (𝟙 (TF (R := R) F)) hJ a b
  have ml : ∀ {y J}, Good D.P.L y J → ∀ a a' b, tauVal D F (a + a') b y J * th D y J (cP D _ a) (cP D _ a') (cP D _ b) =
      tauVal D F a b y J * tauVal D F a' b y J := fun hJ a a' b => tau_mul (𝟙 (TF (R := R) F)) hJ hB a a' b
  obtain ⟨g, hb, hv⟩ := exists_gt (F := F) (cP D _ x) (fun χ => LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F))
    (fun χ => pullGen_isGen _ _ _ _ (tau_isGen D x χ) _) (fun χ U _ h => by
      have a : ∀ w : D.X, jFK (R := R) F ≫ ptK (D.c w) = (cP D (TF (R := R) F) w).left := fun w =>
        (Category.assoc _ _ _).symm
      have a₀ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      rw [prod_gt, ← cPoint_add, add_comm χ x, ← a, ← a, ← a, ← a₀]
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]
      rw [mul_right_comm _ (h _) (h _)]) (fun y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      have t := ml hJ 0 0 x
      rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
      exact (vv 0 y J hJ).trans ((sy hJ _ _).trans (mul_eq_left.1 t.symm))) (fun χ χ' y J hJ => by
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [sy hJ x, sy hJ x, sy hJ x]
      exact ml hJ _ _ _)
  exact ⟨g, (isIota_iff_val _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩
def iota (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] : D.X →+ GtPtF D F :=
  AddMonoidHom.mk' (fun x => (exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
    refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
end GlobalTheory.TorusExt


