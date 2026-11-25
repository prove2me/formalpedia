-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:13:38.202123+00:00
-- url     : https://prove2.me/theorems/8b56ed2d-8643-4f87-b3da-6d8a085aa592
-- title:
--   Arc Var Zpow Injective
-- statement:
--   Definitions and structural lemmas for Arc Var Zpow Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Theorems.Thm_GlobalTheory_ToricData_toricPre_tate
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
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open Matrix in
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
  [Module.Finite ℤ X] in
lemma exists_pos_nat_mul_eq_int {Idx : Type} [Fintype Idx] (q : Idx → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ w : Idx → ℤ, ∀ i, (w i : ℚ) = N * q i := by
  classical
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).pos,
    fun i => (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ), fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)]
  push_cast
  rw [← Rat.mul_den_eq_num (q i)]
  ring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open Matrix in
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
  [Module.Finite ℤ X] in

theorem _root_.GlobalTheory.ToricData.finite_form_le (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (hp : ∀ y, y ≠ 0 → 0 < be y y) (C : ℤ) : {y | be y y ≤ C}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  set Idx := Module.Free.ChooseBasisIndex ℤ X
  let A : Matrix Idx Idx ℤ := fun i j => be (b i) (b j)
  have hQ : ∀ y, be y y = b.repr y ⬝ᵥ A *ᵥ b.repr y := by
    intro y
    have h := congrArg (fun B : LinearMap.BilinForm ℤ X => B y y) (Matrix.toBilin_toMatrix b be)
    simp only [Matrix.toBilin_apply, LinearMap.BilinForm.toMatrix_apply] at h
    rw [← h]
    simp only [A, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpos : ∀ w : Idx → ℤ, w ≠ 0 → 0 < w ⬝ᵥ A *ᵥ w := by
    intro w hw
    have h := hp (b.equivFun.symm w) (b.equivFun.symm.map_ne_zero_iff.mpr hw)
    rwa [hQ, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at h
  let AR : Matrix Idx Idx ℝ := A.map (Int.cast : ℤ → ℝ)
  have hcastR : ∀ w : Idx → ℤ, (fun i => (w i : ℝ)) ⬝ᵥ AR *ᵥ (fun i => (w i : ℝ)) =
      ((w ⬝ᵥ A *ᵥ w : ℤ) : ℝ) := by
    intro w
    simp [AR, dotProduct, Matrix.mulVec]
  have hnn : ∀ v : Idx → ℝ, 0 ≤ v ⬝ᵥ AR *ᵥ v := by
    intro v
    have hd : DenseRange (Pi.map fun _ : Idx => (Rat.cast : ℚ → ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun v => 0 ≤ v ⬝ᵥ AR *ᵥ v) v
      (isClosed_le continuous_const (by fun_prop)) fun q => ?_
    obtain ⟨N, hN, w, hw⟩ := exists_pos_nat_mul_eq_int q
    have hwv : (fun i => (w i : ℝ)) =
        (N : ℝ) • Pi.map (fun _ : Idx => (Rat.cast : ℚ → ℝ)) q := by
      funext i
      have := congrArg (Rat.cast : ℚ → ℝ) (hw i)
      push_cast at this
      simpa using this
    have h1 : 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ AR *ᵥ (fun i => (w i : ℝ)) := by
      rw [hcastR]
      by_cases hw0 : w = 0
      · simp [hw0]
      · exact_mod_cast (hpos w hw0).le
    rw [hwv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h1
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact (mul_nonneg_iff_of_pos_left hN').mp ((mul_nonneg_iff_of_pos_left hN').mp h1)
  have hdetA : A.det ≠ 0 := by
    intro h0
    let AQ : Matrix Idx Idx ℚ := A.map (Int.cast : ℤ → ℚ)
    have hQdet : AQ.det = 0 := by
      have h2 : ((A.det : ℤ) : ℚ) = AQ.det := (Int.castRingHom ℚ).map_det A
      rw [← h2, h0, Int.cast_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hQdet
    obtain ⟨N, hN, w, hw⟩ := exists_pos_nat_mul_eq_int v
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hw0 : w ≠ 0 := by
      intro hw0
      apply hv0
      funext i
      have h := hw i
      simp only [hw0, Pi.zero_apply, Int.cast_zero] at h
      simpa using (mul_eq_zero.mp h.symm).resolve_left hN0
    have hwv : (fun i => (w i : ℚ)) = (N : ℚ) • v := funext fun i => by simp [hw i]
    have hzero : ((w ⬝ᵥ A *ᵥ w : ℤ) : ℚ) = 0 := by
      have h3 : ((w ⬝ᵥ A *ᵥ w : ℤ) : ℚ) =
          (fun i => (w i : ℚ)) ⬝ᵥ AQ *ᵥ (fun i => (w i : ℚ)) := by
        simp [AQ, dotProduct, Matrix.mulVec]
      rw [h3, hwv, Matrix.mulVec_smul, hv]
      simp
    have h4 := hpos w hw0
    have h5 : (w ⬝ᵥ A *ᵥ w) = 0 := by exact_mod_cast hzero
    omega
  have hherm : AR.IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    show ((be (b j) (b i) : ℤ) : ℝ) = ((be (b i) (b j) : ℤ) : ℝ)
    rw [hs]
  have hpsd : AR.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => by simpa using hnn x
  have hdetR : AR.det ≠ 0 := by
    have h2 : ((A.det : ℤ) : ℝ) = AR.det := (Int.castRingHom ℝ).map_det A
    rw [← h2]
    exact_mod_cast hdetA
  have hpd : AR.PosDef := hpsd.posDef_iff_det_ne_zero.mpr hdetR
  have hposR : ∀ v : Idx → ℝ, v ≠ 0 → 0 < v ⬝ᵥ AR *ᵥ v := fun v hv => by
    simpa using hpd.dotProduct_mulVec_pos hv
  have hcont : Continuous fun v : Idx → ℝ => v ⬝ᵥ AR *ᵥ v := by fun_prop
  obtain ⟨m, hm, hmv⟩ : ∃ m : ℝ, 0 < m ∧ ∀ v : Idx → ℝ, m * ‖v‖ ^ 2 ≤ v ⬝ᵥ AR *ᵥ v := by
    by_cases hS : (Metric.sphere (0 : Idx → ℝ) 1).Nonempty
    · obtain ⟨v0, hv0, hmin⟩ :=
        (isCompact_sphere (0 : Idx → ℝ) 1).exists_isMinOn hS hcont.continuousOn
      have hv0' : v0 ≠ 0 := by rintro rfl; simp at hv0
      refine ⟨_, hposR v0 hv0', fun v => ?_⟩
      by_cases hv : v = 0
      · simp [hv]
      have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Idx → ℝ) 1 := by
        simp [norm_smul, hnv.ne']
      have h1 := isMinOn_iff.mp hmin _ hu
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
      calc v0 ⬝ᵥ AR *ᵥ v0 * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ AR *ᵥ v))) * ‖v‖ ^ 2 := by
            gcongr
        _ = v ⬝ᵥ AR *ᵥ v := by field_simp
    · refine ⟨1, one_pos, fun v => ?_⟩
      have hv : v = 0 := by
        by_contra hv
        exact hS ⟨‖v‖⁻¹ • v, by simp [norm_smul, (norm_pos_iff.mpr hv).ne']⟩
      simp [hv]
  set R : ℕ := ⌈(C : ℝ) / m⌉₊ + 1 with hR
  have hbound : ∀ c : Idx → ℤ, c ⬝ᵥ A *ᵥ c ≤ C → ∀ i, |c i| ≤ R := by
    intro c hc i
    have h1 : m * ‖(fun j => (c j : ℝ))‖ ^ 2 ≤ C := by
      have h0 := hmv (fun j => (c j : ℝ))
      rw [hcastR c] at h0
      exact h0.trans (by exact_mod_cast hc)
    have h2 : |(c i : ℝ)| ≤ ‖(fun j => (c j : ℝ))‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun j => (c j : ℝ)) i
    have h6 := Nat.le_ceil ((C : ℝ) / m)
    have h7 : (0 : ℝ) ≤ ⌈(C : ℝ) / m⌉₊ := Nat.cast_nonneg _
    have h3 : (|c i| : ℝ) ≤ R := by
      rw [hR]
      push_cast
      rcases le_or_gt |(c i : ℝ)| 1 with h | h
      · linarith
      · have h4 : |(c i : ℝ)| ≤ ‖(fun j => (c j : ℝ))‖ ^ 2 := by nlinarith
        have h5 : ‖(fun j => (c j : ℝ))‖ ^ 2 ≤ (C : ℝ) / m := by
          rw [le_div_iff₀ hm]
          linarith
        linarith
    exact_mod_cast h3
  have hT : (Set.pi Set.univ fun _ : Idx => Set.Icc (-(R : ℤ)) R).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hT.image b.equivFun.symm).subset fun y hy => ?_
  refine ⟨b.equivFun y, fun i _ => ?_, b.equivFun.symm_apply_apply y⟩
  have h := hbound (b.equivFun y) (by rw [Module.Basis.equivFun_apply, ← hQ]; exact hy) i
  exact abs_le.mp h
section ThetaShiftProofs
def arcVar (k : Type) [Field k] : (FractionRing (PowerSeries k))ˣ :=
  Units.mk0 (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) PowerSeries.X)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero)
def arcExp (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X) (y : X) : (FractionRing (PowerSeries k))ˣ :=
  Units.mk0 (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) PowerSeries.X)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero) ^ (be y y / 2)
variable (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X)
theorem arcVar_val :
    (arcVar k : FractionRing (PowerSeries k)) = algebraMap (PowerSeries k) _ PowerSeries.X := rfl
theorem arcVar_zpow_injective : Function.Injective fun n : ℤ => arcVar k ^ n := by
  rw [injective_zpow_iff_not_isOfFinOrder, isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, h⟩
  have h1 : (PowerSeries.X : PowerSeries k) ^ n = 1 :=
    IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k)) (by
      rw [map_pow, map_one, ← arcVar_val, ← Units.val_pow_eq_pow_val, h, Units.val_one])
  have h2 := congrArg PowerSeries.constantCoeff h1
  simp [hn.ne'] at h2
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem arcExp_eq (y : X) : arcExp k be y = arcVar k ^ (be y y / 2) := rfl
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem arcExp_val (y : X) : (arcExp k be y : FractionRing (PowerSeries k)) =
    algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) PowerSeries.X ^ (be y y / 2) :=
  Units.val_zpow_eq_zpow_val _ _
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem arcExp_neg (y : X) : arcExp k be (-y) = arcExp k be y := by
  simp only [arcExp_eq, map_neg, LinearMap.neg_apply, neg_neg]
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem polar_arcExp (hs : ∀ y z, be y z = be z y) (he : ∀ y, (2 : ℤ) ∣ be y y) (y z : X) :
    polar (arcExp k be) y z = arcVar k ^ (be y z) := by
  rw [polar, arcExp_eq, arcExp_eq, arcExp_eq, ← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add]
  congr 1
  have h1 := he y
  have h2 := he z
  simp only [map_add, LinearMap.add_apply, hs z y]
  omega
theorem psiIn_arcExp_iff (y : X) (n : ℕ) :
    (toricPre _ X (arcExp k be)).PsiIn y (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ n) ↔
      (n : ℤ) ≤ be y y / 2 := by
  rw [psiIn_iff, Ideal.span_singleton_pow]
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 hr
    by_contra hlt
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) = be y y / 2 + (m + 1 : ℕ) := ⟨((n : ℤ) - be y y / 2 - 1).toNat, by omega⟩
    have hX := (arcVar k).ne_zero
    rw [arcVar_val] at hX
    have h1 : (PowerSeries.X : PowerSeries k) ^ (m + 1) * s = 1 :=
      IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k)) (by
        rw [arcExp_val, map_mul, map_pow, ← zpow_natCast, hm, zpow_add₀ hX, _root_.mul_assoc, zpow_natCast] at h
        rw [map_mul, map_pow, map_one]
        exact (mul_left_cancel₀ (zpow_ne_zero _ hX) ((_root_.mul_one _).trans h)).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp at h2
  · intro h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, be y y / 2 = (n + m : ℕ) := ⟨(be y y / 2 - n).toNat, by omega⟩
    refine ⟨PowerSeries.X ^ (n + m), Ideal.mem_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right _ _)), ?_⟩
    rw [arcExp_val, hm, zpow_natCast, map_pow]
def arcData (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (hp : ∀ y, y ≠ 0 → 0 < be y y) (he : ∀ y, (2 : ℤ) ∣ be y y) :
    DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) where
  toPre := toricPre _ X (arcExp k be)
  psi_even := psiEven _ (arcExp_neg k be)
  tau_bimult := tauBimult _ fun a a' b => by
    rw [polar_arcExp k be hs he, polar_arcExp k be hs he, polar_arcExp k be hs he, map_add, LinearMap.add_apply,
      zpow_add]
  psi_pos := fun (y : X) hy => by
    have h1 := hp y hy
    have h2 := he y
    have := (psiIn_arcExp_iff k be y 1).2 (by omega)
    rwa [pow_one] at this
  psi_tendsto := fun n => (finite_form_le be hs hp (2 * n)).subset fun (y : X) hy => by
    have : ¬ (n : ℤ) ≤ be y y / 2 := fun h => hy ((psiIn_arcExp_iff k be y n).2 h)
    change be y y ≤ 2 * n
    omega
variable (hs : ∀ y z, be y z = be z y) (hp : ∀ y, y ≠ 0 → 0 < be y y) (he : ∀ y, (2 : ℤ) ∣ be y y)
instance (O : Type) [Ring O] [Module O X] : Module O (arcData k be hs hp he).toPre.X :=
  inferInstanceAs (Module O X)
theorem arcData_tau_isConst (y z : X) :
    IsConst ((arcData k be hs hp he).toPre.tau y z) (unitOn (arcVar k ^ (be y z))) :=
  (tau_isConst (arcExp k be) y z).of_eq (congrArg unitOn (polar_arcExp k be hs he y z))
def arcOAct (O : Type) [Ring O] [StarRing O] [Module O X]
    (ha : ∀ (a : O) y z, be (a • y) z = be y (star a • z)) : (arcData k be hs hp he).toPre.OAct O :=
  toricOAct (arcExp k be) O fun a y z => by rw [polar_arcExp k be hs he, polar_arcExp k be hs he, ha]
end ThetaShiftProofs
section Base
theorem left_eq_hom {S : Scheme.{0}} {T : Over S} (x : T ⟶ (zeroPolAV S).A) : x.left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w x)
variable (q : X → (FractionRing K)ˣ)
def baseMap {K' : Type} [CommRing K'] [IsDomain K'] (f : K →+* K') (q' : X → (FractionRing K')ˣ) :
    (toricPre K' X q').P.A.left ⟶ (toricPre K X q).P.A.left := spMap f
def baseIso {K' : Type} [CommRing K'] [IsDomain K'] (f : K →+* K') (q' : X → (FractionRing K')ˣ) :
    LB.Iso (toricPre K' X q').P.L ((toricPre K X q).P.L.pull (baseMap q f q')) := ⟨fun _ => 1⟩
variable {K' : Type} [CommRing K'] [IsDomain K']
theorem left_baseMap (f : K →+* K') (q' : X → (FractionRing K')ˣ) {T : Over (Sp K')}
    (x : T ⟶ (toricPre K' X q').P.A) : x.left ≫ baseMap q f q' = T.hom ≫ spMap f :=
  congrArg (· ≫ spMap f) (left_eq_hom x)
variable (f : K →+* K') (q' : X → (FractionRing K')ˣ)
theorem end_baseMap (g' : (toricPre K' X q').P.A ⟶ (toricPre K' X q').P.A)
    (g : (toricPre K X q).P.A ⟶ (toricPre K X q).P.A) :
    g'.left ≫ baseMap q f q' = baseMap q f q' ≫ g.left :=
  (left_baseMap q f q' g').trans
    ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
      (congrArg (spMap f ≫ ·) (left_eq_hom g).symm)))
theorem valF_gv_unitOn {F : Type} [Field F] {V : (Sp F).Opens} (hV : V = ⊤) (a : Fˣ) :
    valF (𝟙 (Sp F)) V (gv (unitOn a) V).val = a := by
  subst hV
  have h : (⊤ : (Sp F).Opens) ≤ (𝟙 (Sp F) : Sp F ⟶ Sp F) ⁻¹ᵁ ⊤ := le_rfl
  rw [valF, dif_pos h, gv, res_self]
  have e : Scheme.Hom.appLE (𝟙 (Sp F)) ⊤ ⊤ h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp]
    exact (Sp F).presheaf.map_id _
  rw [e]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (a : F)
theorem valF_one {F : Type} [Field F] {Y : Scheme.{0}} (x : Sp F ⟶ Y) {U : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valF x U 1 = 1 := by
  rw [valF, dif_pos h, map_one, map_one]
theorem genRel_baseIso_iff {F : Type} [Field F] {J : Type} [Fintype J]
    {pt : J → (Sp F ⟶ (toricPre K' X q').P.A.left)} {pt₀ : J → (Sp F ⟶ (toricPre K X q).P.A.left)} {ε : J → ℤ}
    {t : LB.Gen (LB.LinComb (toricPre K' X q').P.L pt ε)} {t₀ : LB.Gen (LB.LinComb (toricPre K X q).P.L pt₀ ε)}
    {a a₀ : Fˣ} (ht : IsConst t (unitOn a)) (ht₀ : IsConst t₀ (unitOn a₀)) (x : F) :
    GenRel (baseIso q f q') t t₀ x ↔ (∀ j, pt j ≫ baseMap q f q' = pt₀ j) ∧ (a : F) = x * a₀ := by
  have hc : ∀ (j : J → (toricPre K' X q').P.L.ι) (j₀ : J → (toricPre K X q).P.L.ι) (i : J), ⊤ ≤ pt i ⁻¹ᵁ
      (LB.div ((toricPre K X q).P.L.pull (baseMap q f q')) (toricPre K' X q').P.L).U (fun _ => j₀ i, j i) :=
    fun j j₀ i _ _ => ⟨Set.mem_iInter.2 fun _ => trivial, trivial⟩
  have key : ∀ (j : J → (toricPre K' X q').P.L.ι) (j₀ : J → (toricPre K X q).P.L.ι),
      (valF (𝟙 (Sp F)) _ (t.s j).val =
        x * (∏ i, valF (pt i) _ ((baseIso q f q').s (fun _ => j₀ i, j i)).val ^ (-ε i)) *
          valF (𝟙 (Sp F)) _ (t₀.s j₀).val) ↔ (a : F) = x * a₀ := by
    intro j j₀
    have e₁ : valF (𝟙 (Sp F)) _ (t.s j).val = a := by rw [ht j]; exact valF_gv_unitOn (wchart_triv _ _) a
    have e₂ : valF (𝟙 (Sp F)) _ (t₀.s j₀).val = a₀ := by rw [ht₀ j₀]; exact valF_gv_unitOn (wchart_triv _ _) a₀
    have e₃ : ∀ i, valF (pt i) _ ((baseIso q f q').s (fun _ => j₀ i, j i)).val = 1 :=
      fun i => valF_one _ (hc j j₀ i)
    simp only [e₁, e₂, e₃, one_zpow, Finset.prod_const_one, _root_.mul_one]
  exact and_congr_right fun _ =>
    ⟨fun h => (key (fun _ => PUnit.unit) (fun _ => PUnit.unit)).1 (h _ _ (hc _ _)),
      fun h j j₀ _ => (key j j₀).2 h⟩
variable (F : Type) [Field F] [Algebra (FractionRing K') F] [Algebra (FractionRing K) F]
theorem jFK_spMap
    (hF : ∀ x, algebraMap (FractionRing K) F (algebraMap K _ x) = algebraMap (FractionRing K') F (algebraMap K' _ (f x))) :
    (TF (R := K') F).hom ≫ spMap f = (TF (R := K) F).hom := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact (hF x).symm
theorem pointF_baseMap
    (hF : ∀ x, algebraMap (FractionRing K) F (algebraMap K _ x) = algebraMap (FractionRing K') F (algebraMap K' _ (f x)))
    (b' : TF (R := K') F ⟶ (toricPre K' X q').P.A) (b : TF (R := K) F ⟶ (toricPre K X q).P.A) :
    b'.left ≫ baseMap q f q' = b.left :=
  (left_baseMap q f q' b').trans ((jFK_spMap f F hF).trans (left_eq_hom b).symm)
theorem genRel_pt_iff
    (hF : ∀ x, algebraMap (FractionRing K) F (algebraMap K _ x) = algebraMap (FractionRing K') F (algebraMap K' _ (f x)))
    (t' t : Multiplicative X →* Fˣ) (χ' χ : X) (x : F) :
    GenRel (baseIso q f q') ((pt q' F t').s χ') ((pt q F t).s χ) x ↔
      (t' (Multiplicative.ofAdd χ') : F) = x * t (Multiplicative.ofAdd χ) := by
  refine (genRel_baseIso_iff q f q' (pt_isConst q' F t' χ') (pt_isConst q F t χ) x).trans (and_iff_right fun i => ?_)
  fin_cases i <;> exact pointF_baseMap q f q' F hF _ _
end Base
section Examples
def twoMul : LinearMap.BilinForm ℤ ℤ := (2 : ℤ) • LinearMap.mul ℤ ℤ
theorem twoMul_apply (a b : ℤ) : twoMul a b = 2 * (a * b) := rfl
theorem arcExp_twoMul (k : Type) [Field k] (n : ℤ) : arcExp k twoMul n = arcVar k ^ (n ^ 2) := by
  rw [arcExp_eq, twoMul_apply, Int.mul_ediv_cancel_left _ two_ne_zero, sq]
def arcDataInt (k : Type) [Field k] : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData k twoMul (fun a b => by rw [twoMul_apply, twoMul_apply, mul_comm a])
    (fun a ha => by rw [twoMul_apply]; exact mul_pos two_pos (mul_self_pos.2 ha))
    (fun a => ⟨a * a, twoMul_apply a a⟩)
example : (arcDataInt ℚ).toPre = tatePre :=
  (congrArg (toricPre _ ℤ) (funext (arcExp_twoMul ℚ))).trans toricPre_tate
example (k : Type) [Field k] :
    (arcDataInt k).toPre.PsiIn (2 : ℤ) (Ideal.span {PowerSeries.X} ^ 4) ∧
      ¬ (arcDataInt k).toPre.PsiIn (2 : ℤ) (Ideal.span {PowerSeries.X} ^ 5) ∧
      ¬ (arcDataInt k).toPre.PsiIn (0 : ℤ) (Ideal.span {PowerSeries.X} ^ 1) :=
  ⟨(psiIn_arcExp_iff k twoMul 2 4).2 (by decide), fun h => absurd ((psiIn_arcExp_iff k twoMul 2 5).1 h) (by decide),
    fun h => absurd ((psiIn_arcExp_iff k twoMul 0 1).1 h) (by decide)⟩
example (k : Type) [Field k] :
    IsConst ((arcDataInt k).toPre.tau (1 : ℤ) (1 : ℤ)) (unitOn (arcVar k ^ (2 : ℤ))) ∧
      IsConst ((arcDataInt k).toPre.tau (1 : ℤ) (-1 : ℤ)) (unitOn (arcVar k ^ (-2 : ℤ))) ∧
      arcVar k ^ (2 : ℤ) ≠ arcVar k ^ (-2 : ℤ) :=
  ⟨arcData_tau_isConst k twoMul _ _ _ 1 1, arcData_tau_isConst k twoMul _ _ _ 1 (-1),
    fun h => absurd (arcVar_zpow_injective k h) (by decide)⟩
example (k : Type) [Field k] (h) : ∃ o : (arcDataInt k).toPre.OAct ℤ, ∀ x,
    (o.onB.act x).left ≫ baseMap (fun _ : ℤ => 1) (PowerSeries.C (R := k)) (arcExp k twoMul) =
      baseMap (fun _ : ℤ => 1) (PowerSeries.C (R := k)) (arcExp k twoMul) ≫
        ((toricOAct (K := k) (fun _ : ℤ => 1) ℤ h).onB.act x).left :=
  ⟨arcOAct k twoMul _ _ _ ℤ fun a y z => by
      rw [twoMul_apply, twoMul_apply, star_trivial, smul_eq_mul, smul_eq_mul]
      ring,
    fun _ => end_baseMap _ _ _ _ _⟩
example {K' : Type} [CommRing K'] [IsDomain K'] (q : X → (FractionRing K)ˣ) (f : K →+* K')
    (q' : X → (FractionRing K')ˣ) (F : Type) [Field F] [Algebra (FractionRing K') F] [Algebra (FractionRing K) F]
    (hF : ∀ x, algebraMap (FractionRing K) F (algebraMap K _ x) = algebraMap (FractionRing K') F (algebraMap K' _ (f x)))
    (t : Multiplicative X →* Fˣ) (χ : X) (x : F) :
    GenRel (baseIso q f q') ((pt q' F t).s χ) ((pt q F t).s χ) x ↔ x = 1 := by
  rw [genRel_pt_iff q f q' F hF, eq_comm, mul_eq_right₀ (Units.ne_zero _)]
end Examples
end GlobalTheory.ToricData


