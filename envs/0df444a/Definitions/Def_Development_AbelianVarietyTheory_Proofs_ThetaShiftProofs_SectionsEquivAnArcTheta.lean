-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SectionsEquivAnArcTheta
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SectionsEquivAnArcTheta
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:23.196945+00:00
-- url     : https://prove2.me/theorems/4a92c020-7a0f-598a-b7c7-06cbaf42c9b6
-- title:
--   Sections Equiv An Arc Theta
-- statement:
--   Definitions and structural lemmas for Sections Equiv An Arc Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SectionsEquivAnArcTheta.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_smul_left
import Theorems.Thm_GlobalTheory_FrameValue_ahFactor_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_ahFactor_zero
import Theorems.Thm_GlobalTheory_FrameValue_differentiable_genVal
import Theorems.Thm_GlobalTheory_FrameValue_differentiable_secVal
import Theorems.Thm_GlobalTheory_FrameValue_frameProd_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_genVal_add_period
import Theorems.Thm_GlobalTheory_FrameValue_genVal_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_le_chartAt
import Theorems.Thm_GlobalTheory_FrameValue_le_wchart_chartAt
import Theorems.Thm_GlobalTheory_FrameValue_secVal_add_period
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_complex
import Theorems.Thm_P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0
import Theorems.Thm_P2M_GlobalTheory_FrameValue_valAt__sec_9a5221679090
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_gen_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.TwistedTheta
open CubeValues SymmetricSemicharacter EigenNorm FrameValue FieldBaseChange
section Germs
abbrev pt : Sp ℂ := (default : PrimeSpectrum ℂ)
def toStalk : ℂ →+* (Sp ℂ).presheaf.stalk pt :=
  ((Sp ℂ).presheaf.germ ⊤ pt trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
theorem gs_eq_toStalk {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    gs x pt U f = toStalk (valAt' x U f) := by
  rw [gs_eq x pt U (h trivial), valAt', dif_pos h, valAt, toStalk, RingHom.comp_apply]
  erw [(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h) pt trivial _).symm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Y Y' : Scheme.{0}} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ A.left)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ A.left)} {ε'' : K'' → ℤ}
theorem good_chartAt (hL : L.IsLB) : Good L pt (chartAt hL) := fun ψ => le_chartAt hL ψ trivial
theorem secVal_eq_mul (hL : L.IsLB) {s : LB.Sec (LB.LinComb L φ ε)} {s' : LB.Sec (LB.LinComb L φ' ε')}
    {t : LB.Gen (LB.LinComb L φ'' ε'')} {y : Sp ℂ ⟶ Y} {y' : Sp ℂ ⟶ Y'}
    (h : sval s y pt (chartAt hL) = sval s' y' pt (chartAt hL) * (val t y pt (chartAt hL)).val)
    {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ} {z'' : K'' → Fin g → ℂ}
    (hz : IsLift u φ y z) (hz' : IsLift u φ' y' z') (hz'' : IsLift u φ'' y z'')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = (∏ k, f (z' k) ^ ε' k) * ∏ k, f (z'' k) ^ ε'' k) :
    secVal u hL s y z = secVal u hL s' y' z' * genVal u hL t y z'' := by
  have h₁ := le_wchart_chartAt hL φ y
  have h₂ := le_wchart_chartAt hL φ' y'
  have h₃ := le_wchart_chartAt hL φ'' y
  rw [secVal, secVal, genVal, secValIn, secValIn, genValIn, div_mul_div_comm]
  refine congrArg₂ (· / ·) (toStalk.injective ?_) ?_
  · exact (gs_eq_toStalk _ _ h₁ _).symm.trans (h.trans ((congrArg₂ (· * ·) (gs_eq_toStalk _ _ h₂ _)
      ((gs_unit y pt _ (h₃ trivial) _).symm.trans (gs_eq_toStalk _ _ h₃ _))).trans (map_mul _ _ _).symm))
  · have := congrArg (Units.coeHom ℂ) (hs fun w => Units.mk0 _ (u.fr_ne _ w (le_chartAt hL (u.ex w).left)))
    simp only [map_mul, map_prod, map_zpow, Units.coeHom_apply, Units.val_mk0] at this
    simp only [frameProd, hz _, hz' _, hz'' _]
    exact this
theorem secVal_add (hL : L.IsLB) (π : Y ⟶ Sp ℂ) (s t : SecOver π (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y)
    (z : K → Fin g → ℂ) : secVal u hL (s + t : SecOver π _) y z = secVal u hL s y z + secVal u hL t y z := by
  obtain ⟨e, he⟩ := (valueRules Y y).2.1 _ (le_wchart_chartAt hL φ y)
  simp only [secVal, secValIn, ← add_div]
  exact congrArg (· / _) ((he _).trans ((map_add e _ _).trans (congrArg₂ (· + ·) (he _).symm (he _).symm)))
theorem secVal_smul (hL : L.IsLB) (π : Y ⟶ Sp ℂ) (c : ℂ) (s : SecOver π (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y}
    (hy : y ≫ π = 𝟙 _) (z : K → Fin g → ℂ) : secVal u hL (c • s : SecOver π _) y z = c * secVal u hL s y z := by
  have h := le_wchart_chartAt hL φ y
  obtain ⟨e, he⟩ := (valueRules Y y).2.1 _ h
  simp only [secVal, secValIn, ← mul_div_assoc]
  exact congrArg (· / _) ((he _).trans ((map_mul e _ _).trans (congrArg₂ (· * ·)
    ((he _).symm.trans ((valueRules Y y).2.2.2.2.2 π hy _ c h)) (he _).symm)))
end Germs
section Space
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def thetaShift (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (j : ℕ) (c : Fin g → ℂ) :
    Submodule ℂ ((Fin g → ℂ) → ℂ) where
  carrier := {θ | Differentiable ℂ θ ∧ ∀ (l : u.Λ) z, θ (z + l) =
    (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ j *
      Complex.exp (Real.pi * hermForm Hm c l) * θ z}
  zero_mem' := ⟨differentiable_const 0, fun _ _ => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun l z => by
    simp only [Pi.add_apply, ha.2 l z, hb.2 l z]; ring⟩
  smul_mem' := fun r a ha => ⟨ha.1.const_smul r, fun l z => by
    simp only [Pi.smul_apply, smul_eq_mul, ha.2 l z]; ring⟩
variable {u} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
theorem ahFactor_translate (l : u.Λ) (z c : Fin g → ℂ) :
    ahFactor Hm χ l (z + c) = ahFactor Hm χ l z * Complex.exp (Real.pi * hermForm Hm c l) := by
  rw [ahFactor, ahFactor, hermForm_add_left, _root_.mul_assoc (χ l), ← Complex.exp_add]
  congr 2; ring
theorem exp_nsmul (j : ℕ) (b l : Fin g → ℂ) :
    Complex.exp (Real.pi * hermForm Hm (j • b) l) = Complex.exp (Real.pi * hermForm Hm b l) ^ j := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, hermForm_smul_left, ← Complex.exp_nat_mul]
  congr 1; ring
theorem isThetaFn_sub {j : ℕ} {b : Fin g → ℂ} {θ : (Fin g → ℂ) → ℂ} (h : θ ∈ thetaShift u Hm χ j (j • b)) :
    u.IsThetaFn Hm χ j fun z => θ (z - b) := by
  refine ⟨h.1.comp (differentiable_id.sub_const b), fun l z => ?_⟩
  have e := ahFactor_translate (Hm := Hm) (χ := χ) l (z - b) b
  rw [sub_add_cancel] at e
  show θ (z + l - b) = ahFactor Hm χ l z ^ j * θ (z - b)
  rw [add_sub_right_comm, h.2, exp_nsmul, e, mul_pow (ahFactor Hm χ l (z - b))]
  rfl
theorem ex_nsmul (u : HolUnif A L g) (j : ℕ) (b : Fin g → ℂ) : u.ex (j • b) = u.ex b ^ j := by
  induction j with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
theorem comp_const (x y : 𝟙_ (Over (Sp ℂ)) ⟶ A) : x ≫ toUnit A ≫ y = y := by
  rw [← Category.assoc, Subsingleton.elim (x ≫ toUnit A) (𝟙 _), Category.id_comp]
end Space
section Main
variable (D : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D.P.A D.P.L g) (j : ℕ) (α : D.X) (c : Fin g → ℂ)
abbrev SecSpace : Type := SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (Out.DegPre.famε j))
def secFn : SecSpace D j α →ₗ[ℂ] ((Fin g → ℂ) → ℂ) where
  toFun s z := secVal u D.P.isLB s (u.ex z).left ![z, z + c, c, 0]
  map_add' s t := funext fun _ => secVal_add _ _ s t _ _
  map_smul' r s := funext fun z => secVal_smul _ _ r s (Over.w (u.ex z)) _
variable {D u j α c}
theorem secFn_apply (s : D.SecB j α) (z : Fin g → ℂ) :
    secFn D u j α c s z = secVal u D.P.isLB s (u.ex z).left ![z, z + c, c, 0] := rfl
theorem isLift_fam (hc : u.ex c = D.c α) (z : Fin g → ℂ) :
    IsLift u (D.famφB α) (u.ex z).left ![z, z + c, c, 0] := fun k => by
  have e : ∀ (q : D.P.A ⟶ D.P.A) w, u.ex z ≫ q = u.ex w → (u.ex z).left ≫ q.left = (u.ex w).left :=
    fun q w hq => congrArg (fun m => m.left) hq
  fin_cases k
  · exact Category.comp_id _
  · exact e _ (z + c) ((MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id, comp_const, u.ex_add, hc]))
  · exact e _ c (by rw [comp_const, hc])
  · exact e _ 0 ((MonObj.comp_one _).trans (ex_zero u).symm)
theorem valAt'_eq_secFn (hc : u.ex c = D.c α) (s : D.SecB j α) (z : Fin g → ℂ) (i : Fin 4 → D.P.L.ι)
    (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D.P.L.wchart (D.famφB α) i) :
    valAt' (u.ex z).left (D.P.L.wchart (D.famφB α) i) (s.f i) = secFn D u j α c s z *
      (u.fr (i 0) z ^ ((j : ℤ) - 1) * u.fr (i 1) (z + c) * (u.fr (i 2) c)⁻¹ * u.fr (i 3) 0) := by
  refine (valAt'_sec D.P.isLB s (isLift_fam hc z) hi).trans (congrArg₂ (· * ·) rfl ?_)
  simp [frameProd, Fin.prod_univ_four, Out.DegPre.famε]
theorem secFn_injective (hc : u.ex c = D.c α) : Function.Injective (secFn D u j α c) := by
  intro s t h
  have := D.P.isAb.smooth
  have := isReduced_of_smooth_complex _ D.P.A.hom inferInstance
  refine DVR.SecOps.sec_ext fun i => ComplexPoints.eq_of_valAt'_eq D.P.A.hom _ _ _ fun x hx hi => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
  exact (valAt'_eq_secFn hc s z i hi).trans ((congrArg (· * _) (congrFun h z)).trans (valAt'_eq_secFn hc t z i hi).symm)
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
theorem secFn_mem (h : u.IsAH Hm χ) (hc : u.ex c = D.c α) (s : SecSpace D j α) :
    secFn D u j α c s ∈ thetaShift u Hm χ j c := by
  refine ⟨?_, fun l z => ?_⟩
  · have := differentiable_secVal D.P.isLB s (𝟙 _) (q := id) differentiable_id (z := fun z => ![z, z + c, c, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact isLift_fam hc w)
    simp only [id, Category.comp_id] at this
    exact this
  · have e : ![z + l, z + l + c, c, 0] = fun k => ![z, z + c, c, 0] k + ((![l, l, 0, 0] : Fin 4 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp
      abel
    refine (secFn_apply s _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (secFn_apply s z).symm))
    rw [ex_add_period u z l l.2, e, secVal_add_period D.P.isLB h s (isLift_fam hc z)]
    congr 1
    have n := ahFactor_ne_zero h l z
    simp only [Fin.prod_univ_four, Out.DegPre.famε, Matrix.cons_val, ahFactor_zero D.P.isLB h, ahFactor_translate,
      zpow_one, one_zpow, _root_.mul_one, zpow_sub₀ n, zpow_natCast]
    change _ = ahFactor Hm χ l z ^ j * _
    field_simp
abbrev transl (b : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A) : D.P.A ⟶ D.P.A := 𝟙 D.P.A * (toUnit D.P.A ≫ b)
theorem exists_gen_transl {b : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A} (hb : b ^ j = D.c α) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB α) fun _ : PUnit => (transl b).left)
      (Sum.elim (Out.DegPre.famε j) fun _ => -(j : ℤ))), t.IsGen := by
  obtain ⟨t₁, h₁, -⟩ := exists_cubN D.cub (1 : D.P.A ⟶ D.P.A) (toUnit _ ≫ b) (𝟙 _) j
  obtain ⟨t₂, h₂⟩ := DVR.exists_gen_of_local (V := ℂ) D.P.L D.P.isLB (K := Fin 2)
    ![b.left, (1 : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A).left] ![-(j : ℤ), j]
  have e : (toUnit D.P.A ≫ b) ^ j = toUnit D.P.A ≫ D.c α := by rw [← hb, MonObj.comp_pow]
  have e₁ : (toUnit D.P.A).left ≫ b.left = (toUnit D.P.A ≫ b).left := rfl
  have e₂ : (toUnit D.P.A).left ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A).left = (1 : D.P.A ⟶ D.P.A).left :=
    congrArg (fun m : D.P.A ⟶ D.P.A => m.left) (MonObj.comp_one (toUnit D.P.A))
  have e₃ : D.famφB α = ![(𝟙 D.P.A : _ ⟶ _).left, (𝟙 D.P.A * (toUnit D.P.A ≫ D.c α)).left, (toUnit D.P.A ≫ D.c α).left,
    (1 : D.P.A ⟶ D.P.A).left] := rfl
  refine (exists_gen D.P.isLB (fun U _ f => ?_) _ (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁
    (DVR.pullGen_isGen _ _ _ _ h₂ (toUnit D.P.A).left))).imp fun t ht => ht.1
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, e₃, _root_.one_mul, _root_.one_mul, e,
    _root_.mul_comm (toUnit D.P.A ≫ D.c α), _root_.mul_comm (toUnit D.P.A ≫ b)]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_eight, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Out.DegPre.famε, Fintype.prod_unique]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module
theorem exists_secFn_eq (h : u.IsAH Hm χ) (hj : j ≠ 0) (hθ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ)
    (hc : u.ex c = D.c α) {θ : (Fin g → ℂ) → ℂ} (hm : θ ∈ thetaShift u Hm χ j c) : ∃ s, secFn D u j α c s = θ := by
  have hL := D.P.isLB
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℂ, c = j • b := ⟨(j : ℂ)⁻¹ • c, by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hj)]⟩
  obtain ⟨t, ht⟩ := exists_gen_transl (b := u.ex b) ((ex_nsmul u j b).symm.trans hc)
  have tr : ∀ z, (u.ex z).left ≫ (transl (u.ex b)).left = (u.ex (z + b)).left := fun z =>
    congrArg (fun m : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A => m.left) (show u.ex z ≫ transl (u.ex b) = u.ex (z + b) by
      rw [MonObj.comp_mul, Category.comp_id, comp_const, u.ex_add])
  have hz : ∀ z, IsLift u (Sum.elim (D.famφB α) fun _ : PUnit => (transl (u.ex b)).left) (u.ex z).left
      (Sum.elim ![z, z + j • b, j • b, 0] fun _ => z + b) := by
    rintro z (k | k)
    exacts [isLift_fam hc z k, tr z]
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → ℂ, ∀ z, V z =
    genVal u hL t (u.ex z).left (Sum.elim ![z, z + j • b, j • b, 0] fun _ => z + b) := ⟨_, fun _ => rfl⟩
  have hd : Differentiable ℂ V := by
    have := differentiable_genVal hL ht (𝟙 _) (q := id) differentiable_id
      (z := fun z => Sum.elim ![z, z + j • b, j • b, 0] fun _ => z + b)
      (by
        rintro (k | k)
        · fin_cases k <;> simp <;> fun_prop
        · simp)
      (fun w => by rw [id, Category.comp_id]; exact hz w)
    simpa only [id, Category.comp_id, ← hV] using this
  have hconst : ∀ z, V z = V 0 := fun z => entire_apply_eq_of_periodic_of_span_real hd u.full (fun w l hl => by
    have e : (Sum.elim ![w + l, w + l + j • b, j • b, 0] fun _ : PUnit => w + l + b) = fun k =>
        (Sum.elim ![w, w + j • b, j • b, 0] fun _ : PUnit => w + b) k +
          ((Sum.elim ![⟨l, hl⟩, ⟨l, hl⟩, 0, 0] (fun _ => ⟨l, hl⟩) : Fin 4 ⊕ PUnit → u.Λ) k : Fin g → ℂ) := by
      funext k
      rcases k with k | k
      · fin_cases k <;> simp
        abel
      · simp
        abel
    rw [hV, hV, ex_add_period u w l hl, e, genVal_add_period hL h t (hz w)]
    refine (congrArg (· * _) ?_).trans (_root_.one_mul _)
    have n := ahFactor_ne_zero h ⟨l, hl⟩ w
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      Out.DegPre.famε, Matrix.cons_val, ahFactor_zero hL h, ahFactor_translate, exp_nsmul,
      zpow_one, one_zpow, _root_.mul_one, zpow_sub₀ n, zpow_neg, zpow_natCast, mul_pow]
    field_simp) z 0
  have hne : V 0 ≠ 0 := (hV 0).symm ▸ genVal_ne_zero hL t (hz 0)
  obtain ⟨s, hs⟩ := hθ _ (isThetaFn_sub ((thetaShift u Hm χ j (j • b)).smul_mem (V 0)⁻¹ hm))
  obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := D.famφB α) (ε' := Out.DegPre.famε j) (fun U _ f => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Category.comp_id, zpow_neg]
    rw [_root_.mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec s (transl (u.ex b)).left t ht)
  refine ⟨σ, funext fun z => ?_⟩
  have hz' : IsLift u (fun _ : PUnit => 𝟙 D.P.A.left) (u.ex (z + b)).left fun _ => z + b := fun _ => Category.comp_id _
  have e := (hσ _ (u.ex z).left pt _ (good_chartAt hL)).trans (sval_pullMulSec s _ t ht _ pt (good_chartAt hL))
  rw [tr] at e
  have hi := le_wchart_chartAt hL (fun _ : PUnit => 𝟙 D.P.A.left) (u.ex (z + b)).left
  have v : secVal u hL s (u.ex (z + b)).left (fun _ => z + b) = (V 0)⁻¹ * θ z := by
    refine (div_eq_iff (frameProd_ne_zero hz' _ hi)).2 ((hs _ (z + b) hi).trans ?_)
    simp [frameProd]
  refine (secVal_eq_mul hL e (isLift_fam hc z) hz' (hz z) fun f => ?_).trans ?_
  · simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, zpow_neg]
    rw [_root_.mul_left_comm, mul_inv_cancel, _root_.mul_one]
  · rw [v, ← hV, hconst z, _root_.mul_right_comm, inv_mul_cancel₀ hne, _root_.one_mul]
def secEquiv (h : u.IsAH Hm χ) (hj : j ≠ 0) (hθ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ)
    (hc : u.ex c = D.c α) : SecSpace D j α ≃ₗ[ℂ] thetaShift u Hm χ j c :=
  LinearEquiv.ofBijective ((secFn D u j α c).codRestrict _ (secFn_mem h hc))
    ⟨fun _ _ e => secFn_injective hc (congrArg Subtype.val e),
      fun θ => (exists_secFn_eq h hj hθ hc θ.2).imp fun _ e => Subtype.ext e⟩
end Main
end GlobalTheory.TwistedTheta


