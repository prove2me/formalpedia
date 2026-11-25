-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:55.432565+00:00
-- url     : https://prove2.me/theorems/e7e9badd-e1a2-4381-a10f-9edd513688e6
-- title:
--   Eq Zero Of Semicharacter Multiplier
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Semicharacter Multiplier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_natCast_smul
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Pm_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_continuous_rl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_four_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ubox_sub_Icc
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_eq_of_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_add
import Theorems.Thm_ReciprocityTheory_PTheta_thetaCharShift_holds
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
namespace GlobalTheory
variable {ι : Type} [Fintype ι]
def thetaLevel (N : ℕ) (τ : Matrix ι ι ℂ) : Submodule ℂ ((ι → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ (n n' : ι → ℤ) (z : ι → ℂ),
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨hf.add hg, fun n n' z => by simp only [Pi.add_apply (f := f), hf', hg', mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, fun n n' z => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    exact ⟨hf.const_smul c, fun n n' z => by
      simp only [Pi.smul_apply, hf', smul_eq_mul]; ring⟩
def thetaLevelChar (a b : ι → ℝ) (N : ℕ) (τ : Matrix ι ι ℂ) : Submodule ℂ ((ι → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ (n n' : ι → ℤ) (z : ι → ℂ),
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC ((N : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨hf.add hg, fun n n' z => by simp only [Pi.add_apply (f := f), hf', hg', mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, fun n n' z => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    exact ⟨hf.const_smul c, fun n n' z => by
      simp only [Pi.smul_apply, hf', smul_eq_mul]; ring⟩
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
theorem mem_thetaLevel : f ∈ thetaLevel N τ ↔ Differentiable ℂ f ∧ ∀ (n n' : ι → ℤ) (z : ι → ℂ),
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z := Iff.rfl
theorem mem_thetaLevelChar : f ∈ thetaLevelChar a b N τ ↔ Differentiable ℂ f ∧
    ∀ (n n' : ι → ℤ) (z : ι → ℂ), f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC ((N : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z := Iff.rfl
theorem eC_ne_zero (x : ℂ) : eC x ≠ 0 := Complex.exp_ne_zero _
omit [Fintype ι] in
theorem ofRealVec_zero : ofRealVec (0 : ι → ℝ) = 0 := by ext i; simp [ofRealVec]
@[simp] theorem thetaLevelChar_zero (N : ℕ) (τ : Matrix ι ι ℂ) :
    thetaLevelChar 0 0 N τ = thetaLevel N τ := by
  ext f
  simp [mem_thetaLevelChar, mem_thetaLevel, ofRealVec_zero, eC_zero]
section Upper
open ReciprocityTheory.ChartRestriction.G.I2
def coeffMap (N : ℕ) (τ : Matrix ι ι ℂ) :
    thetaLevel N τ →ₗ[ℂ] ((Fin (Fintype.card ι) → Fin N) → ℂ) where
  toFun f := fun r => DimB.Av (DimB.Pm (fun z => f.1 (z ∘ Fintype.equivFin ι))
    (fun l => ((r l : ℕ) : ℤ))) 0
  map_add' f g := by
    funext r
    have hi : ∀ f : thetaLevel N τ, MeasureTheory.IntegrableOn (fun x =>
        DimB.Pm (fun z => f.1 (z ∘ Fintype.equivFin ι)) (fun l => ((r l : ℕ) : ℤ)) (DimB.rl x + 0))
        (DimB.ubox _) := fun f =>
      (ContinuousOn.integrableOn_compact isCompact_Icc
        ((DimB.Pm_diff _ (f.2.1.comp (by unfold Function.comp; fun_prop)) _).continuous.comp
          (DimB.continuous_rl.add continuous_const)).continuousOn).mono_set DimB.ubox_sub_Icc
    rw [Pi.add_apply, DimB.Av, DimB.Av, DimB.Av, ← MeasureTheory.integral_add (hi f) (hi g)]
    simp only [DimB.Pm, Submodule.coe_add, Pi.add_apply, add_mul]
  map_smul' c f := by
    funext r
    rw [Pi.smul_apply, DimB.Av, DimB.Av, RingHom.id_apply, smul_eq_mul,
      ← MeasureTheory.integral_const_mul]
    simp only [DimB.Pm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
theorem coeffMap_injective (hN : 0 < N) (τ : Matrix ι ι ℂ) :
    Function.Injective (coeffMap N τ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hT
  set e := Fintype.equivFin ι
  have hall : ∀ m : Fin (Fintype.card ι) → ℤ, (∀ l, 0 ≤ m l ∧ m l < N) →
      DimB.Av (DimB.Pm (fun z => f.1 (z ∘ e)) m) 0 = 0 := by
    intro m hm
    set r : Fin (Fintype.card ι) → Fin N := fun l => ⟨(m l).toNat, by have := hm l; omega⟩
    have hm' : (fun l => ((r l : ℕ) : ℤ)) = m := by
      funext l; simp only [r]; have := hm l; omega
    have := congrFun hT r
    rw [← hm']
    exact this
  set n : Fin (Fintype.card ι) → ι → ℤ := fun j => -Pi.single (e.symm j) 1 with hn
  have h0 := DimB.four_zero hN (fun z => f.1 (z ∘ e))
    (f.2.1.comp (by unfold Function.comp; fun_prop)) (fun l z => ?_)
    (fun j => (τ *ᵥ ofIntVec (n j)) ∘ e.symm)
    (fun j => eC (-(N : ℂ) * (ofIntVec (n j) ⬝ᵥ (τ *ᵥ ofIntVec (n j)) / 2))) (fun j z => ?_) hall
  · refine Subtype.ext (funext fun v => ?_)
    have := congrFun h0 (v ∘ e.symm)
    simpa [Function.comp_assoc] using this
  · have := f.2.2 0 (Pi.single (e.symm l) 1) (z ∘ e)
    rw [ofIntVec_zero] at this
    simp only [mulVec_zero, add_zero, zero_dotProduct, zero_div, mul_zero, eC_zero,
      one_mul] at this
    rw [← this]
    refine congrArg f.1 (funext fun i => ?_)
    simp [ofIntVec, Pi.single_apply, Equiv.eq_symm_apply]
  · have := f.2.2 (n j) 0 (z ∘ e)
    rw [ofIntVec_zero, add_zero] at this
    have h2 : (z + (τ *ᵥ ofIntVec (n j)) ∘ e.symm) ∘ e = z ∘ e + τ *ᵥ ofIntVec (n j) := by
      funext i; simp
    have h3 : ofIntVec (n j) ⬝ᵥ (z ∘ e) = -z j := by
      simp [hn, ofIntVec, dotProduct, Pi.single_apply]
    rw [h2, this, h3, mul_add, eC_add]
    congr 2
    unfold eC
    congr 1; ring
theorem finiteDimensional_thetaLevel (hN : 0 < N) (τ : Matrix ι ι ℂ) :
    FiniteDimensional ℂ (thetaLevel N τ) :=
  FiniteDimensional.of_injective _ (coeffMap_injective hN τ)
theorem finrank_thetaLevel_le (hN : 0 < N) (τ : Matrix ι ι ℂ) :
    Module.finrank ℂ (thetaLevel N τ) ≤ N ^ Fintype.card ι := by
  refine (LinearMap.finrank_le_finrank_of_injective (coeffMap_injective hN τ)).trans_eq ?_
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
end Upper
def thetaShift (a b : ι → ℝ) (N : ℕ) (τ : Matrix ι ι ℂ) :
    ((ι → ℂ) → ℂ) ≃ₗ[ℂ] ((ι → ℂ) → ℂ) where
  toFun f z := eC (N * (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b))) *
    f (z + τ *ᵥ ofRealVec a + ofRealVec b)
  invFun g w := eC (-(N * (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 +
    ofRealVec a ⬝ᵥ (w - τ *ᵥ ofRealVec a)))) * g (w - τ *ᵥ ofRealVec a - ofRealVec b)
  map_add' f g := by funext z; simp [mul_add]
  map_smul' c f := by funext z; simp [mul_left_comm]
  left_inv f := by
    funext w
    simp only
    rw [show w - τ *ᵥ ofRealVec a - ofRealVec b + τ *ᵥ ofRealVec a + ofRealVec b = w by abel,
      sub_add_cancel, ← mul_assoc, ← eC_add, neg_add_cancel, eC_zero, one_mul]
  right_inv g := by
    funext z
    simp only
    rw [show z + τ *ᵥ ofRealVec a + ofRealVec b - τ *ᵥ ofRealVec a = z + ofRealVec b by abel,
      add_sub_cancel_right, ← mul_assoc, ← eC_add, add_neg_cancel, eC_zero, one_mul]
theorem thetaShift_apply (f : (ι → ℂ) → ℂ) (z : ι → ℂ) : thetaShift a b N τ f z =
    eC (N * (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b))) *
      f (z + τ *ᵥ ofRealVec a + ofRealVec b) := rfl
theorem thetaShift_symm_apply (g : (ι → ℂ) → ℂ) (w : ι → ℂ) : (thetaShift a b N τ).symm g w =
    eC (-(N * (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (w - τ *ᵥ ofRealVec a)))) *
      g (w - τ *ᵥ ofRealVec a - ofRealVec b) := rfl
theorem differentiable_thetaShift_iff :
    Differentiable ℂ (thetaShift a b N τ f) ↔ Differentiable ℂ f := by
  constructor
  · intro h
    rw [← (thetaShift a b N τ).symm_apply_apply f]
    generalize thetaShift a b N τ f = g at h
    have : (thetaShift a b N τ).symm g = fun w => _ := funext (thetaShift_symm_apply g)
    rw [this]
    simp only [eC, dotProduct]
    fun_prop
  · intro h
    have : thetaShift a b N τ f = fun w => _ := funext (thetaShift_apply f)
    rw [this]
    simp only [eC, dotProduct]
    fun_prop
theorem thetaShift_mem_iff (hτ : τ.IsSymm) (a' b' : ι → ℝ) :
    thetaShift a b N τ f ∈ thetaLevelChar (a' + a) (b' + b) N τ ↔
      f ∈ thetaLevelChar a' b' N τ := by
  rw [mem_thetaLevelChar, mem_thetaLevelChar, differentiable_thetaShift_iff]
  refine and_congr_right fun _ => forall₂_congr fun n n' => ?_
  rw [← (Equiv.addRight (τ *ᵥ ofRealVec a + ofRealVec b)).forall_congr_right (q := fun z =>
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') = _ * f z)]
  refine forall_congr' fun z => ?_
  simp only [Equiv.coe_addRight, ← add_assoc z]
  rw [thetaShift_apply, thetaShift_apply,
    show z + τ *ᵥ ofIntVec n + ofIntVec n' + τ *ᵥ ofRealVec a + ofRealVec b =
      z + τ *ᵥ ofRealVec a + ofRealVec b + τ *ᵥ ofIntVec n + ofIntVec n' by abel,
    ← mul_right_inj' (eC_ne_zero (N * (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 +
      ofRealVec a ⬝ᵥ (z + τ *ᵥ ofIntVec n + ofIntVec n' + ofRealVec b))))
      (b := f (z + τ *ᵥ ofRealVec a + ofRealVec b + τ *ᵥ ofIntVec n + ofIntVec n'))]
  refine Eq.congr_right ?_
  simp only [← mul_assoc, ← eC_add]
  congr 2
  simp only [ofRealVec_add, dotProduct_add, add_dotProduct,
    dot_mulVec_symm hτ (ofIntVec n) (ofRealVec a), dotProduct_comm (ofRealVec b) (ofIntVec n)]
  ring
theorem map_thetaShift_thetaLevel (a b : ι → ℝ) (N : ℕ) (hτ : τ.IsSymm) :
    (thetaLevel N τ).map (thetaShift a b N τ).toLinearMap = thetaLevelChar a b N τ := by
  ext g
  obtain ⟨f, rfl⟩ := (thetaShift a b N τ).surjective g
  have := thetaShift_mem_iff (a := a) (b := b) (N := N) (f := f) hτ 0 0
  rw [zero_add, zero_add, thetaLevelChar_zero] at this
  rw [this]
  exact Submodule.mem_map_equiv _ |>.trans (by simp)
def thetaLevelEquivChar (a b : ι → ℝ) (N : ℕ) (hτ : τ.IsSymm) :
    thetaLevel N τ ≃ₗ[ℂ] thetaLevelChar a b N τ :=
  (thetaShift a b N τ).ofSubmodules _ _ (map_thetaShift_thetaLevel a b N hτ)
@[simp] theorem thetaLevelEquivChar_apply (hτ : τ.IsSymm) (f : thetaLevel N τ) :
    (thetaLevelEquivChar a b N hτ f : (ι → ℂ) → ℂ) = thetaShift a b N τ f := rfl
def levelTheta (a b : ι → ℝ) (N : ℕ) (τ : Matrix ι ι ℂ) (c : ι → ℤ) (z : ι → ℂ) : ℂ :=
  theta ((fun i => (c i : ℝ) / N) + a) ((N : ℝ) • b) ((N : ℂ) • z) ((N : ℂ) • τ)
theorem levelTheta_zero_zero (c : ι → ℤ) (z : ι → ℂ) :
    levelTheta 0 0 N τ c z = theta (fun i => (c i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  simp [levelTheta]
omit [Fintype ι] in
theorem ofRealVec_natCast_smul (N : ℕ) (b : ι → ℝ) :
    ofRealVec ((N : ℝ) • b) = (N : ℂ) • ofRealVec b := by
  ext i; simp [ofRealVec]
omit [Fintype ι] in
theorem ofIntVec_natCast_smul (N : ℕ) (n : ι → ℤ) :
    ofIntVec ((N : ℤ) • n) = (N : ℂ) • ofIntVec n := by
  ext i; simp [ofIntVec]
theorem thetaShift_levelTheta (hτ : τ.IsSymm) (c : ι → ℤ) :
    thetaShift a b N τ (levelTheta 0 0 N τ c) = levelTheta a b N τ c := by
  funext z
  have h := thetaCharShift_holds ι a ((N : ℝ) • b) (fun i => (c i : ℝ) / N) 0 ((N : ℂ) • z)
    ((N : ℂ) • τ) (hτ.smul _)
  rw [zero_add, ofRealVec_zero, add_zero, ofRealVec_natCast_smul] at h
  rw [thetaShift_apply, levelTheta_zero_zero, levelTheta, h, smul_add, smul_add, smul_mulVec]
  congr 2
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring
theorem smul_mem_siegelH (hτ : τ ∈ SiegelH ι) (hN : 0 < N) : (N : ℂ) • τ ∈ SiegelH ι :=
  have h : IsSiegel τ := ⟨hτ.1, hτ.2⟩
  ⟨(h.natCast_smul hN).1, (h.natCast_smul hN).2⟩
theorem differentiable_theta (hτ : τ ∈ SiegelH ι) (a b : ι → ℝ) :
    Differentiable ℂ fun z => theta a b z τ :=
  IsSiegel.differentiable_riemannTheta (Ω := τ) ⟨hτ.1, hτ.2⟩ a b
theorem theta_ne_zero (hτ : τ ∈ SiegelH ι) (a b : ι → ℝ) : (fun z => theta a b z τ) ≠ 0 :=
  IsSiegel.riemannTheta_ne_zero (Ω := τ) ⟨hτ.1, hτ.2⟩ a b
theorem levelTheta_ne_zero (hτ : τ ∈ SiegelH ι) (hN : 0 < N) (c : ι → ℤ) :
    levelTheta a b N τ c ≠ 0 := by
  intro h
  refine theta_ne_zero (smul_mem_siegelH hτ hN) ((fun i => (c i : ℝ) / N) + a) ((N : ℝ) • b)
    (funext fun w => ?_)
  have := congrFun h ((N : ℂ)⁻¹ • w)
  rwa [levelTheta, smul_inv_smul₀ (by exact_mod_cast hN.ne')] at this
theorem levelTheta_mem (hτ : τ ∈ SiegelH ι) (hN : 0 < N) (c : ι → ℤ) :
    levelTheta a b N τ c ∈ thetaLevelChar a b N τ := by
  refine ⟨(differentiable_theta (smul_mem_siegelH hτ hN) _ _).comp
    (differentiable_id.const_smul (N : ℂ)), fun n n' z => ?_⟩
  have h := thetaQuasiPeriod_holds ι ((fun i => (c i : ℝ) / N) + a) ((N : ℝ) • b) ((N : ℂ) • z)
    ((N : ℂ) • τ) n ((N : ℤ) • n') (hτ.1.smul _)
  rw [ofIntVec_natCast_smul, smul_mulVec, ← smul_add, ← smul_add] at h
  rw [levelTheta, h, levelTheta, autFactor, ← eC_add, ← eC_add]
  congr 1
  refine eC_eq_of_int _ _ (c ⬝ᵥ n') ?_
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : (N : ℂ) * (ofRealVec (fun i => (c i : ℝ) / N) ⬝ᵥ ofIntVec n') = ((c ⬝ᵥ n' : ℤ) : ℂ) := by
    simp only [dotProduct, ofRealVec, ofIntVec, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by field_simp
  rw [← h1]
  simp only [ofIntVec_natCast_smul, ofRealVec_natCast_smul, ofRealVec_add, smul_mulVec,
    add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring
theorem levelTheta_add_div (hτ : τ.IsSymm) (hN : 0 < N) (c m : ι → ℤ) (z : ι → ℂ) :
    levelTheta 0 0 N τ c (z + (N : ℂ)⁻¹ • ofIntVec m) =
      eC (((c ⬝ᵥ m : ℤ) : ℂ) / N) * levelTheta 0 0 N τ c z := by
  have h := thetaQuasiPeriod_holds ι (fun i => (c i : ℝ) / N) 0 ((N : ℂ) • z)
    ((N : ℂ) • τ) 0 m (hτ.smul _)
  rw [levelTheta_zero_zero, levelTheta_zero_zero, smul_add,
    smul_inv_smul₀ (by exact_mod_cast hN.ne')]
  rw [autFactor, ofIntVec_zero] at h
  simp only [mulVec_zero, add_zero, dotProduct_zero, zero_dotProduct, sub_zero, neg_zero, zero_div,
    eC_zero, mul_one] at h
  rw [h]
  congr 2
  simp only [dotProduct, ofRealVec, ofIntVec]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem intCast_zmod_eq_of_eC_eq (hN : 0 < N) {p q : ℤ} (h : eC (p / N) = eC (q / N)) :
    (p : ZMod N) = q := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (p : ℂ) = q + N * k := by
    have h3 : (p : ℂ) / N = q / N + k :=
      mul_left_cancel₀ Complex.two_pi_I_ne_zero (by rw [hk]; ring)
    field_simp at h3
    exact h3
  have h4 : p = q + N * k := by exact_mod_cast h2
  simp [h4]
theorem linearIndependent_levelTheta (hτ : τ ∈ SiegelH ι) (hN : 0 < N) {κ : Type*}
    {r : κ → ι → ℤ} (hr : Function.Injective fun k i => (r k i : ZMod N)) :
    LinearIndependent ℂ fun k => levelTheta a b N τ (r k) := by
  classical
  suffices h : LinearIndependent ℂ fun k => levelTheta 0 0 N τ (r k) by
    simpa only [Function.comp_def, LinearEquiv.coe_coe, thetaShift_levelTheta hτ.1] using
      h.map' (thetaShift a b N τ).toLinearMap (LinearEquiv.ker _)
  let χ : κ → Multiplicative (ι → ℤ) →* ℂ := fun k =>
    { toFun := fun m => eC (((r k ⬝ᵥ m.toAdd : ℤ) : ℂ) / N)
      map_one' := by simp [eC_zero]
      map_mul' := fun m m' => by simp [dotProduct_add, add_div, eC_add] }
  have hχ : Function.Injective χ := fun k k' h => hr (funext fun i => by
    have := DFunLike.congr_fun h (Multiplicative.ofAdd (Pi.single i 1))
    simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, dotProduct_single, mul_one] at this
    exact intCast_zmod_eq_of_eC_eq hN this)
  have hli := (linearIndependent_monoidHom (Multiplicative (ι → ℤ)) ℂ).comp χ hχ
  rw [linearIndependent_iff'] at hli ⊢
  intro s w hw k hk
  by_contra hk0
  refine levelTheta_ne_zero (a := 0) (b := 0) hτ hN (r k) (funext fun z => ?_)
  have := hli s (fun k => w k * levelTheta 0 0 N τ (r k) z) (funext fun m => ?_) k hk
  · exact (mul_eq_zero.1 this).resolve_left hk0
  · have := congrFun hw (z + (N : ℂ)⁻¹ • ofIntVec m.toAdd)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, levelTheta_add_div hτ.1 hN,
      Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply, χ,
      MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => by ring
theorem finiteDimensional_thetaLevelChar (hτ : τ.IsSymm) (hN : 0 < N) :
    FiniteDimensional ℂ (thetaLevelChar a b N τ) :=
  have := finiteDimensional_thetaLevel hN τ
  (thetaLevelEquivChar a b N hτ).finiteDimensional
theorem finrank_thetaLevelChar (hτ : τ ∈ SiegelH ι) (hN : 0 < N) :
    Module.finrank ℂ (thetaLevelChar a b N τ) = N ^ Fintype.card ι := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have := finiteDimensional_thetaLevelChar (a := a) (b := b) hτ.1 hN
  refine le_antisymm ((thetaLevelEquivChar a b N hτ.1).finrank_eq ▸ finrank_thetaLevel_le hN τ) ?_
  have h := linearIndependent_levelTheta (a := a) (b := b) hτ hN
    (r := fun (c : ι → ZMod N) i => ((c i).val : ℤ)) (fun c c' h => by simpa using h)
  have h' : LinearIndependent ℂ fun c : ι → ZMod N =>
      (⟨_, levelTheta_mem hτ hN fun i => ((c i).val : ℤ)⟩ : thetaLevelChar a b N τ) :=
    LinearIndependent.of_comp (thetaLevelChar a b N τ).subtype h
  simpa using h'.fintype_card_le_finrank
theorem finrank_thetaLevel (hτ : τ ∈ SiegelH ι) (hN : 0 < N) :
    Module.finrank ℂ (thetaLevel N τ) = N ^ Fintype.card ι :=
  thetaLevelChar_zero N τ ▸ finrank_thetaLevelChar hτ hN
theorem span_levelTheta (hτ : τ ∈ SiegelH ι) (hN : 0 < N) {κ : Type*}
    {r : κ → ι → ℤ} (hr : Function.Bijective fun k i => (r k i : ZMod N)) :
    Submodule.span ℂ (Set.range fun k => levelTheta a b N τ (r k)) = thetaLevelChar a b N τ := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have := finiteDimensional_thetaLevelChar (a := a) (b := b) hτ.1 hN
  let e := Equiv.ofBijective _ hr
  let _ : Fintype κ := Fintype.ofEquiv _ e.symm
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact levelTheta_mem hτ hN _
  · rw [finrank_span_eq_card (linearIndependent_levelTheta hτ hN hr.1),
      finrank_thetaLevelChar hτ hN, Fintype.card_congr e]
    simp
def thetaLevelCharBasis (a b : ι → ℝ) (hτ : τ ∈ SiegelH ι) (hN : 0 < N) {κ : Type*}
    {r : κ → ι → ℤ} (hr : Function.Bijective fun k i => (r k i : ZMod N)) :
    Module.Basis κ ℂ (thetaLevelChar a b N τ) :=
  (Module.Basis.span (linearIndependent_levelTheta hτ hN hr.1)).map
    (LinearEquiv.ofEq _ _ (span_levelTheta hτ hN hr))
def thetaLevelBasis (hτ : τ ∈ SiegelH ι) (hN : 0 < N) {κ : Type*}
    {r : κ → ι → ℤ} (hr : Function.Bijective fun k i => (r k i : ZMod N)) :
    Module.Basis κ ℂ (thetaLevel N τ) :=
  (thetaLevelCharBasis 0 0 hτ hN hr).map (LinearEquiv.ofEq _ _ (thetaLevelChar_zero N τ))
example : Module.finrank ℂ (thetaLevel 3 !![1 + 2 * I, 1 / 2 + I; 1 / 2 + I, 2 * I]) = 9 := by
  rw [finrank_thetaLevel ⟨isSiegel_example.1, isSiegel_example.2⟩ (by norm_num)]
  simp
end GlobalTheory


