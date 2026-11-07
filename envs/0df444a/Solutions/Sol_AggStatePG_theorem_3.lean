-- Prove2me | solution 1 for AggStatePG.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T07:53:41.973338+00:00
-- url     : https://prove2.me/submissions/d79055f2-c16b-47d5-b9fd-000cc77aaeb5

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_Vstar
import Definitions.Def_AggStatePG_objective
import Definitions.Def_AggStatePG_aggSet
import Definitions.Def_AggStatePG_IsFirstOrderStationary
import Definitions.Def_AggStatePG_IsAggErrorBound

set_option autoImplicit false

namespace AggT3

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA AggStatePG

section Core

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- A matrix as an operator on the sup-normed space `S → ℝ`. -/
noncomputable def Lm (X : Matrix S S ℝ) : (S → ℝ) →L[ℝ] (S → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' X)

lemma Lm_apply (X : Matrix S S ℝ) (v : S → ℝ) : Lm X v = X.mulVec v := by
  simp [Lm, Matrix.toLin'_apply]

lemma Lm_add (X Y : Matrix S S ℝ) : Lm (X + Y) = Lm X + Lm Y := by
  ext1 v
  simp only [ContinuousLinearMap.add_apply, Lm_apply, Matrix.add_mulVec]

lemma Lm_smul (c : ℝ) (X : Matrix S S ℝ) : Lm (c • X) = c • Lm X := by
  ext1 v
  funext i
  simp [Lm_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma Lm_norm (X : Matrix S S ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a, ∑ b, |X a b| ≤ C) : ‖Lm X‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  rw [Lm_apply]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  rw [Real.norm_eq_abs]
  calc |Matrix.mulVec X x a| = |∑ b, X a b * x b| := rfl
    _ ≤ ∑ b, |X a b * x b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |X a b| * ‖x‖ := Finset.sum_le_sum fun b _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm x b) (abs_nonneg _)
    _ = (∑ b, |X a b|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (h a) (norm_nonneg _)

/-- The transition matrix of a (possibly signed) table `π`. -/
noncomputable def Tm (π : S → A → ℝ) (P : S → A → S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' => InducedTransition π P s s'

lemma Tm_apply (π : S → A → ℝ) (P : S → A → S → ℝ) (s s' : S) :
    Tm π P s s' = ∑ a, π s a * P s a s' := rfl

lemma occ_succ (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (n : ℕ) (s' : S) :
    OccupationDist π P s0 (n + 1) s' =
      ∑ s, OccupationDist π P s0 n s * InducedTransition π P s s' := rfl

lemma occ_zero (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 s : S) :
    OccupationDist π P s0 0 s = if s = s0 then 1 else 0 := rfl

lemma pow_apply_eq (π : S → A → ℝ) (P : S → A → S → ℝ) :
    ∀ (n : ℕ) (u : S → ℝ) (s0 : S),
      ((Lm (Tm π P)) ^ n) u s0 = ∑ s', OccupationDist π P s0 n s' * u s' := by
  intro n
  induction n with
  | zero =>
    intro u s0
    simp [occ_zero]
  | succ n ih =>
    intro u s0
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih]
    simp only [Lm_apply, Matrix.mulVec, dotProduct, Tm, Matrix.of_apply, occ_succ,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The value of any table whose discounted transition operator is a contraction is the
resolvent applied to the reward vector. -/
lemma value_eq (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (h : ‖γ • Lm (Tm π P)‖ < 1) (s : S) :
    PolicyValue π P r γ s =
      Ring.inverse (1 - γ • Lm (Tm π P)) (fun s => InducedReward π r s) s := by
  have hs : Summable (fun n => (γ • Lm (Tm π P)) ^ n) := summable_geometric_of_norm_lt_one h
  have hinv : Ring.inverse (1 - γ • Lm (Tm π P)) = ∑' n, (γ • Lm (Tm π P)) ^ n := by
    rw [NormedRing.inverse_one_sub _ h]; rfl
  let e : ((S → ℝ) →L[ℝ] (S → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s).comp
      (ContinuousLinearMap.apply ℝ (S → ℝ) (fun s => InducedReward π r s))
  have he : ∀ Y, e Y = Y (fun s => InducedReward π r s) s := fun Y => rfl
  rw [hinv, ← he, e.map_tsum hs]
  unfold PolicyValue
  congr 1
  funext n
  rw [he, smul_pow, ContinuousLinearMap.smul_apply, Pi.smul_apply, pow_apply_eq, smul_eq_mul]

lemma resolvent_fix (X : (S → ℝ) →L[ℝ] (S → ℝ)) (h : ‖X‖ < 1) (w : S → ℝ) :
    Ring.inverse (1 - X) w = w + X (Ring.inverse (1 - X) w) := by
  have hu : IsUnit (1 - X) := ⟨Units.oneSub X h, rfl⟩
  have h1 : (1 - X) (Ring.inverse (1 - X) w) = w := by
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu,
      ContinuousLinearMap.one_apply]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h1
  exact sub_eq_iff_eq_add.mp h1

lemma Tm_nonneg (π : S → A → ℝ) (P : S → A → S → ℝ) (hπ : IsPolicy π)
    (hP : IsTransitionKernel P) (s s' : S) : 0 ≤ Tm π P s s' :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')

lemma Tm_row (π : S → A → ℝ) (P : S → A → S → ℝ) (hπ : IsPolicy π)
    (hP : IsTransitionKernel P) (s : S) : ∑ s', Tm π P s s' = 1 := by
  simp only [Tm_apply]
  rw [Finset.sum_comm]
  have e : ∀ a, ∑ s', π s a * P s a s' = π s a := fun a => by
    rw [← Finset.mul_sum, (hP s a).2, mul_one]
  simp only [e]
  exact (hπ s).2

lemma norm_lt (π : S → A → ℝ) (P : S → A → S → ℝ) (hπ : IsPolicy π)
    (hP : IsTransitionKernel P) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) :
    ‖γ • Lm (Tm π P)‖ < 1 := by
  have hL : ‖Lm (Tm π P)‖ ≤ 1 := Lm_norm _ 1 zero_le_one fun a => by
    rw [← Tm_row π P hπ hP a]
    exact le_of_eq (Finset.sum_congr rfl fun b _ => abs_of_nonneg (Tm_nonneg π P hπ hP a b))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  calc γ * ‖Lm (Tm π P)‖ ≤ γ * 1 := mul_le_mul_of_nonneg_left hL h0
    _ < 1 := by linarith

lemma bellman (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hπ : IsPolicy π) (hP : IsTransitionKernel P) (h0 : 0 ≤ γ) (h1 : γ < 1) (s : S) :
    PolicyValue π P r γ s =
      InducedReward π r s + γ * ∑ s', Tm π P s s' * PolicyValue π P r γ s' := by
  have hn := norm_lt π P hπ hP γ h0 h1
  have hV : (fun s => PolicyValue π P r γ s) =
      Ring.inverse (1 - γ • Lm (Tm π P)) (fun s => InducedReward π r s) :=
    funext (value_eq π P r γ hn)
  have := congrFun (resolvent_fix _ hn (fun s => InducedReward π r s)) s
  rw [← hV] at this
  simp only at this
  rw [this]
  simp [Lm_apply, Matrix.mulVec, dotProduct]

lemma V_eq_sumQ (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hπ : IsPolicy π) (hP : IsTransitionKernel P) (h0 : 0 ≤ γ) (h1 : γ < 1) (s : S) :
    PolicyValue π P r γ s = ∑ a, π s a * QFunction π P r γ s a := by
  rw [bellman π P r γ hπ hP h0 h1 s]
  simp only [QFunction, InducedReward, Tm_apply, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s' _ => by ring

lemma cmp (π : S → A → ℝ) (P : S → A → S → ℝ) (hπ : IsPolicy π) (hP : IsTransitionKernel P)
    (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) (z : S → ℝ)
    (hz : ∀ s, 0 ≤ z s - γ * ∑ s', Tm π P s s' * z s') : ∀ s, 0 ≤ z s := by
  intro s0
  haveI : Nonempty S := ⟨s0⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ z Finset.univ_nonempty
  have key : z m ≤ ∑ s', Tm π P m s' * z s' := by
    calc z m = ∑ s', Tm π P m s' * z m := by rw [← Finset.sum_mul, Tm_row π P hπ hP, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (hm s' (Finset.mem_univ _)) (Tm_nonneg π P hπ hP m s')
  have h := hz m
  have hxm : 0 ≤ z m := by nlinarith [mul_le_mul_of_nonneg_left key h0]
  exact le_trans hxm (hm s0 (Finset.mem_univ _))

/-! ### The policy-to-operator maps on stacked vectors -/

noncomputable def dPl (P : S → A → S → ℝ) :
    EuclideanSpace ℝ (S × A) →ₗ[ℝ] ((S → ℝ) →L[ℝ] (S → ℝ)) where
  toFun y := Lm (Tm (asPolicy y) P)
  map_add' y z := by
    rw [← Lm_add]
    congr 1
    ext s s'
    simp [Tm_apply, asPolicy, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    rw [RingHom.id_apply, ← Lm_smul]
    congr 1
    ext s s'
    simp [Tm_apply, asPolicy, Finset.mul_sum, mul_assoc]

noncomputable def dP (P : S → A → S → ℝ) :
    EuclideanSpace ℝ (S × A) →L[ℝ] ((S → ℝ) →L[ℝ] (S → ℝ)) :=
  LinearMap.toContinuousLinearMap (dPl P)

lemma dP_apply (P : S → A → S → ℝ) (y : EuclideanSpace ℝ (S × A)) :
    dP P y = Lm (Tm (asPolicy y) P) := rfl

noncomputable def dRl (r : S → A → ℝ) : EuclideanSpace ℝ (S × A) →ₗ[ℝ] (S → ℝ) where
  toFun y := fun s => InducedReward (asPolicy y) r s
  map_add' y z := by
    funext s
    simp [InducedReward, asPolicy, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    funext s
    simp [InducedReward, asPolicy, Finset.mul_sum, mul_assoc]

noncomputable def dR (r : S → A → ℝ) : EuclideanSpace ℝ (S × A) →L[ℝ] (S → ℝ) :=
  LinearMap.toContinuousLinearMap (dRl r)

lemma dR_apply (r : S → A → ℝ) (y : EuclideanSpace ℝ (S × A)) :
    dR r y = fun s => InducedReward (asPolicy y) r s := rfl

noncomputable def ell (ρ : S → ℝ) : (S → ℝ) →L[ℝ] ℝ :=
  ∑ s, ρ s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s

lemma ell_apply (ρ : S → ℝ) (v : S → ℝ) : ell ρ v = ∑ s, ρ s * v s := by
  simp [ell]

/-- The discounted occupancy weights (unnormalised): `μ = ρᵀ (I - γ P_x)⁻¹`. -/
noncomputable def mu (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ)
    (x : EuclideanSpace ℝ (S × A)) (s : S) : ℝ :=
  ell ρ (Ring.inverse (1 - (γ • dP P) x) (Pi.single s 1))

lemma mu_ge (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1)
    (ρ : S → ℝ) (hρ : ∀ s, 0 ≤ ρ s) (x : EuclideanSpace ℝ (S × A))
    (hx : IsPolicy (asPolicy x)) (s : S) : ρ s ≤ mu P γ ρ x s := by
  have hxn : ‖(γ • dP P) x‖ < 1 := norm_lt (asPolicy x) P hx hP γ h0 h1
  have hfix := resolvent_fix _ hxn (Pi.single s (1 : ℝ))
  set z := Ring.inverse (1 - (γ • dP P) x) (Pi.single s (1 : ℝ)) with hz
  have hpt : ∀ s0, z s0 = (Pi.single s (1 : ℝ) : S → ℝ) s0 + γ * ∑ s', Tm (asPolicy x) P s0 s' * z s' := by
    intro s0
    have := congrFun hfix s0
    rw [this]
    simp [dP_apply, Lm_apply, Matrix.mulVec, dotProduct]
  have hsn : ∀ s0, (0 : ℝ) ≤ (Pi.single s (1 : ℝ) : S → ℝ) s0 := fun s0 => by
    by_cases h : s0 = s <;> simp [Pi.single_apply, h]
  have hz0 : ∀ s0, 0 ≤ z s0 := cmp (asPolicy x) P hx hP γ h0 h1 z (fun s0 => by
    linarith [hpt s0, hsn s0])
  have hge : ∀ s0, (Pi.single s (1 : ℝ) : S → ℝ) s0 ≤ z s0 := fun s0 => by
    have hs : 0 ≤ ∑ s', Tm (asPolicy x) P s0 s' * z s' :=
      Finset.sum_nonneg fun s' _ => mul_nonneg (Tm_nonneg _ P hx hP s0 s') (hz0 s')
    nlinarith [mul_nonneg h0 hs, hpt s0]
  have hmu : mu P γ ρ x s = ∑ s0, ρ s0 * z s0 := by rw [mu, ell_apply]
  rw [hmu]
  calc ρ s = ∑ s0, ρ s0 * (Pi.single s (1 : ℝ) : S → ℝ) s0 := by simp [Pi.single_apply]
    _ ≤ _ := Finset.sum_le_sum fun s0 _ => mul_le_mul_of_nonneg_left (hge s0) (hρ s0)

/-- The policy gradient formula at a point of the simplex. -/
lemma grad_formula (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ)
    (h0 : 0 ≤ γ) (h1 : γ < 1) (ρ : S → ℝ) (x : EuclideanSpace ℝ (S × A))
    (hx : IsPolicy (asPolicy x)) (v : EuclideanSpace ℝ (S × A)) :
    inner ℝ (gradient (Jext P r γ ρ) x) v =
      (1 - γ) * ∑ s, mu P γ ρ x s * ∑ a, v (s, a) * QFunction (asPolicy x) P r γ s a := by
  have hxn : ‖(γ • dP P) x‖ < 1 := norm_lt (asPolicy x) P hx hP γ h0 h1
  set u := Units.oneSub ((γ • dP P) x) hxn with hu_def
  set N := Ring.inverse (1 - (γ • dP P) x) with hN_def
  have hNu : ((u⁻¹ : ((S → ℝ) →L[ℝ] (S → ℝ))ˣ) : (S → ℝ) →L[ℝ] (S → ℝ)) = N := by
    rw [hN_def, NormedRing.inverse_one_sub _ hxn]
  have hA : HasFDerivAt (fun y => 1 - (γ • dP P) y) (-(γ • dP P)) x :=
    (γ • dP P).hasFDerivAt.const_sub 1
  have hI : HasFDerivAt (𝕜 := ℝ) Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ ((S → ℝ) →L[ℝ] (S → ℝ)) N N))
      (1 - (γ • dP P) x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hNu] at this
    exact this
  have hG := hI.comp x hA
  have hB := hG.clm_apply (dR r).hasFDerivAt
  have hF := (ell ρ).hasFDerivAt.comp x hB
  have hJ := hF.const_mul (1 - γ)
  have hU : IsOpen {y : EuclideanSpace ℝ (S × A) | ‖(γ • dP P) y‖ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hev : Jext P r γ ρ =ᶠ[nhds x]
      fun y => (1 - γ) * (ell ρ ∘ fun y => Ring.inverse (1 - (γ • dP P) y) (dR r y)) y := by
    filter_upwards [hU.mem_nhds hxn] with y hy
    have hy' : ‖γ • Lm (Tm (asPolicy y) P)‖ < 1 := hy
    show (1 - γ) * valueAt (asPolicy y) P r γ ρ = _
    rw [Function.comp_apply, ell_apply]
    congr 1
    unfold valueAt
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [value_eq _ P r γ hy' s]
    rfl
  have hJ' := hJ.congr_of_eventuallyEq hev
  have hlin : ∀ w : S → ℝ, ell ρ (N w) = ∑ s, mu P γ ρ x s * w s := by
    intro w
    have hw : w = ∑ s, w s • (Pi.single s (1 : ℝ) : S → ℝ) := by
      conv_lhs => rw [← Finset.univ_sum_single w]
      refine Finset.sum_congr rfl fun s _ => ?_
      ext j
      by_cases h : j = s <;> simp [Pi.single_apply, h]
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul, smul_eq_mul, mu]
    refine Finset.sum_congr rfl fun s _ => by rw [← hN_def]; ring
  have hY : ∀ w, ((-(ContinuousLinearMap.mulLeftRight ℝ ((S → ℝ) →L[ℝ] (S → ℝ)) N N))
      ((-(γ • dP P)) v)) w = N ((γ • dP P) v (N w)) := by
    intro w
    simp only [ContinuousLinearMap.neg_apply, map_neg, neg_neg,
      ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply]
  have hcomp : (Ring.inverse ∘ fun y => 1 - γ • (dP P) y) x = N := rfl
  have hV : N (dR r x) = fun s => PolicyValue (asPolicy x) P r γ s := by
    funext s
    exact (value_eq (asPolicy x) P r γ hxn s).symm
  rw [gradient, hJ'.fderiv, InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hcomp, hY, ← map_add, hlin, hV]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  simp only [Pi.add_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, dP_apply,
    dR_apply, Lm_apply, Matrix.mulVec, dotProduct, Tm_apply, QFunction, InducedReward, asPolicy,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s' _ => by ring

/-- Comparison: a policy whose `Q`-values exceed its values by at most `2ε` is
`2ε/(1-γ)`-optimal. -/
lemma value_bound (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ)
    (h0 : 0 ≤ γ) (h1 : γ < 1) (π0 : S → A → ℝ) (ε : ℝ)
    (key : ∀ s b, QFunction π0 P r γ s b ≤ PolicyValue π0 P r γ s + 2 * ε)
    (π : S → A → ℝ) (hπ : IsPolicy π) (s : S) :
    PolicyValue π P r γ s ≤ PolicyValue π0 P r γ s + 2 * ε / (1 - γ) := by
  haveI : Nonempty S := ⟨s⟩
  let D : S → ℝ := fun s => PolicyValue π P r γ s - PolicyValue π0 P r γ s
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ D Finset.univ_nonempty
  have hstep : ∀ s, D s ≤ 2 * ε + γ * D m := by
    intro s
    have hb := V_eq_sumQ π P r γ hπ hP h0 h1 s
    have hterm : ∀ a, QFunction π P r γ s a ≤ PolicyValue π0 P r γ s + 2 * ε + γ * D m := by
      intro a
      have e : QFunction π P r γ s a =
          QFunction π0 P r γ s a + γ * ∑ s', P s a s' * D s' := by
        simp only [QFunction, D, mul_sub, Finset.sum_sub_distrib]
        ring
      have hD : ∑ s', P s a s' * D s' ≤ D m := by
        calc ∑ s', P s a s' * D s' ≤ ∑ s', P s a s' * D m :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (hm s' (Finset.mem_univ _)) ((hP s a).1 s')
          _ = D m := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
      rw [e]
      nlinarith [key s a, mul_le_mul_of_nonneg_left hD h0]
    have hle : PolicyValue π P r γ s ≤ PolicyValue π0 P r γ s + 2 * ε + γ * D m := by
      rw [hb]
      calc ∑ a, π s a * QFunction π P r γ s a
          ≤ ∑ a, π s a * (PolicyValue π0 P r γ s + 2 * ε + γ * D m) :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hterm a) ((hπ s).1 a)
        _ = _ := by rw [← Finset.sum_mul, (hπ s).2, one_mul]
    show PolicyValue π P r γ s - PolicyValue π0 P r γ s ≤ _
    linarith
  have hmm := hstep m
  have h1' : 0 < 1 - γ := by linarith
  have hDm : D m ≤ 2 * ε / (1 - γ) := by
    rw [le_div_iff₀ h1']
    nlinarith
  have hs := le_trans (hm s (Finset.mem_univ _)) hDm
  show PolicyValue π P r γ s ≤ PolicyValue π0 P r γ s + 2 * ε / (1 - γ)
  have : PolicyValue π P r γ s - PolicyValue π0 P r γ s ≤ 2 * ε / (1 - γ) := hs
  linarith

end Core

/-- Stationarity on `Π_φ` plus the aggregation error bound give `Q ≤ V + 2ε`. -/
lemma key_ineq {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq ι]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (h0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (hseg : ∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), ρ s')
    (ε : ℝ) (hε : IsAggErrorBound P r γ φ ε)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf) (s0 : S) (b : A) :
    QFunction (asPolicy πinf) P r γ s0 b ≤ PolicyValue (asPolicy πinf) P r γ s0 + 2 * ε := by
  classical
  have hpol' : IsPolicy (asPolicy πinf) := hmem.1
  have hagg' : ∀ s s' : S, φ s = φ s' → ∀ a : A, πinf (s, a) = πinf (s', a) := hmem.2
  have hVQ : ∀ s, PolicyValue (asPolicy πinf) P r γ s =
      ∑ a, asPolicy πinf s a * QFunction (asPolicy πinf) P r γ s a :=
    fun s => V_eq_sumQ (asPolicy πinf) P r γ hpol' hP h0 hγ1 s
  have hQε : ∀ a s s', φ s = φ s' →
      |QFunction (asPolicy πinf) P r γ s a - QFunction (asPolicy πinf) P r γ s' a| ≤ ε :=
    fun a s s' h => hε πinf hmem a s s' h
  let x' : EuclideanSpace ℝ (S × A) := WithLp.toLp 2 (fun p : S × A =>
    if φ p.1 = φ s0 then (if p.2 = b then (1 : ℝ) else 0) else πinf p)
  have hx' : ∀ s a, x' (s, a) =
      if φ s = φ s0 then (if a = b then (1 : ℝ) else 0) else πinf (s, a) := fun s a => rfl
  have hx'mem : x' ∈ aggSet φ := by
    show x' ∈ simplexSet S A ∧ ∀ s s' : S, φ s = φ s' → ∀ a : A, x' (s, a) = x' (s', a)
    refine ⟨?_, fun s s' hss a => ?_⟩
    · show IsPolicy (asPolicy x')
      intro s
      refine ⟨fun a => ?_, ?_⟩
      · show 0 ≤ x' (s, a)
        rw [hx']
        split_ifs
        · norm_num
        · norm_num
        · exact (hpol' s).1 a
      · show ∑ a, x' (s, a) = 1
        simp only [hx']
        by_cases h : φ s = φ s0
        · simp [h]
        · simp only [h, if_false]
          exact (hpol' s).2
    · rw [hx', hx', hss]
      split_ifs <;> first | rfl | exact hagg' s s' hss a
  have hst := hstat.2 x' hx'mem
  rw [grad_formula P hP r γ h0 hγ1 ρ πinf hpol' (x' - πinf)] at hst
  have hg : ∀ s, ∑ a, (x' - πinf) (s, a) * QFunction (asPolicy πinf) P r γ s a =
      if φ s = φ s0 then QFunction (asPolicy πinf) P r γ s b -
        PolicyValue (asPolicy πinf) P r γ s else 0 := by
    intro s
    simp only [PiLp.sub_apply, hx']
    by_cases h : φ s = φ s0
    · simp only [h, if_true]
      rw [hVQ s]
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, asPolicy]
    · simp [h]
  simp only [hg, mul_ite, mul_zero] at hst
  rw [← Finset.sum_filter] at hst
  have h1' : 0 < 1 - γ := by linarith
  have hsum : ∑ s ∈ Finset.univ.filter (fun s => φ s = φ s0), mu P γ ρ πinf s *
      (QFunction (asPolicy πinf) P r γ s b - PolicyValue (asPolicy πinf) P r γ s) ≤ 0 := by
    by_contra hc
    push_neg at hc
    have := mul_pos h1' hc
    linarith
  have hterm : ∀ s ∈ Finset.univ.filter (fun s => φ s = φ s0),
      mu P γ ρ πinf s * (QFunction (asPolicy πinf) P r γ s0 b -
        PolicyValue (asPolicy πinf) P r γ s0 - 2 * ε) ≤
      mu P γ ρ πinf s * (QFunction (asPolicy πinf) P r γ s b -
        PolicyValue (asPolicy πinf) P r γ s) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have hseg' := hs.2
    have hmu : 0 ≤ mu P γ ρ πinf s :=
      le_trans (hρ.1 s) (mu_ge P hP γ h0 hγ1 ρ hρ.1 πinf hpol' s)
    refine mul_le_mul_of_nonneg_left ?_ hmu
    have e1 := abs_le.mp (hQε b s s0 hseg')
    have hVs : PolicyValue (asPolicy πinf) P r γ s ≤ PolicyValue (asPolicy πinf) P r γ s0 + ε := by
      rw [hVQ s, hVQ s0]
      calc ∑ a, asPolicy πinf s a * QFunction (asPolicy πinf) P r γ s a
          = ∑ a, asPolicy πinf s0 a * QFunction (asPolicy πinf) P r γ s a :=
            Finset.sum_congr rfl fun a _ => by
              show πinf (s, a) * _ = πinf (s0, a) * _
              rw [hagg' s s0 hseg' a]
        _ ≤ ∑ a, asPolicy πinf s0 a * (QFunction (asPolicy πinf) P r γ s0 a + ε) :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
              (by linarith [(abs_le.mp (hQε a s s0 hseg')).2]) ((hpol' s0).1 a)
        _ = ∑ a, asPolicy πinf s0 a * QFunction (asPolicy πinf) P r γ s0 a + ε := by
            simp only [mul_add, Finset.sum_add_distrib]
            rw [← Finset.sum_mul, (hpol' s0).2, one_mul]
    linarith [e1.1]
  have hmass : 0 < ∑ s ∈ Finset.univ.filter (fun s => φ s = φ s0), mu P γ ρ πinf s :=
    lt_of_lt_of_le (hseg s0)
      (Finset.sum_le_sum fun s _ => mu_ge P hP γ h0 hγ1 ρ hρ.1 πinf hpol' s)
  have h2 : (∑ s ∈ Finset.univ.filter (fun s => φ s = φ s0), mu P γ ρ πinf s) *
      (QFunction (asPolicy πinf) P r γ s0 b - PolicyValue (asPolicy πinf) P r γ s0 - 2 * ε) ≤ 0 := by
    rw [Finset.sum_mul]
    exact le_trans (Finset.sum_le_sum hterm) hsum
  by_contra hc
  push_neg at hc
  have : 0 < QFunction (asPolicy πinf) P r γ s0 b - PolicyValue (asPolicy πinf) P r γ s0 - 2 * ε := by
    linarith
  linarith [mul_pos hmass this]

theorem main_thm {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq ι]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (hseg : ∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), ρ s')
    (ε : ℝ) (hε : IsAggErrorBound P r γ φ ε)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf) :
    (∀ πstar : S → A → ℝ, IsPolicy πstar → (∀ s : S, PolicyValue πstar P r γ s = Vstar P r γ s) →
      objective P r γ ρ πstar - objective P r γ ρ (asPolicy πinf) ≤
        (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖) ∧
    (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖ ≤ 2 * ε := by
  have h0 : 0 ≤ γ := hγ0.le
  have h1' : 0 < 1 - γ := by linarith
  have hpol' : IsPolicy (asPolicy πinf) := hmem.1
  have hS : Nonempty S := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := hρ.2
    simp at this
  obtain ⟨s00⟩ := hS
  have hAne : Nonempty A := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := (hpol' s00).2
    simp at this
  obtain ⟨a00⟩ := hAne
  have hε0 : 0 ≤ ε := by
    have := hε πinf hmem a00 s00 s00 rfl
    simpa using this
  have key := key_ineq P hP r γ h0 hγ1 ρ hρ φ hseg ε hε πinf hmem hstat
  have hvb := value_bound P hP r γ h0 hγ1 (asPolicy πinf) ε key
  have hbdd : ∀ s, BddAbove {v : ℝ | ∃ π : S → A → ℝ, IsPolicy π ∧ PolicyValue π P r γ s = v} :=
    fun s => ⟨PolicyValue (asPolicy πinf) P r γ s + 2 * ε / (1 - γ), by
      rintro v ⟨π, hπ, rfl⟩
      exact hvb π hπ s⟩
  have hVs_le : ∀ s, Vstar P r γ s ≤ PolicyValue (asPolicy πinf) P r γ s + 2 * ε / (1 - γ) :=
    fun s => csSup_le ⟨_, asPolicy πinf, hpol', rfl⟩ (by
      rintro v ⟨π, hπ, rfl⟩
      exact hvb π hπ s)
  have hVs_ge : ∀ s, PolicyValue (asPolicy πinf) P r γ s ≤ Vstar P r γ s :=
    fun s => le_csSup (hbdd s) ⟨asPolicy πinf, hpol', rfl⟩
  have hnorm : ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖ ≤
      2 * ε / (1 - γ) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hVs_le s, hVs_ge s]
  refine ⟨?_, ?_⟩
  · intro πstar _ hstar
    have hpt : ∀ s, Vstar P r γ s - PolicyValue (asPolicy πinf) P r γ s ≤
        ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖ := fun s => by
      have := norm_le_pi_norm ((fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ) s
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      linarith [neg_abs_le (PolicyValue (asPolicy πinf) P r γ s - Vstar P r γ s)]
    simp only [objective, valueAt, hstar]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ?_ h1'.le
    calc ∑ s, (ρ s * Vstar P r γ s - ρ s * PolicyValue (asPolicy πinf) P r γ s)
        = ∑ s, ρ s * (Vstar P r γ s - PolicyValue (asPolicy πinf) P r γ s) := by
          simp only [mul_sub]
      _ ≤ ∑ s, ρ s * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖ :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hρ.1 s)
      _ = _ := by rw [← Finset.sum_mul, hρ.2, one_mul]
  · calc (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖
        ≤ (1 - γ) * (2 * ε / (1 - γ)) := mul_le_mul_of_nonneg_left hnorm h1'.le
      _ = 2 * ε := by field_simp

end AggT3

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA AggStatePG in
theorem solution {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq ι]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : IsDist ρ) (φ : S → ι)
    (hseg : ∀ s : S, 0 < ∑ s' ∈ Finset.univ.filter (fun s' => φ s' = φ s), ρ s')
    (ε : ℝ) (hε : IsAggErrorBound P r γ φ ε)
    (πinf : EuclideanSpace ℝ (S × A)) (hmem : πinf ∈ aggSet φ)
    (hstat : IsFirstOrderStationary P r γ ρ (aggSet φ) πinf) :
    (∀ πstar : S → A → ℝ, IsPolicy πstar → (∀ s : S, PolicyValue πstar P r γ s = Vstar P r γ s) →
      objective P r γ ρ πstar - objective P r γ ρ (asPolicy πinf) ≤
        (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖) ∧
    (1 - γ) * ‖(fun s => PolicyValue (asPolicy πinf) P r γ s) - Vstar P r γ‖ ≤ 2 * ε := by
  exact AggT3.main_thm P hP r γ hγ0 hγ1 ρ hρ φ hseg ε hε πinf hmem hstat
