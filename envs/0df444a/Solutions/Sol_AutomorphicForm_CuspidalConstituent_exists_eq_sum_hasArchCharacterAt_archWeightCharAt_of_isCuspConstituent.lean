-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/22ec5b06-484c-5972-930c-edf9d3c2ba10

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent

set_option autoImplicit false

noncomputable section
open MeasureTheory Complex AddCircle
open scoped Real

namespace EvalCoords

variable {X : Type*}

def vanishingOn (E : Submodule ℂ (X → ℂ)) (s : Finset X) : Submodule ℂ E where
  carrier := {e | ∀ x ∈ s, (e : X → ℂ) x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb x hx => by
    simp only [Submodule.coe_add, Pi.add_apply, ha x hx, hb x hx, add_zero]
  smul_mem' := fun c {a} ha x hx => by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha x hx, smul_zero]

theorem vanishingOn_mono (E : Submodule ℂ (X → ℂ)) {s t : Finset X} (h : s ⊆ t) :
    vanishingOn E t ≤ vanishingOn E s := fun _ he x hx => he x (h hx)

theorem exists_finset_separating (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ s : Finset X, ∀ e ∈ E, (∀ x ∈ s, e x = 0) → e = 0 := by
  classical

  have key : ∀ k : ℕ, k ≤ Module.finrank ℂ E →
      ∃ s : Finset X, Module.finrank ℂ (vanishingOn E s) ≤ Module.finrank ℂ E - k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, (Submodule.finrank_le _).trans le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hs⟩ := ih (Nat.le_of_succ_le hk)
      by_cases hbot : vanishingOn E s = ⊥
      · refine ⟨s, ?_⟩
        rw [hbot, finrank_bot]
        exact Nat.zero_le _
      · obtain ⟨e, he, hne⟩ := (Submodule.ne_bot_iff _).mp hbot
        have hne' : (e : X → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
        obtain ⟨x, hx⟩ := Function.ne_iff.mp hne'
        refine ⟨insert x s, ?_⟩
        have hlt : vanishingOn E (insert x s) < vanishingOn E s := by
          refine lt_of_le_of_ne (vanishingOn_mono E (Finset.subset_insert x s)) fun h => ?_
          have : e ∈ vanishingOn E (insert x s) := h ▸ he
          exact hx (this x (Finset.mem_insert_self x s))
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
  obtain ⟨s, hs⟩ := key (Module.finrank ℂ E) le_rfl
  rw [Nat.sub_self, Nat.le_zero] at hs
  refine ⟨s, fun e he h0 => ?_⟩
  have hmem : (⟨e, he⟩ : E) ∈ vanishingOn E s := h0
  rw [Submodule.finrank_eq_zero.mp hs, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem exists_eval_coords (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (s : Finset X) (b : X → X → ℂ), (∀ x, b x ∈ E) ∧ ∀ e ∈ E, e = ∑ x ∈ s, e x • b x := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating E

  let res : E →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun e x => (e : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker res = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun e he => ?_
    rw [LinearMap.mem_ker] at he
    apply Subtype.ext
    exact hs e e.2 fun x hx => congrFun he ⟨x, hx⟩
  obtain ⟨g, hg⟩ := res.exists_leftInverse_of_injective hker
  let b : X → X → ℂ := fun x => if hx : x ∈ s then ((g (Pi.single (⟨x, hx⟩ : s) 1) : E) : X → ℂ) else 0
  refine ⟨s, b, fun x => ?_, fun e he => ?_⟩
  · simp only [b]
    split_ifs
    · exact Submodule.coe_mem _
    · exact E.zero_mem
  · have h1 : (⟨e, he⟩ : E) = g (res ⟨e, he⟩) := (LinearMap.congr_fun hg ⟨e, he⟩).symm
    have h2 : res ⟨e, he⟩ = ∑ x : s, e x • (Pi.single x (1 : ℂ) : s → ℂ) := by
      ext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single y]
      · simp [res]
      · intro z _ hzy; simp [Ne.symm hzy]
      · intro hy; exact absurd (Finset.mem_univ y) hy
    have h3 : e = ((g (res ⟨e, he⟩) : E) : X → ℂ) := congrArg Subtype.val h1
    conv_lhs => rw [h3, h2, map_sum]
    rw [Submodule.coe_sum, Finset.univ_eq_attach, ← Finset.sum_attach s (fun x => e x • b x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, Submodule.coe_smul]
    simp only [b, dif_pos x.2]

end EvalCoords

namespace PeriodicFlow

scoped instance instFactTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {X : Type*}

structure IsPeriodicFlow (act : ℝ → X → X) : Prop where
  act_act : ∀ (s t : ℝ) (x : X), act s (act t x) = act (t + s) x
  act_add_two_pi : ∀ (t : ℝ) (x : X), act (t + 2 * π) x = act t x
  act_zero : ∀ x : X, act 0 x = x

private def _root_.PeriodicFlow.ker (n : ℤ) (θ : ℝ) : ℂ := exp (-((n : ℂ) * θ * I))

p2m_export "PeriodicFlow" "ker"
theorem continuous_ker (n : ℤ) : Continuous (ker n) := by
  unfold ker; fun_prop

theorem ker_add_two_pi (n : ℤ) (θ : ℝ) : ker n (θ + 2 * π) = ker n θ := by
  unfold ker
  have : -((n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) = -((n : ℂ) * θ * I) + (-n : ℤ) * (2 * π * I) := by
    push_cast; ring
  rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

def P (act : ℝ → X → X) (n : ℤ) (f : X → ℂ) : X → ℂ :=
  fun x => (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..2 * π, ker n θ * f (act θ x)

variable {act : ℝ → X → X}

theorem periodic_integrand (hact : IsPeriodicFlow act) (n : ℤ) (f : X → ℂ) (x : X) :
    Function.Periodic (fun θ => ker n θ * f (act θ x)) (2 * π) := fun θ => by
  simp only [ker_add_two_pi, hact.act_add_two_pi]

theorem P_eq_integral (hact : IsPeriodicFlow act) (n : ℤ) (f : X → ℂ) (x : X) (a : ℝ) :
    P act n f x = (1 / (2 * π) : ℂ) * ∫ θ in a..a + 2 * π, ker n θ * f (act θ x) := by
  unfold P
  rw [(periodic_integrand hact n f x).intervalIntegral_add_eq a 0, zero_add]

theorem P_act (hact : IsPeriodicFlow act) (n : ℤ) (f : X → ℂ) (θ₀ : ℝ) (x : X) :
    P act n f (act θ₀ x) = exp ((n : ℂ) * θ₀ * I) * P act n f x := by
  rw [P_eq_integral hact n f x θ₀]
  unfold P
  simp_rw [hact.act_act]
  have h : ∀ θ : ℝ, ker n θ * f (act (θ₀ + θ) x) =
      (fun u => exp ((n : ℂ) * θ₀ * I) * (ker n u * f (act u x))) (θ + θ₀) := by
    intro θ
    simp only [ker]
    rw [add_comm θ₀ θ, ← mul_assoc, ← exp_add]
    congr 2
    push_cast; ring
  simp_rw [h]
  rw [intervalIntegral.integral_comp_add_right (fun u => exp ((n : ℂ) * θ₀ * I) * (ker n u * f (act u x))) θ₀,
    zero_add, add_comm (2 * π) θ₀, intervalIntegral.integral_const_mul]
  ring

def ContinuousOrbits (act : ℝ → X → X) (f : X → ℂ) : Prop := ∀ x : X, Continuous fun θ : ℝ => f (act θ x)

theorem intervalIntegrable_integrand {f : X → ℂ} (hf : ContinuousOrbits act f) (n : ℤ) (x : X) (a b : ℝ) :
    IntervalIntegrable (fun θ => ker n θ * f (act θ x)) volume a b :=
  ((continuous_ker n).mul (hf x)).intervalIntegrable a b

theorem continuousOrbits_P (hact : IsPeriodicFlow act) (n : ℤ) (f : X → ℂ) :
    ContinuousOrbits act (P act n f) := fun x => by
  simp_rw [P_act hact]
  fun_prop

theorem ContinuousOrbits.add {f g : X → ℂ} (hf : ContinuousOrbits act f) (hg : ContinuousOrbits act g) :
    ContinuousOrbits act (f + g) := fun x => (hf x).add (hg x)

theorem ContinuousOrbits.smul {f : X → ℂ} (c : ℂ) (hf : ContinuousOrbits act f) :
    ContinuousOrbits act (c • f) := fun x => (hf x).const_smul c

theorem ContinuousOrbits.zero : ContinuousOrbits act (0 : X → ℂ) := fun _ => continuous_const

theorem ContinuousOrbits.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i ∈ s, ContinuousOrbits act (f i)) :
    ContinuousOrbits act (∑ i ∈ s, f i) := fun x => by
  simp only [Finset.sum_apply]
  exact continuous_finsetSum s fun i hi => hf i hi x

theorem P_add {f g : X → ℂ} (hf : ContinuousOrbits act f) (hg : ContinuousOrbits act g) (n : ℤ) :
    P act n (f + g) = P act n f + P act n g := by
  funext x
  simp only [P, Pi.add_apply, mul_add]
  rw [intervalIntegral.integral_add (intervalIntegrable_integrand hf n x _ _)
    (intervalIntegrable_integrand hg n x _ _), mul_add]

theorem P_smul (c : ℂ) (f : X → ℂ) (n : ℤ) : P act n (c • f) = c • P act n f := by
  funext x
  simp only [P, Pi.smul_apply, smul_eq_mul]
  have : (fun θ => ker n θ * (c * f (act θ x))) = fun θ => c * (ker n θ * f (act θ x)) := by
    funext θ; ring
  rw [this, intervalIntegral.integral_const_mul]
  ring

theorem P_zero (n : ℤ) : P act n (0 : X → ℂ) = 0 := by
  funext x; simp [P]

theorem P_sum {ι : Type*} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i ∈ s, ContinuousOrbits act (f i)) (n : ℤ) :
    P act n (∑ i ∈ s, f i) = ∑ i ∈ s, P act n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      P_add (hf a (Finset.mem_insert_self a s))
        (ContinuousOrbits.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem P_P (hact : IsPeriodicFlow act) (m n : ℤ) (f : X → ℂ) :
    P act m (P act n f) = if n = m then P act n f else 0 := by
  funext x
  have LHS : P act m (P act n f) x =
      P act n f x * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..2 * π, exp (((n : ℂ) - m) * I * θ)) := by
    show (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..2 * π, ker m θ * P act n f (act θ x) = _
    simp_rw [P_act hact n f]
    have : (fun θ : ℝ => ker m θ * (exp ((n : ℂ) * θ * I) * P act n f x)) =
        fun θ : ℝ => P act n f x * exp (((n : ℂ) - m) * I * θ) := by
      funext θ
      simp only [ker]
      rw [← mul_assoc, ← exp_add, mul_comm _ (P act n f x)]
      congr 2; ring
    rw [this, intervalIntegral.integral_const_mul]
    ring
  rw [LHS]
  split_ifs with hnm
  · subst hnm
    simp only [sub_self, zero_mul, exp_zero]
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
  · have hc : ((n : ℂ) - m) * I ≠ 0 := by
      apply mul_ne_zero _ I_ne_zero
      rw [sub_ne_zero]
      exact_mod_cast hnm
    rw [integral_exp_mul_complex hc]
    have h1 : exp (((n : ℂ) - m) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      have : ((n : ℂ) - m) * I * ((2 * π : ℝ) : ℂ) = ((n - m : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
      rw [this, exp_int_mul_two_pi_mul_I]
    rw [h1]
    simp

theorem P_mem (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] {f : X → ℂ} (hf : ContinuousOrbits act f)
    (hE : ∀ θ : ℝ, (fun x => f (act θ x)) ∈ E) (n : ℤ) : P act n f ∈ E := by
  classical
  obtain ⟨s, b, hb, hcoord⟩ := EvalCoords.exists_eval_coords E
  have hpt : ∀ (θ : ℝ) (x : X), f (act θ x) = ∑ y ∈ s, f (act θ y) * b y x := by
    intro θ x
    have := congrFun (hcoord _ (hE θ)) x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have hP : P act n f = ∑ y ∈ s, P act n f y • b y := by
    funext x
    simp only [P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [hpt _ x, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : (fun θ => ker n θ * (f (act θ y) * b y x)) = fun θ => (ker n θ * f (act θ y)) * b y x := by
        funext θ; ring
      rw [this, intervalIntegral.integral_mul_const]
      ring
    · intro y _
      have : (fun θ => ker n θ * (f (act θ y) * b y x)) = fun θ => (ker n θ * f (act θ y)) * b y x := by
        funext θ; ring
      rw [this]
      exact (intervalIntegrable_integrand hf n y _ _).mul_const _
  rw [hP]
  exact E.sum_mem fun y _ => E.smul_mem _ (hb y)

theorem finite_setOf_P_ne_zero (hact : IsPeriodicFlow act) (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E]
    {f : X → ℂ} (hf : ContinuousOrbits act f) (hE : ∀ θ : ℝ, (fun x => f (act θ x)) ∈ E) :
    {n : ℤ | P act n f ≠ 0}.Finite := by
  classical
  set N := {n : ℤ | P act n f ≠ 0} with hN

  let v : N → E := fun n => ⟨P act n f, P_mem E hf hE n⟩
  have hli : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp E.subtype
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have hsum' : ∑ j ∈ s, c j • P act (j : ℤ) f = 0 := by
      simpa [v, Function.comp] using hsum
    have := congrArg (P act (i : ℤ)) hsum'
    rw [P_sum s (fun j _ => (continuousOrbits_P hact _ f).smul (c j)), P_zero] at this
    simp_rw [P_smul, P_P hact] at this
    rw [Finset.sum_eq_single i] at this
    · simp only [if_true] at this
      rcases smul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h i.2
    · intro j _ hji
      have : (j : ℤ) ≠ i := fun h => hji (Subtype.ext h)
      simp [this]
    · intro hi'; exact absurd hi hi'
  have : Finite N := hli.finite_of_isNoetherian
  exact Set.toFinite N

def orbitLift (hact : IsPeriodicFlow act) (f : X → ℂ) (x : X) : AddCircle (2 * π) → ℂ :=
  Function.Periodic.lift (f := fun θ : ℝ => f (act θ x)) (c := 2 * π) (fun θ => by
    simp only [hact.act_add_two_pi])

theorem orbitLift_coe (hact : IsPeriodicFlow act) (f : X → ℂ) (x : X) (θ : ℝ) :
    orbitLift hact f x (θ : AddCircle (2 * π)) = f (act θ x) :=
  Function.Periodic.lift_coe _ θ

theorem continuous_orbitLift (hact : IsPeriodicFlow act) {f : X → ℂ} (hf : ContinuousOrbits act f) (x : X) :
    Continuous (orbitLift hact f x) :=
  continuous_coinduced_dom.mpr ((hf x).congr fun θ => (orbitLift_coe hact f x θ).symm)

theorem fourier_coe_two_pi (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * π)) = exp ((n : ℂ) * θ * I) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp

theorem fourierCoeff_orbitLift (hact : IsPeriodicFlow act) (f : X → ℂ) (x : X) (n : ℤ) :
    fourierCoeff (orbitLift hact f x) n = P act n f x := by
  rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
  unfold P
  have : (fun θ : ℝ => fourier (-n) (θ : AddCircle (2 * π)) • orbitLift hact f x (θ : AddCircle (2 * π))) =
      fun θ : ℝ => ker n θ * f (act θ x) := by
    funext θ
    rw [orbitLift_coe, fourier_coe_two_pi, smul_eq_mul]
    simp only [ker, Int.cast_neg, neg_mul]
  rw [this, Complex.real_smul]
  push_cast
  ring

theorem eq_sum_P (hact : IsPeriodicFlow act) {f : X → ℂ} (hf : ContinuousOrbits act f)
    (N : Finset ℤ) (hN : ∀ n, P act n f ≠ 0 → n ∈ N) : f = ∑ n ∈ N, P act n f := by
  classical
  funext x

  let g : C(AddCircle (2 * π), ℂ) := ⟨orbitLift hact f x, continuous_orbitLift hact hf x⟩
  let h : C(AddCircle (2 * π), ℂ) := g + ∑ n ∈ N, (-P act n f x) • fourier n
  have hg_int : Integrable g (haarAddCircle (T := 2 * π)) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint : ∀ n ∈ N, Integrable ((-P act n f x) • (fourier n : AddCircle (2 * π) → ℂ)) (haarAddCircle (T := 2 * π)) :=
    fun n _ => ((fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).smul _
  have hcoe : (h : AddCircle (2 * π) → ℂ) =
      (g : AddCircle (2 * π) → ℂ) + ∑ n ∈ N, (-P act n f x) • (fourier n : AddCircle (2 * π) → ℂ) := by
    simp only [h, ContinuousMap.coe_add, ContinuousMap.coe_sum, ContinuousMap.coe_smul]
  have hF : fourierCoeff (h : AddCircle (2 * π) → ℂ) =
      fourierCoeff (g : AddCircle (2 * π) → ℂ) + ∑ n ∈ N, (-P act n f x) • (Pi.single n (1 : ℂ) : ℤ → ℂ) := by
    rw [hcoe, fourierCoeff.add hg_int (integrable_finsetSum' N hint), fourierCoeff.sum N _ hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← fourierCoeff_fourier (T := 2 * π) n]
    funext m
    exact fourierCoeff.const_smul _ _ m
  have hcoeff : ∀ m : ℤ, fourierCoeff (h : AddCircle (2 * π) → ℂ) m = 0 := by
    intro m
    rw [hF, Pi.add_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq N m]
    change fourierCoeff (orbitLift hact f x) m + (if m ∈ N then -P act m f x else 0) = 0
    rw [fourierCoeff_orbitLift hact f x m]
    split_ifs with hm
    · ring
    · have : P act m f = 0 := by
        by_contra hne; exact hm (hN m hne)
      rw [this]; simp

  have hLp : ContinuousMap.toLp (E := ℂ) 2 (haarAddCircle (T := 2 * π)) ℂ h = 0 := by
    have hrepr : fourierBasis.repr (ContinuousMap.toLp (E := ℂ) 2 (haarAddCircle (T := 2 * π)) ℂ h) = 0 := by
      apply lp.ext
      funext i
      rw [fourierBasis_repr, fourierCoeff_toLp, hcoeff]
      rfl
    exact (LinearIsometryEquiv.map_eq_zero_iff _).mp hrepr
  have hzero : h = 0 := ContinuousMap.toLp_injective (haarAddCircle (T := 2 * π)) (by rw [hLp, map_zero])

  have h0 := congrArg (fun u : C(AddCircle (2 * π), ℂ) => u 0) hzero
  simp only [h, g, ContinuousMap.add_apply, ContinuousMap.zero_apply, ContinuousMap.coe_sum,
    ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, fourier_eval_zero, smul_eq_mul, mul_one,
    ContinuousMap.coe_mk] at h0
  rw [← QuotientAddGroup.mk_zero, orbitLift_coe, hact.act_zero, Finset.sum_neg_distrib, add_neg_eq_zero] at h0
  rw [h0, Finset.sum_apply]

theorem P_comp (n : ℤ) (f : X → ℂ) (σ : X → X) (c : ℂ) (hσ : ∀ θ x, act θ (σ x) = σ (act θ x))
    (hf : ∀ x, f (σ x) = c * f x) : ∀ x, P act n f (σ x) = c * P act n f x := by
  intro x
  simp only [P, hσ, hf]
  have : (fun θ => ker n θ * (c * f (act θ x))) = fun θ => c * (ker n θ * f (act θ x)) := by funext θ; ring
  rw [this, intervalIntegral.integral_const_mul]
  ring

end PeriodicFlow
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow"

noncomputable section
open scoped Classical
open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain

namespace TSRot

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

@[scoped simp] theorem rotMat_apply_00 (θ : ℝ) : rotMat θ 0 0 = Real.cos θ := rfl
@[scoped simp] theorem rotMat_apply_01 (θ : ℝ) : rotMat θ 0 1 = Real.sin θ := rfl
@[scoped simp] theorem rotMat_apply_10 (θ : ℝ) : rotMat θ 1 0 = -Real.sin θ := rfl
@[scoped simp] theorem rotMat_apply_11 (θ : ℝ) : rotMat θ 1 1 = Real.cos θ := rfl

theorem det_rotMat (θ : ℝ) : (rotMat θ).det = 1 := by
  rw [Matrix.det_fin_two, rotMat_apply_00, rotMat_apply_01, rotMat_apply_10, rotMat_apply_11]
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem continuous_rotMat_apply (i j : Fin 2) : Continuous fun θ : ℝ => rotMat θ i j := by
  fin_cases i <;> fin_cases j
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin
  · simp
    exact Real.continuous_sin.neg
  · simpa using Real.continuous_cos

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat θ) (by rw [det_rotMat]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat θ, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    rw [rotGL_coe, rotMat_apply_00, rotMat_apply_01, rotMat_apply_10, rotMat_apply_11,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

def rotSO (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem rotSO_coe_apply (θ : ℝ) (i j : Fin 2) :
    (((rotSO θ : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      rotMat θ i j := rfl

theorem rotSO_add (a b : ℝ) : rotSO (a + b) = rotSO a * rotSO b := by
  apply Subtype.ext
  apply Units.ext
  change rotMat (a + b) = rotMat a * rotMat b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rotSO_zero : rotSO 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rotMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rotSO_two_pi : rotSO (2 * Real.pi) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rotMat (2 * Real.pi) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem archWeightOneℝ_rotSO (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := rfl

theorem archWeightOneℝ_rotSO_eq_exp (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [archWeightOneℝ_rotSO, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]

theorem rotSO_surjective : Function.Surjective rotSO := by
  intro k
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by
      rw [hz, Complex.normSq_mk]
      nlinarith [hab]
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact this
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h2, h3]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨Complex.arg z, ?_⟩
  have hc : Real.cos (Complex.arg z) = a := by rw [Complex.cos_arg hz0, hnorm, div_one]
  have hs : Real.sin (Complex.arg z) = b := by rw [Complex.sin_arg, hnorm, div_one]
  apply Subtype.ext
  apply Units.ext
  change rotMat (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.eta_fin_two ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), ← ha, ← hb, h10, h11,
    rotMat, hc, hs]

section Adelic

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

omit [NumberField F] in
theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

variable {F}

omit [NumberField F] in
theorem rotAt_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = (ringEquivRealOfIsReal hw).symm (rotMat θ i j) :=
  rfl

omit [NumberField F] in

theorem rowIsometrySubgroup₀Map_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotAt F hw he θ) = rotSO θ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat θ i j)) = rotMat θ i j
  exact RingEquiv.apply_symm_apply _ _

omit [NumberField F] in
theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a b : ℝ) :
    rotAt F hw he (a + b) = rotAt F hw he a * rotAt F hw he b := by
  rw [rotAt, rotSO_add, map_mul]
  rfl

omit [NumberField F] in
theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : rotAt F hw he 0 = 1 := by
  rw [rotAt, rotSO_zero, map_one]

def adelicRot {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w
    ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)

theorem adelicRot_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a b : ℝ) :
    adelicRot hw he (a + b) = adelicRot hw he a * adelicRot hw he b := by
  rw [adelicRot, rotAt_add, Subgroup.coe_mul, map_mul]
  rfl

theorem adelicRot_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : adelicRot hw he 0 = 1 := by
  rw [adelicRot, rotAt_zero, OneMemClass.coe_one, map_one]

theorem adelicRot_neg {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a : ℝ) :
    adelicRot hw he (-a) = (adelicRot hw he a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← adelicRot_add, neg_add_cancel, adelicRot_zero]

theorem adelicRot_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    ((adelicRot hw he θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem continuous_adelicRot {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) :
    Continuous fun θ : ℝ => adelicRot hw he θ := by
  have hval : Continuous fun θ : ℝ =>
      ((adelicRot hw he θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [adelicRot_coe_apply]
    refine Continuous.prodMk ?_ continuous_const
    apply continuous_pi
    intro v
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self, rotAt_coe_apply]
      exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (continuous_rotMat_apply i j)
    · simp only [Function.update_of_ne hv]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun θ : ℝ => (((adelicRot hw he θ)⁻¹ : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
      fun θ : ℝ => ((adelicRot hw he (-θ) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext θ
    rw [adelicRot_neg]
  rw [this]
  exact hval.comp continuous_neg

end Adelic
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow"

section More

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem rotAt_surjective {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) :
    Function.Surjective (rotAt F hw he) := by
  intro k
  obtain ⟨θ, hθ⟩ := rotSO_surjective
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k)
  refine ⟨θ, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j : 1
  change (ringEquivRealOfIsReal hw).symm (rotMat θ i j) = _
  have hij : rotMat θ i j =
      (ringEquivRealOfIsReal hw) ((((k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j) := by
    rw [← rotSO_coe_apply θ i j, hθ]
    rfl
  rw [hij, RingEquiv.symm_apply_apply]

theorem adelicRot_two_pi {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : adelicRot hw he (2 * Real.pi) = 1 := by
  rw [adelicRot, rotAt, rotSO_two_pi, map_one, OneMemClass.coe_one, map_one]

theorem adelicRot_add_two_pi {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    adelicRot hw he (θ + 2 * Real.pi) = adelicRot hw he θ := by
  rw [adelicRot_add, adelicRot_two_pi, mul_one]

omit [NumberField F] in

theorem archWeightCharAt_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (n : ℤ) (θ : ℝ) :
    ((archWeightCharAt hw n (rotAt F hw he θ) : ℂˣ) : ℂ) = Complex.exp ((n : ℂ) * θ * Complex.I) := by
  rw [archWeightCharAt, archWeightOneAt, MonoidHom.comp_apply, MonoidHom.comp_apply,
    rowIsometrySubgroup₀Map_rotAt, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val,
    archWeightOneℝ_rotSO_eq_exp, ← Complex.exp_int_mul]
  congr 1
  ring

theorem mul_adelicArchGLInclAt_comm_of_glArch_eq_one (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    {u : AdelicGL2 (𝓞 F) F} (hu : AdelicLevel.glArch (𝓞 F) F u = 1) :
    u * adelicArchGLInclAt F w k = adelicArchGLInclAt F w k * u := by
  have hfin : AdelicLevel.glFin (𝓞 F) F (adelicArchGLInclAt F w k) = 1 := by
    rw [adelicArchGLInclAt]
    exact glFin_adelicArchGLIncl F _
  have h₁ : AdelicLevel.glArch (𝓞 F) F (u * adelicArchGLInclAt F w k) =
      AdelicLevel.glArch (𝓞 F) F (adelicArchGLInclAt F w k * u) := by
    rw [map_mul, map_mul, hu, one_mul, mul_one]
  have h₂ : AdelicLevel.glFin (𝓞 F) F (u * adelicArchGLInclAt F w k) =
      AdelicLevel.glFin (𝓞 F) F (adelicArchGLInclAt F w k * u) := by
    rw [map_mul, map_mul, hfin, one_mul, mul_one]
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem mul_adelicRot_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ)
    {u : AdelicGL2 (𝓞 F) F} (hu : AdelicLevel.glArch (𝓞 F) F u = 1) :
    u * adelicRot hw he θ = adelicRot hw he θ * u :=
  mul_adelicArchGLInclAt_comm_of_glArch_eq_one w _ hu

theorem adelicRot_comm_adelicArchGLInclAt {w v : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (hvw : v ≠ w) (θ : ℝ)
    (k : GL (Fin 2) v.Completion) :
    adelicArchGLInclAt F v k * adelicRot hw he θ = adelicRot hw he θ * adelicArchGLInclAt F v k :=
  (commute_adelicArchGLInclAt_of_ne F hvw k _).eq

end More
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow"

end TSRot
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.TSRot"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.TSRot"

noncomputable section

namespace TSMain

open scoped Classical
open NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain PeriodicFlow TSRot

variable (K : Type) [Field K] [NumberField K]

theorem continuous_of_mem_cuspKFiniteSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspKFiniteSubmodule K pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ h
  · rintro φ ⟨_, hc, _⟩; exact hc
  · exact continuous_const
  · intro _ _ _ _ hu hv; exact hu.add hv
  · intro c _ _ hu; exact hu.const_smul c

theorem exists_finiteDimensional_of_mem_archCutSubmodule (tys : ArchTypeFamily K) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ archCutSubmodule K tys) (w : InfinitePlace K) :
    ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := by
  have hw := (mem_archCutSubmodule_iff K tys φ).mp hφ w
  refine Submodule.iSup_induction _
    (motive := fun φ => ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) hw ?_ ?_ ?_
  · intro i φ hφi
    refine Submodule.span_induction (p := fun φ _ => ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) ?_ ?_ ?_ ?_ hφi
    · rintro _ ⟨T, hT, v, rfl⟩
      refine ⟨LinearMap.range T, inferInstance, fun k => ?_⟩
      have : rightTranslate K (rowIsometryInclAt₀ K w k) (T v) = T ((tys.rep w i).ρ k v) := by
        funext x; exact (hT k v x).symm
      rw [this]; exact LinearMap.mem_range_self T _
    · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
    · rintro φ ψ - - ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
      haveI := hW₁; haveI := hW₂
      exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
        rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩
    · rintro c φ - ⟨W, hW, h⟩
      exact ⟨W, hW, fun k => by rw [rightTranslate_smul]; exact W.smul_mem c (h k)⟩
  · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
  · rintro φ ψ ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
    haveI := hW₁; haveI := hW₂
    exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
      rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩

variable {K}

def rotFlow {w : InfinitePlace K} (hw : w.IsReal) : ℝ → AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K :=
  fun θ x => x * adelicRot hw (norm_symm_ringEquivRealOfIsReal K hw) θ

theorem isPeriodicFlow_rotFlow {w : InfinitePlace K} (hw : w.IsReal) : IsPeriodicFlow (rotFlow hw) where
  act_act s t x := by
    simp only [rotFlow, mul_assoc, ← adelicRot_add]
  act_add_two_pi t x := by
    simp only [rotFlow, adelicRot_add_two_pi]
  act_zero x := by
    simp only [rotFlow, adelicRot_zero, mul_one]

theorem split_at (C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hC_cont : ∀ φ ∈ C, Continuous φ)
    {w : InfinitePlace K} (hw : w.IsReal)
    (hC_stab : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C)
    (hC_fd : ∀ φ ∈ C, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : φ ∈ C) :
    ∃ (N : Finset ℤ) (ψ : ℤ → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ n, ψ n ∈ C) ∧
      (∀ n, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ψ n)) ∧
      φ = ∑ n ∈ N, ψ n ∧
      ∀ (v : InfinitePlace K) (χ : rowIsometrySubgroup₀ v.Completion →* ℂˣ), v ≠ w →
        HasArchCharacterAt₀ K v χ φ → ∀ n, HasArchCharacterAt₀ K v χ (ψ n) := by
  set he := norm_symm_ringEquivRealOfIsReal K hw
  have hact := isPeriodicFlow_rotFlow hw
  have hcont : ContinuousOrbits (rotFlow hw) φ := fun x =>
    (hC_cont φ hφ).comp (continuous_const.mul (continuous_adelicRot hw he))

  obtain ⟨W, hWfd, hW⟩ := hC_fd φ hφ
  haveI := hWfd
  let E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := W ⊓ C
  haveI : FiniteDimensional ℂ E := inferInstance
  have hE : ∀ θ : ℝ, (fun x => φ (rotFlow hw θ x)) ∈ E := fun θ =>
    ⟨hW (rotAt K hw he θ), hC_stab (rotAt K hw he θ) φ hφ⟩
  refine ⟨(finite_setOf_P_ne_zero hact E hcont hE).toFinset, fun n => P (rotFlow hw) n φ,
    fun n => (P_mem E hcont hE n).2, fun n => ?_, ?_, ?_⟩
  ·
    intro k g
    obtain ⟨θ, rfl⟩ := rotAt_surjective hw he k
    rw [archWeightCharAt_rotAt hw he n θ]
    exact P_act hact n φ θ g
  · exact eq_sum_P hact hcont _ fun n hn => (Set.Finite.mem_toFinset _).mpr hn
  · intro v χ hvw hχ n k g
    refine P_comp n φ (fun x => x * adelicArchGLInclAt K v (k : GL (Fin 2) v.Completion)) _ ?_ ?_ g
    · intro θ x
      simp only [rotFlow, mul_assoc, adelicRot_comm_adelicArchGLInclAt hw he hvw]
    · intro x; exact hχ k x

theorem split_finset (C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hC_cont : ∀ φ ∈ C, Continuous φ)
    (hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C)
    (hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W)
    (S : Finset (InfinitePlace K)) :
    ∀ φ ∈ C, ∃ (ι : Type) (_ : Fintype ι) (ys : ι → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ j, ys j ∈ C) ∧
      (∀ j, ∀ w ∈ S, ∀ hw : w.IsReal, ∃ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ys j)) ∧
      φ = ∑ j, ys j := by
  induction S using Finset.induction_on with
  | empty =>
    intro φ hφ
    exact ⟨Unit, inferInstance, fun _ => φ, fun _ => hφ, fun _ w hw => absurd hw (Finset.notMem_empty w),
      by simp⟩
  | insert w S hwS ih =>
    intro φ hφ
    obtain ⟨ι, _, ys, hysC, hysW, hsum⟩ := ih φ hφ
    by_cases hw : w.IsReal
    ·
      choose N ψ hψC hψw hψsum hψold using fun j =>
        split_at C hC_cont hw (hC_stab w) (fun φ hφ => hC_fd φ hφ w) (ys j) (hysC j)
      refine ⟨(Σ j : ι, (N j : Set ℤ)), inferInstance, fun p => ψ p.1 p.2, fun p => hψC p.1 p.2, ?_, ?_⟩
      · rintro ⟨j, n, hn⟩ v hv hv'
        rcases Finset.mem_insert.mp hv with rfl | hvS
        · exact ⟨n, hψw j n⟩
        · have hvw : v ≠ w := fun h => hwS (h ▸ hvS)
          obtain ⟨m, hm⟩ := hysW j v hvS hv'
          exact ⟨m, hψold j v _ hvw hm n⟩
      · rw [hsum, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hψsum j]
        exact (Finset.sum_coe_sort (N j) (ψ j)).symm
    · refine ⟨ι, inferInstance, ys, hysC, ?_, hsum⟩
      intro j v hv hv'
      rcases Finset.mem_insert.mp hv with rfl | hvS
      · exact absurd hv' hw
      · exact hysW j v hvS hv'

end TSMain
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.TSRot"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.PeriodicFlow P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.TSRot"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

set_option linter.unusedVariables false in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)),
      (∀ j, ys j ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
      (∀ j, ∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ys j)) ∧
      y = ∑ j, ys j := by
  set pins := productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K) with hpins
  set C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := V ⊓ levelInvariantSubmodule K pins N ⊓ archCutSubmodule K tys
    with hC

  have hC_cont : ∀ φ ∈ C, Continuous φ := fun φ hφ =>
    TSMain.continuous_of_mem_cuspKFiniteSubmodule K (hV.1.le hφ.1.1)
  have hU : ∀ u' ∈ pins.U N, AdelicLevel.glArch (𝓞 K) K u' = 1 := fun u' hu' => hu'.2
  have hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C := by
    intro w k φ hφ
    refine ⟨⟨hV.1.rightTranslate_arch_mem w k φ hφ.1.1, ?_⟩,
      rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule K tys hφ.2 w k⟩
    intro g u' hu'
    show φ (g * u' * rowIsometryInclAt₀ K w k) = φ (g * rowIsometryInclAt₀ K w k)
    rw [rowIsometryInclAt₀_apply, mul_assoc, TSRot.mul_adelicArchGLInclAt_comm_of_glArch_eq_one w _ (hU u' hu'),
      ← mul_assoc]
    exact hφ.1.2 _ u' hu'
  have hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := fun φ hφ w =>
    TSMain.exists_finiteDimensional_of_mem_archCutSubmodule K tys hφ.2 w
  obtain ⟨ι, _, ys, hysC, hysW, hsum⟩ :=
    TSMain.split_finset C hC_cont hC_stab hC_fd Finset.univ y hy
  refine ⟨Fintype.card ι, fun j => ys ((Fintype.equivFin ι).symm j), fun j => hysC _,
    fun j w hw => hysW _ w (Finset.mem_univ w) hw, ?_⟩
  rw [hsum]
  exact ((Fintype.equivFin ι).symm.sum_comp ys).symm

end S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent (solution)
