-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part05
-- name    : OAI_AlternatingFlow_Part05
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:34:25.056906+00:00
-- url     : https://prove2.me/theorems/70062d38-a45d-41d8-81ed-7bc20035458c
-- title:
--   Alternating-flow construction, part 5 of 11 (port of OpenAI's formalization): effective arithmetic, quantitative bounds and names
-- statement:
--   Part 5 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains effective arithmetic, quantitative bounds and names.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `Effective`, `Quantitative`, `EffectiveProfiles`, `Arithmetic`, `Names`, `ExpNames`, `ProfileNames`, `DecoderBounds`, `DecoderNames`, `RecursiveBounds` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Effective.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Quantitative.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/EffectiveProfiles.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Arithmetic.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Names.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/ExpNames.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/ProfileNames.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/DecoderBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/DecoderNames.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/RecursiveBounds.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 5 of 11: effective arithmetic, quantitative bounds and names.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: Effective.lean, Quantitative.lean, EffectiveProfiles.lean, Arithmetic.lean, Names.lean, ExpNames.lean, ProfileNames.lean, DecoderBounds.lean, DecoderNames.lean, RecursiveBounds.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part04

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Effective.lean =====
namespace OAI

section EffectiveDevelopment

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory

namespace AlternatingNS
namespace Effective

lemma nat_pow : Primrec₂ (fun b n : ℕ => b ^ n) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

lemma capacity : Primrec₂ Scales.K :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2)

lemma exponent : Primrec₂ Scales.s :=
  Primrec.nat_mul.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
    (nat_pow.comp (Primrec.const 2) (nat_pow.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 3)) (Primrec.const 2)))

lemma states : Primrec Machine.states :=
  Primrec.nat_add.comp Primrec.fst (Primrec.const 1)

lemma alphabet : Primrec Machine.alphabet :=
  Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)

lemma initialState : Primrec Machine.initialState :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma haltingStates : Primrec Machine.haltingStates :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

lemma table : Primrec Machine.table :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

lemma base : Primrec Machine.base :=
  Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.const 1)
      (Primrec.nat_max.comp (Primrec.nat_add.comp states (Primrec.const 1)) alphabet))

lemma instruction : Primrec (fun z : Machine × ℕ × ℕ => z.1.instruction z.2.1 z.2.2) := by
  have h := Primrec.list_getElem?.comp (table.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (alphabet.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.option_getD.comp h (Primrec.const none)).of_eq (by
    intro z; dsimp only [Machine.instruction];
    cases (z.1.table[z.2.1 * z.1.alphabet + z.2.2]?) <;> rfl)

lemma member {α : Type*} [Primcodable α] : PrimrecRel (fun l : List α => fun a => a ∈ l) :=
  (Primrec.eq.exists_mem_list).of_eq (by simp)

lemma command : Primrec (fun z : Machine × ℕ × ℕ => z.1.command z.2.1 z.2.2) := by
  apply Primrec.ite
  · exact (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (states.comp Primrec.fst)).or
      (member.comp (haltingStates.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  · exact (Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (1 : Fin 3)))
  · exact Primrec.option_getD.comp instruction ((states.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (1 : Fin 3))))

lemma program_of_computable {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Computable f) : ∃ c : Program, ∀ a, Returns c a (f a) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun a => ?_⟩
  simp [Returns, hc, Encodable.encodek]

lemma compiler_of_computable {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    (f : A → B → C) (hf : Computable₂ f) :
    ∃ compile : A → Program, Computable compile ∧
      ∀ a b, Returns (compile a) b (f a b) := by
  obtain ⟨c, hc⟩ := program_of_computable (fun z : A × B => f z.1 z.2) hf
  refine ⟨fun a => c.curry (Encodable.encode a),
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode).to_comp, ?_⟩
  intro a b
  simpa only [Returns, Nat.Partrec.Code.eval_curry, Encodable.encode_prod_val] using hc (a, b)

theorem command_program : ∃ compile : Machine → Program, Computable compile ∧
    ∀ M q a, Returns (compile M) (q, a) (M.command q a) := by
  obtain ⟨c, hC, h⟩ := compiler_of_computable
    (fun M : Machine => fun z : ℕ × ℕ => M.command z.1 z.2) command.to_comp
  exact ⟨c, hC, fun M q a => h M (q, a)⟩

end Effective
end AlternatingNS

end EffectiveDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Quantitative.lean =====
namespace OAI

section QuantitativeDevelopment

open scoped BigOperators ContDiff

namespace AlternatingNS
namespace Quantitative

noncomputable def rhoTerm (m : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ m * expNegInvGlue x

lemma rhoTerm_smooth (m : ℕ) : ContDiff ℝ ∞ (rhoTerm m) := by
  change ContDiff ℝ ∞ (fun x => x⁻¹ ^ m * expNegInvGlue x)
  simpa only [Polynomial.eval_X_pow] using
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X ^ m : Polynomial ℝ))

lemma rhoTerm_deriv (m : ℕ) :
    deriv (rhoTerm m) = fun x => rhoTerm (m + 2) x - m * rhoTerm (m + 1) x := by
  funext x
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.X ^ m : Polynomial ℝ) x).deriv
  simp only [Polynomial.eval_X_pow] at h
  change deriv (rhoTerm m) x = _ at h
  rw [h]
  simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X_pow, rhoTerm]
  cases m with
  | zero => norm_num
  | succ m => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]; ring

lemma exp_monomial_bound (y : ℝ) (hy : 0 ≤ y) (m : ℕ) :
    y ^ m * Real.exp (-y) ≤ m.factorial := by
  have h := Real.pow_div_factorial_le_exp y hy m
  have hp : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h' := (div_le_iff₀ hp).mp h
  calc
    _ ≤ (Real.exp y * m.factorial) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; simp

lemma rhoTerm_bound (m : ℕ) (x : ℝ) : |rhoTerm m x| ≤ m.factorial := by
  by_cases hx : x ≤ 0
  · simp [rhoTerm, expNegInvGlue.zero_of_nonpos hx]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [rhoTerm, expNegInvGlue, ite_eq_right hx,
      abs_of_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hx').le _) (Real.exp_pos _).le)]
    exact exp_monomial_bound x⁻¹ (inv_pos.mpr hx').le m

lemma rhoTerm_derivative_bound (r m : ℕ) (x : ℝ) :
    |iteratedDeriv r (rhoTerm m) x| ≤
      ((m + 2 * r).factorial : ℝ) * (m + 2 * r + 1 : ℕ) ^ r := by
  induction r generalizing m with
  | zero => simpa using rhoTerm_bound m x
  | succ r ih =>
    rw [iteratedDeriv_succ', rhoTerm_deriv]
    have hs (j : ℕ) : ContDiffAt ℝ (r : ℕ∞ω) (rhoTerm j) x :=
      ((rhoTerm_smooth j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    change |iteratedDeriv r (rhoTerm (m + 2) - fun x => (m : ℝ) * rhoTerm (m + 1) x) x| ≤ _
    rw [iteratedDeriv_sub (hs _) (contDiffAt_const.mul (hs _)), iteratedDeriv_const_mul _ (hs _)]
    have ht : m + 2 + 2 * r = m + 2 * (r + 1) := by omega
    have hf : ((m + 1 + 2 * r).factorial : ℝ) ≤ (m + 2 * (r + 1)).factorial := by
      exact_mod_cast Nat.factorial_le (by omega : m + 1 + 2 * r ≤ m + 2 * (r + 1))
    have hp : ((m + 1 + 2 * r + 1 : ℕ) : ℝ) ^ r ≤ (m + 2 * (r + 1) + 1 : ℕ) ^ r := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (by omega : m + 1 + 2 * r + 1 ≤ m + 2 * (r + 1) + 1)
    have hsmall := (ih (m + 1)).trans (mul_le_mul hf hp (by positivity) (by positivity))
    have hbig := ih (m + 2)
    rw [ht] at hbig
    calc
      _ ≤ |iteratedDeriv r (rhoTerm (m + 2)) x| + (m : ℝ) * |iteratedDeriv r (rhoTerm (m + 1)) x| := by
        simpa only [Real.norm_eq_abs, abs_mul, Nat.abs_cast] using
          norm_sub_le (iteratedDeriv r (rhoTerm (m + 2)) x) ((m : ℝ) * iteratedDeriv r (rhoTerm (m + 1)) x)
      _ ≤ ((m + 2 * (r + 1)).factorial : ℝ) * (m + 2 * (r + 1) + 1 : ℕ) ^ r +
          m * (((m + 2 * (r + 1)).factorial : ℝ) * (m + 2 * (r + 1) + 1 : ℕ) ^ r) :=
        add_le_add hbig (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _))
      _ ≤ _ := by
        rw [pow_succ]
        have hm : (m : ℝ) + 1 ≤ (m + 2 * (r + 1) + 1 : ℕ) := by
          push_cast; nlinarith
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m + 2 * (r + 1)).factorial by positivity)
          (show (0 : ℝ) ≤ (m + 2 * (r + 1) + 1 : ℕ) ^ r by positivity)]

lemma rho_derivative_bound (r : ℕ) (x : ℝ) :
    |iteratedDeriv r expNegInvGlue x| ≤ ((2 * r).factorial : ℝ) * (2 * r + 1 : ℕ) ^ r := by
  have he : rhoTerm 0 = expNegInvGlue := by funext x; simp [rhoTerm]
  simpa only [he, zero_add] using rhoTerm_derivative_bound r 0 x

def rhoBound (r : ℕ) : ℕ := (2 * r).factorial * (2 * r + 1) ^ r

lemma rho_jet_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r expNegInvGlue x‖ ≤ rhoBound r := by
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    rhoBound, Nat.cast_mul, Nat.cast_pow] using rho_derivative_bound r x

lemma transition_denom_lower (x : ℝ) :
    (1 / 9 : ℝ) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have he : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg]
    apply (le_inv_comm₀ (by norm_num) (Real.exp_pos _)).mpr
    have h : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
      simp
    rw [h]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hhalf : (1 / 9 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    norm_num [expNegInvGlue] at *
    exact he
  by_cases hx : (1 / 2 : ℝ) ≤ x
  · exact le_trans (hhalf.trans (expNegInvGlue.monotone hx))
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
  · exact le_trans (hhalf.trans (expNegInvGlue.monotone (by linarith : 1 / 2 ≤ 1 - x)))
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _))

lemma inverse_jet_bound (q r : ℕ) {x : ℝ} (hx : 0 < x) (hq : x⁻¹ ≤ q) :
    ‖iteratedFDeriv ℝ r (fun x : ℝ => x⁻¹) x‖ ≤ (r.factorial * q ^ (r + 1) : ℕ) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hexp : (-1 - (r : ℤ)) = -((r + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← inv_pow, norm_mul, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    Nat.abs_cast, Nat.cast_mul, Nat.cast_pow,
    abs_of_nonneg (pow_nonneg (inv_pos.mpr hx).le _)]
  gcongr

def reciprocalBound (q : ℕ) (B : ℕ → ℕ) (r : ℕ) : ℕ :=
  r.factorial * (r.factorial * q ^ (r + 1)) *
    (1 + ∑ i ∈ Finset.range (r + 1), B i) ^ r

lemma reciprocal_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (B : ℕ → ℕ)
    (hB : ∀ r x, ‖iteratedFDeriv ℝ r f x‖ ≤ B r)
    (q : ℕ) (hq : 1 ≤ q) (hpos : ∀ x, 0 < f x) (hrecip : ∀ x, (f x)⁻¹ ≤ q)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (fun x => (f x)⁻¹) x‖ ≤ reciprocalBound q B r := by
  classical
  let D : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), (B i : ℝ)
  let C : ℝ := r.factorial * (q : ℝ) ^ (r + 1)
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
  have hd (i : ℕ) (hi : i ≤ r) : (B i : ℝ) ≤ D := by
    have h := Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun i => (B i : ℝ)) (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega : i < r + 1))
    dsimp [D]; linarith
  have hu : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Set.Ioi 0) :=
    (contDiffOn_inv ℝ).mono (by intro y hy; simpa using ne_of_gt hy)
  have h := norm_iteratedFDeriv_comp_le' (g := fun y : ℝ => y⁻¹) (f := f)
    (t := Set.Ioi 0) (fun y hy => by rcases hy with ⟨z, rfl⟩; exact hpos z)
    hu hinv hf (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) x (C := C) (D := D) ?_ ?_
  · simpa only [reciprocalBound, C, D, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_sum, Function.comp_def] using h
  · intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (contDiffAt_inv ℝ (hpos x).ne') (hpos x)]
    apply (inverse_jet_bound q i (hpos x) (hrecip x)).trans
    dsimp [C]
    push_cast
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hi
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (by omega)
    · positivity
    · positivity
  · intro i hi hir
    exact (hB i x).trans ((hd i hir).trans (le_self_pow₀ hD (by omega)))

noncomputable def transitionDenom (x : ℝ) : ℝ := expNegInvGlue x + expNegInvGlue (1 - x)

lemma transitionDenom_smooth : ContDiff ℝ ∞ transitionDenom :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma transitionDenom_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r transitionDenom x‖ ≤ (2 * rhoBound r : ℕ) := by
  have hs : ContDiff ℝ ∞ (fun x => expNegInvGlue (1 - x)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  unfold transitionDenom
  rw [fun_iteratedFDeriv_add_apply (expNegInvGlue.contDiff (n := ⊤) |>.of_le
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) |>.contDiffAt)
      (hs.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  apply (norm_add_le _ _).trans
  have h₂ : ‖iteratedFDeriv ℝ r (fun x => expNegInvGlue (1 - x)) x‖ ≤ rhoBound r := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_const_sub]
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using rho_jet_bound r (1 - x)
  have h₁ := rho_jet_bound r x
  push_cast
  linarith

def transitionInvBound (r : ℕ) : ℕ := reciprocalBound 9 (fun i => 2 * rhoBound i) r

lemma transitionInv_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (fun x => (transitionDenom x)⁻¹) x‖ ≤ transitionInvBound r := by
  apply reciprocal_jet_bound transitionDenom transitionDenom_smooth
    (fun i => 2 * rhoBound i) transitionDenom_bound 9 (by norm_num)
    (fun x => Real.smoothTransition.pos_denom x) _ r x
  intro x
  exact (inv_le_comm₀ (Real.smoothTransition.pos_denom x) (by norm_num : (0 : ℝ) < 9)).mpr
    (by simpa only [one_div] using transition_denom_lower x)

def transitionBound (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), r.choose i * rhoBound i * transitionInvBound (r - i)

lemma transition_jet_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r Real.smoothTransition x‖ ≤ transitionBound r := by
  have he : Real.smoothTransition = fun x => expNegInvGlue x * (transitionDenom x)⁻¹ := by
    funext x; simp only [Real.smoothTransition, transitionDenom, div_eq_mul_inv]
  rw [he]
  apply (norm_iteratedFDeriv_mul_le (expNegInvGlue.contDiff (n := ⊤))
    (transitionDenom_smooth.inv (fun x => (Real.smoothTransition.pos_denom x).ne')) x
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
  simp only [transitionBound, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul _ (transitionInv_bound (r - i) x) (norm_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (rho_jet_bound i x) (Nat.cast_nonneg _)

end Quantitative
end AlternatingNS

end QuantitativeDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/EffectiveProfiles.lean =====
namespace OAI

section EffectiveProfilesDevelopment

open scoped BigOperators ContDiff

namespace AlternatingNS
namespace Effective

lemma factorial : Primrec Nat.factorial := by
  have hs : Primrec₂ (fun n a : ℕ => (n + 1) * a) :=
    Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  have h := Primrec.nat_rec₁ 1 hs
  refine h.of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, ih] using (Nat.factorial_succ n).symm

lemma sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Primrec₂ (fun a : A => fun z : ℕ × ℕ => z.2 + f a z.1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  have h := Primrec.nat_rec (Primrec.const (0 : ℕ) : Primrec (fun _ : A => (0 : ℕ))) hs
  refine h.of_eq ?_
  intro a n
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

lemma choose : Primrec₂ Nat.choose := by
  apply Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (Primrec.nat_div.comp (factorial.comp Primrec.fst)
      (Primrec.nat_mul.comp (factorial.comp Primrec.snd)
        (factorial.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd)))) (Primrec.const 0) |>.of_eq
  rintro ⟨n,k⟩
  dsimp only
  split_ifs with h
  · exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

lemma rhoBound : Primrec Quantitative.rhoBound := by
  exact Primrec.nat_mul.comp (factorial.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (nat_pow.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1)) Primrec.id)

lemma reciprocalBound {A : Type*} [Primcodable A] {q : A → ℕ} {B : A → ℕ → ℕ}
    (hq : Primrec q) (hB : Primrec₂ B) :
    Primrec₂ (fun a r => Quantitative.reciprocalBound (q a) (B a) r) := by
  let hr : Primrec (fun z : A × ℕ => z.2) := Primrec.snd
  let hfac := factorial.comp hr
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp hfac
      (Primrec.nat_mul.comp hfac (nat_pow.comp (hq.comp Primrec.fst) (Primrec.succ.comp hr))))
    (nat_pow.comp (Primrec.nat_add.comp (Primrec.const 1)
      ((sum_range hB).comp Primrec.fst (Primrec.succ.comp hr))) hr)

lemma transitionInvBound : Primrec Quantitative.transitionInvBound := by
  have hs : Primrec₂ (fun _ : ℕ => fun r : ℕ => 2 * Quantitative.rhoBound r) :=
    Primrec.nat_mul.comp (Primrec.const 2) (rhoBound.comp Primrec.snd)
  exact (reciprocalBound (Primrec.const 9 : Primrec (fun _ : ℕ => (9 : ℕ))) hs).comp
    Primrec.id Primrec.id

lemma transitionBound : Primrec Quantitative.transitionBound := by
  have hs : Primrec₂ (fun r i : ℕ => r.choose i * Quantitative.rhoBound i *
      Quantitative.transitionInvBound (r - i)) :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp choose (rhoBound.comp Primrec.snd))
      (transitionInvBound.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
  exact (sum_range hs).comp Primrec.id Primrec.succ

theorem profile_bound_programs :
    ∃ cρ cH : Program,
      (∀ r : ℕ, Returns cρ r (Quantitative.rhoBound r) ∧
        ∀ x : ℝ, ‖iteratedFDeriv ℝ r expNegInvGlue x‖ ≤ Quantitative.rhoBound r) ∧
      (∀ r : ℕ, Returns cH r (Quantitative.transitionBound r) ∧
        ∀ x : ℝ, ‖iteratedFDeriv ℝ r Real.smoothTransition x‖ ≤ Quantitative.transitionBound r) := by
  obtain ⟨cρ, hρ⟩ := program_of_computable Quantitative.rhoBound rhoBound.to_comp
  obtain ⟨cH, hH⟩ := program_of_computable Quantitative.transitionBound transitionBound.to_comp
  exact ⟨cρ, cH, fun r => ⟨hρ r, Quantitative.rho_jet_bound r⟩,
    fun r => ⟨hH r, Quantitative.transition_jet_bound r⟩⟩

end Effective
end AlternatingNS

end EffectiveProfilesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Arithmetic.lean =====
namespace OAI

section ArithmeticDevelopment

namespace AlternatingNS
namespace Arithmetic

lemma int_natCast : Primrec (fun n : ℕ => (n : ℤ)) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq (fun n => rfl)

lemma int_negSucc : Primrec Int.negSucc := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq (fun n => rfl)

lemma int_cases {A B : Type*} [Primcodable A] [Primcodable B]
    {f g : A → ℕ → B} (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec (fun z : A × ℤ => (Int.casesOn z.2 (f z.1) (g z.1) : B)) := by
  have hi : Primrec (fun z : A × ℤ => Encodable.encode z.2) := Primrec.encode.comp Primrec.snd
  refine (Primrec.cond (Primrec.nat_bodd.comp hi)
    (hg.comp Primrec.fst (Primrec.nat_div2.comp hi))
    (hf.comp Primrec.fst (Primrec.nat_div2.comp hi))).of_eq ?_
  rintro ⟨a,z⟩
  cases z with
  | ofNat n =>
    change (bif (Nat.bit false n).bodd then g a (Nat.bit false n).div2
      else f a (Nat.bit false n).div2) = f a n
    simp
  | negSucc n =>
    change (bif (Nat.bit true n).bodd then g a (Nat.bit true n).div2
      else f a (Nat.bit true n).div2) = g a n
    simp

lemma int_toNat : Primrec Int.toNat := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => n) (g := fun _ _ => (0 : ℕ))
    Primrec.snd (Primrec.const (0 : ℕ))
  exact (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq (fun z => by cases z <;> rfl)

lemma int_abs : Primrec Int.natAbs := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => n) (g := fun _ n => n + 1)
    Primrec.snd (Primrec.succ.comp Primrec.snd)
  exact (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq (fun z => by cases z <;> rfl)

lemma int_diff : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  refine (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (int_natCast.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (int_negSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)))).of_eq ?_
  rintro ⟨a,b⟩
  dsimp only
  split_ifs <;> omega

lemma int_neg : Primrec (fun z : ℤ => -z) := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => (0 : ℤ) - n)
    (g := fun _ n => (n + 1 : ℕ))
    (int_diff.comp (Primrec.const 0 : Primrec (fun _ : ℕ × ℕ => (0 : ℕ))) Primrec.snd)
    (int_natCast.comp (Primrec.succ.comp Primrec.snd))
  refine (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change (0 : ℤ) - n = -(n : ℤ); simp
  | negSucc n => change ((n + 1 : ℕ) : ℤ) = -Int.negSucc n; simp

lemma int_add : Primrec₂ (fun a b : ℤ => a + b) := by
  have h := int_diff.comp
    (Primrec.nat_add.comp (int_toNat.comp Primrec.fst) (int_toNat.comp Primrec.snd))
    (Primrec.nat_add.comp (int_toNat.comp (int_neg.comp Primrec.fst))
      (int_toNat.comp (int_neg.comp Primrec.snd)))
  exact h.of_eq (fun z => by push_cast; omega)

lemma int_sub : Primrec₂ (fun a b : ℤ => a - b) :=
  (int_add.comp Primrec.fst (int_neg.comp Primrec.snd)).of_eq (fun _ => (sub_eq_add_neg _ _).symm)

lemma int_mul : Primrec₂ (fun a b : ℤ => a * b) := by
  have hn : Primrec (fun z : ℤ × ℤ => (Int.natAbs z.1 * Int.natAbs z.2 : ℕ)) :=
    Primrec.nat_mul.comp (int_abs.comp Primrec.fst) (int_abs.comp Primrec.snd)
  have hh := Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst))
    (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
      (int_natCast.comp hn) (int_neg.comp (int_natCast.comp hn)))
    (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
      (int_neg.comp (int_natCast.comp hn)) (int_natCast.comp hn))
  refine hh.of_eq ?_
  rintro ⟨a,b⟩
  change (bif (Encodable.encode a).bodd then
    (bif (Encodable.encode b).bodd then ((a.natAbs * b.natAbs : ℕ) : ℤ) else
      -((a.natAbs * b.natAbs : ℕ) : ℤ)) else
    (bif (Encodable.encode b).bodd then -((a.natAbs * b.natAbs : ℕ) : ℤ) else
      ((a.natAbs * b.natAbs : ℕ) : ℤ))) = a * b
  have hsign (z : ℤ) : (Encodable.encode z).bodd = decide (z < 0) := by
    cases z with
    | ofNat n =>
      change (Nat.bit false n).bodd = decide ((n : ℤ) < 0)
      simp
    | negSucc n =>
      change (Nat.bit true n).bodd = decide (Int.negSucc n < 0)
      simp

  rw [hsign a, hsign b]
  simp only [Bool.cond_decide, Nat.cast_mul, Int.natCast_natAbs]
  split_ifs with ha hb hb <;> simp_all [abs_of_neg, abs_of_nonneg, not_lt]

end Arithmetic
end AlternatingNS

namespace AlternatingNS.Arithmetic
lemma nat_dvd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

lemma nat_gcd : Primrec₂ Nat.gcd := by
  have h := Primrec.nat_findGreatest (p := fun z : ℕ × ℕ => fun d => d ∣ z.1 ∧ d ∣ z.2)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)
    ((nat_dvd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (nat_dvd.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  refine h.of_eq ?_
  rintro ⟨a,b⟩
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨?_, fun _ => ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩, ?_⟩
  · by_cases ha : a = 0
    · simp [ha]
    · exact (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)).trans (Nat.le_add_right a b)
  · intro d hd _ hab
    have hpos : 0 < a.gcd b := by
      by_contra hn
      have hz := Nat.gcd_eq_zero_iff.mp (by omega : a.gcd b = 0)
      omega
    exact (not_lt_of_ge (Nat.le_of_dvd hpos (Nat.dvd_gcd hab.1 hab.2))) hd

lemma rat_valid : PrimrecPred (fun z : ℤ × ℕ => 0 < z.2 ∧ z.1.natAbs.Coprime z.2) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (Primrec.eq.comp (nat_gcd.comp (int_abs.comp Primrec.fst) Primrec.snd) (Primrec.const 1))

def ratEquiv : ℚ ≃ {z : ℤ × ℕ // 0 < z.2 ∧ z.1.natAbs.Coprime z.2} where
  toFun q := ⟨(q.num,q.den), q.den_pos, q.reduced⟩
  invFun q := ⟨q.1.1,q.1.2, Nat.ne_of_gt q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def rationalCoding : Primcodable ℚ := by
  letI := Primcodable.subtype rat_valid
  exact Primcodable.ofEquiv _ ratEquiv

lemma rationalCoding_encode (q : ℚ) :
    @Encodable.encode ℚ rationalCoding.toEncodable q = Encodable.encode q := rfl

attribute [local instance] rationalCoding

lemma rat_num : Primrec Rat.num := by
  let := Primcodable.subtype rat_valid
  have := Primrec.fst.comp (Primrec.subtype_val (hp := rat_valid))
  exact this.comp (Primrec.of_equiv (e := ratEquiv))

lemma rat_den : Primrec Rat.den := by
  let := Primcodable.subtype rat_valid
  exact (Primrec.snd.comp (Primrec.subtype_val (hp := rat_valid))).comp
    (Primrec.of_equiv (e := ratEquiv))

lemma int_ediv_nat : Primrec₂ (fun z : ℤ => fun d : ℕ => z / (d : ℤ)) := by
  have h := int_cases
    (f := fun d n : ℕ => ((n / d : ℕ) : ℤ))
    (g := fun d n => if d = 0 then 0 else Int.negSucc (n / d))
    (int_natCast.comp (Primrec.nat_div.comp Primrec.snd Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (int_negSucc.comp (Primrec.nat_div.comp Primrec.snd Primrec.fst)))
  refine (h.comp (Primrec.snd.pair Primrec.fst)).of_eq ?_
  rintro ⟨z,d⟩
  cases z with
  | ofNat n => exact Int.natCast_ediv n d
  | negSucc n => cases d <;> rfl

lemma rat_mk : Primrec₂ mkRat := by
  have hz : PrimrecPred (fun z : ℤ × ℕ => z.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hg : Primrec (fun z : ℤ × ℕ => z.2.gcd z.1.natAbs) :=
    nat_gcd.comp Primrec.snd (int_abs.comp Primrec.fst)
  have hn := Primrec.ite hz (Primrec.const (0 : ℤ)) (int_ediv_nat.comp Primrec.fst hg)
  have hd := Primrec.ite hz (Primrec.const (1 : ℕ)) (Primrec.nat_div.comp Primrec.snd hg)
  apply Primrec.encode_iff.mp
  refine (Primrec₂.natPair.comp (Primrec.encode.comp hn) hd).of_eq ?_
  rintro ⟨n,d⟩
  change Nat.pair (Encodable.encode (if d = 0 then (0 : ℤ) else n / ↑(d.gcd n.natAbs)))
    (if d = 0 then 1 else d / d.gcd n.natAbs) =
    Nat.pair (Encodable.encode (mkRat n d).num) (mkRat n d).den
  rw [Rat.num_mkRat, Rat.den_mkRat]

lemma rat_intCast : Primrec (fun n : ℤ => (n : ℚ)) := by
  exact (rat_mk.comp Primrec.id (Primrec.const 1)).of_eq (fun n => by simp [Rat.mkRat_eq_div])

lemma rat_natCast : Primrec (fun n : ℕ => (n : ℚ)) :=
  (rat_intCast.comp int_natCast).of_eq (fun n => by simp)

lemma rat_add : Primrec₂ (fun a b : ℚ => a + b) := by
  have hn := int_add.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_natCast.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_natCast.comp (rat_den.comp Primrec.fst)))
  have hd := Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd)
  exact (rat_mk.comp hn hd).of_eq (fun z => by
    dsimp only
    rw [Rat.add_def, Rat.normalize_eq_mkRat])

lemma rat_mul : Primrec₂ (fun a b : ℚ => a * b) := by
  exact (rat_mk.comp (int_mul.comp (rat_num.comp Primrec.fst) (rat_num.comp Primrec.snd))
    (Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd))).of_eq
    (fun z => (Rat.mul_eq_mkRat z.1 z.2).symm)

lemma rat_neg : Primrec (fun a : ℚ => -a) := by
  refine (rat_mk.comp (int_neg.comp rat_num) rat_den).of_eq ?_
  intro q
  rw [Rat.mkRat_eq_div, Int.cast_neg, neg_div, Rat.num_div_den]

lemma rat_sub : Primrec₂ (fun a b : ℚ => a - b) :=
  (rat_add.comp Primrec.fst (rat_neg.comp Primrec.snd)).of_eq (fun _ => (sub_eq_add_neg _ _).symm)

lemma int_le : PrimrecRel (fun a b : ℤ => a ≤ b) :=
  (Primrec.eq.comp (int_toNat.comp int_sub) (Primrec.const 0)).of_eq (fun z => by
    dsimp only; omega)

lemma int_lt : PrimrecRel (fun a b : ℤ => a < b) :=
  (int_le.comp Primrec.snd Primrec.fst).not.of_eq (fun z => by simp)

lemma rat_divInt : Primrec₂ Rat.divInt := by
  have h := int_cases (f := fun a : ℤ => fun d : ℕ => mkRat a d)
    (g := fun a d => mkRat (-a) (d + 1)) rat_mk
    (rat_mk.comp (int_neg.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  refine h.of_eq ?_
  rintro ⟨n,d⟩
  cases d with
  | ofNat d => rfl
  | negSucc d => exact (Rat.normalize_eq_mkRat (Nat.succ_ne_zero d)).symm

lemma rat_inv : Primrec (fun q : ℚ => q⁻¹) :=
  (rat_divInt.comp (int_natCast.comp rat_den) rat_num).of_eq (fun q => (Rat.inv_def q).symm)

lemma rat_div : Primrec₂ (fun a b : ℚ => a / b) :=
  (rat_mul.comp Primrec.fst (rat_inv.comp Primrec.snd)).of_eq
    (fun _ => (div_eq_mul_inv _ _).symm)

lemma rat_le : PrimrecRel (fun a b : ℚ => a ≤ b) :=
  (int_le.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_natCast.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_natCast.comp (rat_den.comp Primrec.fst)))).of_eq
    (fun z => (Rat.le_iff z.1 z.2).symm)

lemma rat_lt : PrimrecRel (fun a b : ℚ => a < b) :=
  (rat_le.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => by simp)

lemma rat_abs : Primrec (fun a : ℚ => |a|) :=
  (Primrec.ite (rat_le.comp (Primrec.const 0) Primrec.id) Primrec.id rat_neg).of_eq
    (fun a => by
      change (if 0 ≤ a then a else -a) = |a|
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm)

lemma rat_floor : Primrec (fun q : ℚ => ⌊q⌋) := by
  change Primrec Rat.floor
  exact (int_ediv_nat.comp rat_num rat_den).of_eq (fun q => (Rat.floor_def q).symm)

lemma rat_pow : Primrec₂ (fun q : ℚ => fun n : ℕ => q ^ n) := by
  have hs : Primrec₂ (fun q : ℚ => fun z : ℕ × ℚ => z.2 * q) :=
    rat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  refine (Primrec.nat_rec (Primrec.const (1 : ℚ)) hs).of_eq ?_
  intro q n
  induction n with
  | zero => simp
  | succ n ih => simpa only [ih] using (pow_succ q n).symm

end AlternatingNS.Arithmetic

end ArithmeticDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Names.lean =====
namespace OAI

section NamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective

attribute [local instance] Arithmetic.rationalCoding

def tolerance (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n

lemma tolerance_cast (n : ℕ) : (tolerance n : ℝ) = dyadicError n := by
  simp [tolerance, dyadicError]

lemma tolerance_primrec : Primrec tolerance :=
  Arithmetic.rat_pow.comp (Primrec.const (1 / 2)) Primrec.id

lemma tolerance_pos (n : ℕ) : (0 : ℝ) < tolerance n := by
  rw [tolerance_cast]; exact pow_pos (by norm_num) _

lemma tolerance_tendsto : Tendsto (fun n => (tolerance n : ℝ)) atTop (𝓝 0) := by
  simp only [tolerance_cast, dyadicError]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def Named {A : Type*} [Primcodable A] (f : A → ℝ) : Prop :=
  ∃ a : A × ℕ → ℚ, Computable a ∧
    ∀ x n, |f x - (a (x,n) : ℝ)| ≤ tolerance n

lemma computable_find {A : Type*} [Primcodable A] (p : A → ℕ → Prop)
    [DecidableRel p] (hp : Computable (fun z : A × ℕ => decide (p z.1 z.2)))
    (h : ∀ a, ∃ n, p a n) : Computable (fun a => @Nat.find (p a) (fun _ => inferInstance) (h a)) := by
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (decide (p a n)))) :=
    Partrec.rfind hp.to₂.partrec₂
  apply hr.of_eq_tot
  intro a
  apply Nat.mem_rfind.mpr
  refine ⟨?_, fun {m} hm => ?_⟩
  · simp [Nat.find_spec (h a)]
  · simp [Nat.find_min (h a) hm]

lemma Named.of_certificate {A : Type*} [Primcodable A] (f : A → ℝ)
    (a e : A × ℕ → ℚ) (ha : Computable a) (he : Computable e)
    (hbound : ∀ x n, |f x - (a (x,n) : ℝ)| ≤ (e (x,n) : ℝ))
    (hlim : ∀ x, Tendsto (fun n => (e (x,n) : ℝ)) atTop (𝓝 0)) : Named f := by
  classical
  let p (z : A × ℕ) (n : ℕ) : Prop := e (z.1,n) ≤ tolerance z.2
  have hp : Computable (fun z : (A × ℕ) × ℕ => decide (p z.1 z.2)) :=
    Arithmetic.rat_le.decide.to_comp.comp
      (he.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (tolerance_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
  have hex (z : A × ℕ) : ∃ n, p z n := by
    have hE := (hlim z.1).eventually (gt_mem_nhds (tolerance_pos z.2))
    obtain ⟨n,hn⟩ := hE.exists
    exact ⟨n, by exact_mod_cast hn.le⟩
  let N (z : A × ℕ) : ℕ := Nat.find (hex z)
  have hN : Computable N := computable_find p hp hex
  refine ⟨fun z => a (z.1,N z), ha.comp (Computable.fst.pair hN), fun x k => ?_⟩
  exact (hbound x (N (x,k))).trans (by exact_mod_cast Nat.find_spec (hex (x,k)))

lemma Named.congr {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (h : ∀ a, f a = g a) : Named g := by
  simpa only [show f = g from funext h] using hf

lemma Named.comp {A B : Type*} [Primcodable A] [Primcodable B] {f : A → ℝ}
    (hf : Named f) {g : B → A} (hg : Computable g) : Named (f ∘ g) := by
  obtain ⟨a, ha, hb⟩ := hf
  exact ⟨fun z => a (g z.1,z.2),
    ha.comp ((hg.comp Computable.fst).pair Computable.snd), fun z n => hb (g z) n⟩

lemma Named.rational {A : Type*} [Primcodable A] {f : A → ℚ} (hf : Computable f) :
    Named (fun a => (f a : ℝ)) :=
  ⟨fun z => f z.1, hf.comp Computable.fst, fun _ n => by
    simp only [sub_self, abs_zero]; exact (tolerance_pos n).le⟩

lemma Named.const {A : Type*} [Primcodable A] (q : ℚ) : Named (fun _ : A => (q : ℝ)) :=
  Named.rational (Computable.const q)

lemma approximation_tendsto {x : ℝ} {a : ℕ → ℚ}
    (h : ∀ n, |x - (a n : ℝ)| ≤ tolerance n) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => x - (tolerance n : ℝ))
    (h := fun n => x + (tolerance n : ℝ))
  · simpa using tendsto_const_nhds.sub tolerance_tendsto
  · simpa using tendsto_const_nhds.add tolerance_tendsto
  · intro n; have := (abs_le.mp (h n)).2; linarith
  · intro n; have := (abs_le.mp (h n)).1; linarith

lemma Named.add {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x + g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  apply Named.of_certificate _ (fun z => a z + b z) (fun z => 2 * tolerance z.2)
    (Arithmetic.rat_add.to_comp.comp ha hb)
    (Arithmetic.rat_mul.to_comp.comp (Computable.const 2)
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    push_cast
    calc
      _ = |(f x - (a (x,n) : ℝ)) + (g x - (b (x,n) : ℝ))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (by linarith [hae x n, hbe x n])
  · intro x; simpa using (tolerance_tendsto.const_mul 2)

lemma Named.neg {A : Type*} [Primcodable A] {f : A → ℝ} (hf : Named f) :
    Named (fun x => -f x) := by
  obtain ⟨a,ha,h⟩ := hf
  refine ⟨fun z => -a z, Arithmetic.rat_neg.to_comp.comp ha, fun x n => ?_⟩
  simpa only [Rat.cast_neg, neg_sub_neg, abs_sub_comm] using h x n

lemma Named.sub {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x - g x) :=
  (hf.add hg.neg).congr (fun _ => (sub_eq_add_neg _ _).symm)

lemma Named.mul {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x * g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  let e : A × ℕ → ℚ := fun z => (|a z| + |b z| + tolerance z.2) * tolerance z.2
  have he : Computable e := Arithmetic.rat_mul.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp
      (Arithmetic.rat_add.to_comp.comp (Arithmetic.rat_abs.to_comp.comp ha)
        (Arithmetic.rat_abs.to_comp.comp hb))
      (tolerance_primrec.to_comp.comp Computable.snd))
    (tolerance_primrec.to_comp.comp Computable.snd)
  apply Named.of_certificate _ (fun z => a z * b z) e
    (Arithmetic.rat_mul.to_comp.comp ha hb) he
  · intro x n
    dsimp [e]; push_cast
    have hf : |f x| ≤ |(a (x,n) : ℝ)| + (tolerance n : ℝ) := by
      have h := abs_add_le (f x - (a (x,n) : ℝ)) (a (x,n))
      ring_nf at h
      linarith [hae x n]
    calc
      _ = |f x * (g x - (b (x,n) : ℝ)) + (f x - (a (x,n) : ℝ)) * (b (x,n) : ℝ)| := by congr 1; ring
      _ ≤ |f x| * |g x - (b (x,n) : ℝ)| + |f x - (a (x,n) : ℝ)| * |(b (x,n) : ℝ)| := by
        simpa only [abs_mul] using abs_add_le (f x * (g x - (b (x,n) : ℝ))) ((f x - (a (x,n) : ℝ)) * (b (x,n) : ℝ))
      _ ≤ (|(a (x,n) : ℝ)| + (tolerance n : ℝ)) * (tolerance n : ℝ) +
          (tolerance n : ℝ) * |(b (x,n) : ℝ)| :=
        add_le_add (mul_le_mul hf (hbe x n) (abs_nonneg _) (add_nonneg (abs_nonneg _) (tolerance_pos n).le))
          (mul_le_mul_of_nonneg_right (hae x n) (abs_nonneg _))
      _ = _ := by ring
  · intro x
    dsimp [e]
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
    simpa using (((approximation_tendsto (hae x)).abs.add
      (approximation_tendsto (hbe x)).abs).add tolerance_tendsto).mul tolerance_tendsto

lemma Named.ite {A : Type*} [Primcodable A] (p : A → Prop) [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => if p x then f x else g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  refine ⟨fun z => if p z.1 then a z else b z,
    (Computable.cond (hp.comp Computable.fst) ha hb).of_eq (by simp), ?_⟩
  intro x n; dsimp only; split_ifs <;> simp_all

lemma Named.apply_lipschitz {A : Type*} [Primcodable A] (g : A → ℝ → ℝ)
    (L : A → ℚ) (hL : Computable L) (hpos : ∀ a, 0 ≤ L a)
    (hLip : ∀ a x y, |g a x - g a y| ≤ (L a : ℝ) * |x - y|)
    (hg : Named (fun z : A × ℚ => g z.1 z.2))
    {f : A → ℝ} (hf : Named f) : Named (fun a => g a (f a)) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  apply Named.of_certificate _ (fun z => b ((z.1,a z),z.2))
    (fun z => (L z.1 + 1) * tolerance z.2)
    (hb.comp ((Computable.fst.pair ha).pair Computable.snd))
    (Arithmetic.rat_mul.to_comp.comp
      (Arithmetic.rat_add.to_comp.comp (hL.comp Computable.fst) (Computable.const 1))
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    push_cast
    calc
      _ ≤ |g x (f x) - g x (a (x,n))| + |g x (a (x,n)) - (b ((x,a (x,n)),n) : ℝ)| := abs_sub_le _ _ _
      _ ≤ (L x : ℝ) * (tolerance n : ℝ) + (tolerance n : ℝ) :=
        add_le_add ((hLip x _ _).trans (mul_le_mul_of_nonneg_left (hae x n) (by exact_mod_cast hpos x)))
          (hbe (x,a (x,n)) n)
      _ = _ := by ring
  · intro x; simpa using tolerance_tendsto.const_mul ((L x : ℝ) + 1)

end AlternatingNS.Effective

end NamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/ExpNames.lean =====
namespace OAI

section ExpNamesDevelopment

open scoped BigOperators ContDiff Topology
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma rat_sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℚ}
    (hf : Computable₂ f) : Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Computable₂ (fun a : A => fun z : ℕ × ℚ => z.2 + f a z.1) :=
    Arithmetic.rat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have h := Computable.nat_rec (Computable.snd : Computable (fun z : A × ℕ => z.2))
    (Computable.const (0 : ℚ))
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  refine h.to₂.of_eq ?_
  rintro ⟨a,n⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

lemma abs_rat_cast_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have h : (q.den : ℝ) ≥ 1 := by exact_mod_cast q.den_pos
  rw [Rat.cast_def, abs_div, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_self (Nat.cast_nonneg _) h

lemma exp_named : Named (fun q : ℚ => Real.exp (q : ℝ)) := by
  let N (z : ℚ × ℕ) : ℕ := 2 * z.1.num.natAbs + z.2 + 1
  have hN : Computable N := (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Arithmetic.int_abs.comp (Arithmetic.rat_num.comp Primrec.fst))) Primrec.snd)
    (Primrec.const 1)).to_comp
  let a (z : ℚ × ℕ) : ℚ := ∑ i ∈ Finset.range (N z), z.1 ^ i / i.factorial
  let err (z : ℚ × ℕ) : ℚ := |z.1| ^ N z / (N z).factorial * 2
  have ht : Computable₂ (fun q : ℚ => fun i : ℕ => q ^ i / i.factorial) :=
    Arithmetic.rat_div.to_comp.comp Arithmetic.rat_pow.to_comp
      (Arithmetic.rat_natCast.to_comp.comp (factorial.to_comp.comp Computable.snd))
  have ha : Computable a := (rat_sum_range ht).comp Computable.fst hN
  have he : Computable err := Arithmetic.rat_mul.to_comp.comp
    (Arithmetic.rat_div.to_comp.comp
      (Arithmetic.rat_pow.to_comp.comp (Arithmetic.rat_abs.to_comp.comp Computable.fst) hN)
      (Arithmetic.rat_natCast.to_comp.comp (factorial.to_comp.comp hN))) (Computable.const 2)
  apply Named.of_certificate _ a err ha he
  · intro q n
    have hl : ‖(q : ℂ)‖ / (N (q,n)).succ ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N (q,n)).succ)]
      rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
      have hh := abs_rat_cast_le_num q
      dsimp [N]; push_cast; linarith
    have h := Complex.exp_bound' hl
    have hc : (∑ i ∈ Finset.range (N (q,n)), (q : ℂ) ^ i / i.factorial) = (a (q,n) : ℂ) := by
      simp [a]
    rw [hc, show (q : ℂ) = ((q : ℝ) : ℂ) by simp, ← Complex.ofReal_exp,
      show (a (q,n) : ℂ) = ((a (q,n) : ℝ) : ℂ) by simp,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs] at h
    simpa only [err, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_abs,
      Rat.cast_natCast, Rat.cast_ofNat] using h
  · intro q
    have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop |(q : ℝ)|).mul_const 2
    have hshift : Tendsto (fun n => N (q,n)) atTop atTop := by
      apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
      intro n; dsimp [N]; omega
    simpa only [err, Function.comp_def, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, zero_mul] using hlim.comp hshift

end AlternatingNS.Effective

end ExpNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/ProfileNames.lean =====
namespace OAI

section ProfileNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma rat_max : Primrec₂ (fun x y : ℚ => max x y) :=
  (Primrec.ite Arithmetic.rat_le Primrec.snd Primrec.fst).of_eq (by intro z; simp [max_def])

lemma Named.inv_of_lower {A : Type*} [Primcodable A] {f : A → ℝ}
    (hf : Named f) (b : A → ℚ) (hb : Computable b) (hpos : ∀ x, 0 < b x)
    (hlower : ∀ x, (b x : ℝ) ≤ f x) : Named (fun x => (f x)⁻¹) := by
  obtain ⟨a,ha,he⟩ := hf
  let c : A × ℕ → ℚ := fun z => max (b z.1) (a z)
  have hc : Computable c := rat_max.to_comp.comp (hb.comp Computable.fst) ha
  apply Named.of_certificate _ (fun z => (c z)⁻¹)
    (fun z => (b z.1)⁻¹ ^ 2 * tolerance z.2)
    (Arithmetic.rat_inv.to_comp.comp hc)
    (Arithmetic.rat_mul.to_comp.comp
      (Arithmetic.rat_pow.to_comp.comp (Arithmetic.rat_inv.to_comp.comp (hb.comp Computable.fst))
        (Computable.const 2)) (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    have hb₀ : (0 : ℝ) < b x := by exact_mod_cast hpos x
    have hc₀ : (b x : ℝ) ≤ c (x,n) := by exact_mod_cast (le_max_left (b x) (a (x,n)))
    have ha₀ : (a (x,n) : ℝ) ≤ c (x,n) := by exact_mod_cast (le_max_right (b x) (a (x,n)))
    have hce : |f x - (c (x,n) : ℝ)| ≤ tolerance n := by
      rw [abs_le]
      have h := abs_le.mp (he x n)
      refine ⟨?_, by linarith⟩
      have hmax : (c (x,n) : ℝ) ≤ f x + (tolerance n : ℝ) := by
        dsimp only [c]; push_cast
        apply max_le
        · exact (hlower x).trans (le_add_of_nonneg_right (tolerance_pos n).le)
        · linarith
      linarith
    have hfx : 0 < f x := hb₀.trans_le (hlower x)
    have hcx : 0 < (c (x,n) : ℝ) := hb₀.trans_le hc₀
    push_cast
    rw [inv_sub_inv hfx.ne' hcx.ne', abs_div, abs_mul,
      abs_of_pos hfx, abs_of_pos hcx, abs_sub_comm]
    calc
      _ ≤ (tolerance n : ℝ) / ((b x : ℝ) * (b x : ℝ)) :=
        div_le_div₀ (tolerance_pos n).le hce (mul_pos hb₀ hb₀)
          (mul_le_mul (hlower x) hc₀ hb₀.le hfx.le)
      _ = _ := by ring
  · intro x
    convert tolerance_tendsto.const_mul ((b x : ℝ)⁻¹ ^ 2) using 1 <;>
      simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, inv_pow, mul_zero]

lemma Named.sum_range {A : Type*} [Primcodable A] {f : A × ℕ → ℝ}
    (hf : Named f) (N : A → ℕ) (hN : Computable N) :
    Named (fun x => ∑ i ∈ Finset.range (N x), f (x,i)) := by
  obtain ⟨a,ha,he⟩ := hf
  have hs : Computable₂ (fun z : A × ℕ => fun i : ℕ => a ((z.1,i),z.2)) :=
    ha.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  apply Named.of_certificate _ (fun z => ∑ i ∈ Finset.range (N z.1), a ((z.1,i),z.2))
    (fun z => (N z.1 : ℚ) * tolerance z.2)
    ((rat_sum_range hs).comp Computable.id (hN.comp Computable.fst))
    (Arithmetic.rat_mul.to_comp.comp (Arithmetic.rat_natCast.to_comp.comp (hN.comp Computable.fst))
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n; push_cast; rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (N x), (tolerance n : ℝ) := Finset.sum_le_sum (fun i _ => he (x,i) n)
      _ = _ := by simp
  · intro x; push_cast
    simpa only [inv_pow, mul_zero] using tolerance_tendsto.const_mul (N x : ℝ)

lemma rho_named : Named (fun q : ℚ => expNegInvGlue (q : ℝ)) := by
  have hn := exp_named.comp (Arithmetic.rat_neg.comp Arithmetic.rat_inv |>.to_comp)
  exact (Named.ite (fun q : ℚ => q ≤ 0)
    (Arithmetic.rat_le.decide.to_comp.comp Computable.id (Computable.const 0))
    (Named.const 0) hn).congr (by intro q; simp [expNegInvGlue])

lemma transition_named : Named (fun q : ℚ => Real.smoothTransition (q : ℝ)) := by
  have h₂ := rho_named.comp (Arithmetic.rat_sub.to_comp.comp (Computable.const 1) Computable.id)
  have hd := rho_named.add h₂
  have hi := hd.inv_of_lower (fun _ => 1/9) (Computable.const _) (by intro; norm_num)
    (by intro q; simpa [Function.comp_def] using Quantitative.transition_denom_lower (q : ℝ))
  exact (rho_named.mul hi).congr (by intro q; simp [Real.smoothTransition, div_eq_mul_inv])

lemma jet_one_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (B : ℕ)
    (hB : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ B) (x y : ℝ) :
    |f x - f y| ≤ (B : ℝ) * |x-y| := by
  have h : ∀ x, ‖deriv f x‖ ≤ (B : ℝ) := by
    intro z
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] using hB z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Set.univ) => hf.differentiable (by simp) z) (fun z _ => h z)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)

lemma Named.transition {A : Type*} [Primcodable A] {f : A → ℝ} (hf : Named f) :
    Named (fun a => Real.smoothTransition (f a)) := by
  apply Named.apply_lipschitz (fun _ => Real.smoothTransition)
    (fun _ => (Quantitative.transitionBound 1 : ℚ)) (Computable.const _) (fun _ => by positivity)
    (fun _ x y => ?_) (transition_named.comp Computable.snd) hf
  simpa only [Rat.cast_natCast] using jet_one_lipschitz Real.smoothTransition.contDiff
    (Quantitative.transitionBound 1) (Quantitative.transition_jet_bound 1) x y

end AlternatingNS.Effective

end ProfileNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DecoderBounds.lean =====
namespace OAI

section DecoderBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Quantitative

lemma linear_id_jet (r : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |iteratedDeriv r id x| ≤ 1 := by
  rw [iteratedDeriv_id]; split_ifs <;> simp_all

lemma transition_affine (r : ℕ) (a d : ℝ) :
    iteratedDeriv r (fun x => Real.smoothTransition ((x-a)/d)) =
      fun x => d⁻¹ ^ r * iteratedDeriv r Real.smoothTransition ((x-a)/d) := by
  have h : (fun x => Real.smoothTransition ((x-a)/d)) =
      (fun x => Real.smoothTransition (d⁻¹ * (x-a))) := by funext x; congr 1; ring
  rw [h, iteratedDeriv_comp_sub_const r (fun z => Real.smoothTransition (d⁻¹ * z)) a,
    iteratedDeriv_comp_const_mul
    (Real.smoothTransition.contDiff.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [div_eq_mul_inv, mul_comm]

lemma periodizer_jet_bound (r : ℕ) (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1)
    (x : ℝ) :
    ‖iteratedFDeriv ℝ r (Profiles.periodizer a c) x‖ ≤
      1 + (c-a)⁻¹ ^ r * transitionBound r := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  have hnon : 0 ≤ (c-a)⁻¹ ^ r * (transitionBound r : ℝ) := by positivity
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have he : Profiles.periodizer a c =ᶠ[𝓝 x] (fun y => y - (⌊x⌋ : ℝ)) := by
      have hlo : (⌊x⌋ : ℝ) + (c - 1) < x := by linarith
      have hhi : x < (⌊x⌋ : ℝ) + a := by linarith
      filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
      have hy' : y - (⌊x⌋ : ℝ) ∈ Set.Ioo (c - 1) a := by
        constructor <;> linarith [hy.1, hy.2]
      calc
        Profiles.periodizer a c y = Profiles.periodizer a c ((⌊x⌋ : ℝ) + (y - (⌊x⌋ : ℝ))) := by congr 1; ring
        _ = Profiles.periodizer a c (y - (⌊x⌋ : ℝ)) := Profiles.periodizer_int_add a c _ _
        _ = y - (⌊x⌋ : ℝ) := Profiles.periodizer_near_zero a c ha hac hc _ hy'
    rw [he.iteratedDeriv_eq r]
    change |iteratedDeriv r (fun y => id (y - (⌊x⌋ : ℝ))) x| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    exact (linear_id_jet r (by rw [hx]; simp)).trans (le_add_of_nonneg_right hnon)
  · have he : Profiles.periodizer a c =ᶠ[𝓝 x]
        (fun y => (y - (⌊x⌋ : ℝ)) - Real.smoothTransition ((y - (⌊x⌋ : ℝ)-a)/(c-a))) := by
      have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
      filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
      have hy' : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
      simp only [Profiles.periodizer, Int.fract, hy']
    rw [he.iteratedDeriv_eq r]
    change |iteratedDeriv r (fun y => ((id : ℝ → ℝ) - fun z => Real.smoothTransition ((z-a)/(c-a)))
      (y - (⌊x⌋ : ℝ))) x| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    dsimp only
    rw [iteratedDeriv_sub contDiffAt_id
      (show ContDiffAt ℝ (r : ℕ∞ω) (fun z => Real.smoothTransition ((z-a)/(c-a))) (x - (⌊x⌋ : ℝ)) from by fun_prop),
      transition_affine]
    calc
      _ ≤ |iteratedDeriv r id (x - (⌊x⌋ : ℝ))| +
          (c-a)⁻¹ ^ r * |iteratedDeriv r Real.smoothTransition ((x - (⌊x⌋:ℝ)-a)/(c-a))| := by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hac).le) r)] using
          norm_sub_le (iteratedDeriv r id (x - (⌊x⌋ : ℝ)))
            ((c-a)⁻¹ ^ r * iteratedDeriv r Real.smoothTransition ((x - (⌊x⌋:ℝ)-a)/(c-a)))
      _ ≤ _ := add_le_add (linear_id_jet r (by
          rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
          linarith [Int.lt_floor_add_one x]))
        (mul_le_mul_of_nonneg_left
          (by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
            transition_jet_bound r ((x - (⌊x⌋:ℝ)-a)/(c-a)))
          (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hac).le) r))

def decoderBound (b r : ℕ) : ℕ := 1 + (3 * (b - 1)) ^ r * transitionBound r

lemma decoder_jet_bound (b : ℕ) (hb : 2 ≤ b) (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (Profiles.decoder b) x‖ ≤ decoderBound b r := by
  have hm0 := Encoding.tailMax_nonneg b hb
  have hm1 := Encoding.tailMax_lt_one b hb
  have hgap : (((Encoding.tailMax b + 2) / 3) - ((2 * Encoding.tailMax b + 1) / 3))⁻¹ =
      (3 * (b - 1) : ℕ) := by
    have hbn : (b - 1 : ℕ) = (b : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ b)
    rw [Nat.cast_mul, hbn]
    have h : (b : ℝ) - 1 ≠ 0 := by
      have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    unfold Encoding.tailMax
    field_simp
    ring
  have h := periodizer_jet_bound r ((2 * Encoding.tailMax b + 1) / 3)
    ((Encoding.tailMax b + 2) / 3) (by linarith) (by linarith) (by linarith) x
  rw [hgap] at h
  simpa only [Profiles.decoder, decoderBound, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using h

end AlternatingNS.Quantitative

end DecoderBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DecoderNames.lean =====
namespace OAI

section DecoderNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma decoderBound : Primrec₂ Quantitative.decoderBound :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_mul.comp
      (nat_pow.comp (Primrec.nat_mul.comp (Primrec.const 3)
        (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))) Primrec.snd)
      (transitionBound.comp Primrec.snd))

lemma rat_fract : Primrec (fun q : ℚ => Int.fract q) :=
  Arithmetic.rat_sub.comp Primrec.id (Arithmetic.rat_intCast.comp Arithmetic.rat_floor)

lemma frac_cast (q : ℚ) : ((Int.fract q : ℚ) : ℝ) = Int.fract (q : ℝ) := by
  simp only [Int.fract, Rat.cast_sub, Rat.cast_intCast, Rat.floor_cast]

lemma periodizer_named : Named (fun z : (ℚ × ℚ) × ℚ => Profiles.periodizer z.1.1 z.1.2 z.2) := by
  have hv : Computable (fun z : (ℚ × ℚ) × ℚ => Int.fract z.2) := rat_fract.to_comp.comp Computable.snd
  have hA : Computable (fun z : (ℚ × ℚ) × ℚ => (Int.fract z.2 - z.1.1)/(z.1.2-z.1.1)) :=
    Arithmetic.rat_div.to_comp.comp
      (Arithmetic.rat_sub.to_comp.comp hv (Computable.fst.comp Computable.fst))
      (Arithmetic.rat_sub.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.fst))
  exact ((Named.rational hv).sub (transition_named.comp hA)).congr (by
    intro z
    simp only [Function.comp_def, Profiles.periodizer, Rat.cast_div, Rat.cast_sub]
    rw [frac_cast])

lemma decoder_named : Named (fun z : ℕ × ℚ => Profiles.decoder z.1 (z.2 : ℝ)) := by
  let m (b : ℕ) : ℚ := ((b : ℚ)-2)/((b : ℚ)-1)
  have hm : Computable m := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_sub.to_comp.comp Arithmetic.rat_natCast.to_comp (Computable.const 2))
    (Arithmetic.rat_sub.to_comp.comp Arithmetic.rat_natCast.to_comp (Computable.const 1))
  have ha : Computable (fun z : ℕ × ℚ => (2*m z.1+1)/3) := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp
      (Arithmetic.rat_mul.to_comp.comp (Computable.const 2) (hm.comp Computable.fst))
      (Computable.const 1)) (Computable.const 3)
  have hc : Computable (fun z : ℕ × ℚ => (m z.1+2)/3) := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp (hm.comp Computable.fst) (Computable.const 2)) (Computable.const 3)
  exact (periodizer_named.comp ((ha.pair hc).pair Computable.snd)).congr (by
    intro z; simp [Profiles.decoder, Encoding.tailMax, m])

lemma Named.decoder {A : Type*} [Primcodable A] (b : A → ℕ) (hb : Computable b)
    (hbase : ∀ x, 2 ≤ b x) {f : A → ℝ} (hf : Named f) :
    Named (fun x => Profiles.decoder (b x) (f x)) := by
  let L (x : A) : ℚ := Quantitative.decoderBound (b x) 1
  have hL : Computable L := Arithmetic.rat_natCast.to_comp.comp
    (decoderBound.to_comp.comp hb (Computable.const 1))
  have hg : Named (fun z : A × ℚ => Profiles.decoder (b z.1) (z.2 : ℝ)) :=
    Named.comp (g := fun z : A × ℚ => (b z.1, z.2)) decoder_named
      ((hb.comp Computable.fst).pair Computable.snd)
  have hlip (a : A) (x y : ℝ) : |Profiles.decoder (b a) x - Profiles.decoder (b a) y| ≤
      (L a : ℝ) * |x-y| := by
    simpa only [L, Rat.cast_natCast] using jet_one_lipschitz (Profiles.decoder_smooth _ (hbase a))
      (Quantitative.decoderBound (b a) 1) (Quantitative.decoder_jet_bound (b a) (hbase a) 1) x y
  exact Named.apply_lipschitz (fun x => Profiles.decoder (b x)) L hL
    (fun _ => Nat.cast_nonneg _) hlip hg hf

end AlternatingNS.Effective

end DecoderNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/RecursiveBounds.lean =====
namespace OAI

section RecursiveBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma nat_sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℕ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Computable₂ (fun a : A => fun z : ℕ × ℕ => z.2 + f a z.1) :=
    Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have h := Computable.nat_rec (Computable.snd : Computable (fun z : A × ℕ => z.2))
    (Computable.const (0 : ℕ))
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  refine h.to₂.of_eq ?_
  rintro ⟨a,n⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

def Scaled {A E F : Type*} [Primcodable A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : A → ℕ → ℝ) (f : A → ℕ → E → F) : Prop :=
  (∀ a n, ContDiff ℝ ∞ (f a n)) ∧ ∃ B : A × ℕ → ℕ, Computable B ∧
    ∀ a r n x, ‖iteratedFDeriv ℝ r (f a n) x‖ ≤ (B (a,r) : ℝ) * s a n ^ r

variable {A A' E F G : Type*} [Primcodable A] [Primcodable A']
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma Scaled.congr {s : A → ℕ → ℝ} {f g : A → ℕ → E → F} (hf : Scaled s f)
    (he : ∀ a n x, f a n x = g a n x) : Scaled s g := by
  rwa [← show f = g from funext (fun a => funext (fun n => funext (he a n)))]

lemma Scaled.param {s : A → ℕ → ℝ} {f : A → ℕ → E → F} (hf : Scaled s f)
    (g : A' → A) (hg : Computable g) : Scaled (fun a => s (g a)) (fun a => f (g a)) := by
  obtain ⟨hf,B,hB,h⟩ := hf
  exact ⟨fun a n => hf (g a) n, fun z => B (g z.1,z.2),
    hB.comp ((hg.comp Computable.fst).pair Computable.snd), fun a => h (g a)⟩

lemma Scaled.const {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) (f : A → ℕ → F)
    (B : A → ℕ) (hB : Computable B) (h : ∀ a n, ‖f a n‖ ≤ B a) :
    Scaled s (fun a n (_ : E) => f a n) := by
  refine ⟨fun _ _ => contDiff_const, fun z => B z.1, hB.comp Computable.fst, ?_⟩
  intro a r n x
  cases r with
  | zero => simpa using h a n
  | succ r =>
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _)

lemma Scaled.add {s : A → ℕ → ℝ} {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x + g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => (sf a n).add (sg a n), fun z => Bf z + B z,
    Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  push_cast
  exact (norm_add_le _ _).trans (by linarith [hfa a r n x, hgb a r n x])

lemma Scaled.sub {s : A → ℕ → ℝ} {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x - g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => (sf a n).sub (sg a n), fun z => Bf z + B z,
    Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  push_cast
  exact (norm_sub_le _ _).trans (by linarith [hfa a r n x, hgb a r n x])

lemma Scaled.smul {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) (c : A → ℕ → ℝ) (B : A → ℕ) (hB : Computable B)
    (hc : ∀ a n, |c a n| ≤ B a) : Scaled s (fun a n x => c a n • f a n x) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => contDiff_const.smul (sf a n), fun z => B z.1 * C z,
    Primrec.nat_mul.to_comp.comp (hB.comp Computable.fst) hC, fun a r n x => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, Real.norm_eq_abs]
  push_cast
  calc
    _ ≤ (B a : ℝ) * ((C (a,r) : ℝ) * s a n ^ r) := by gcongr; exact hc a n; exact hfC a r n x
    _ = _ := by ring

lemma Scaled.mul {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f g : A → ℕ → E → ℝ}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x * g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  let C (z : A × ℕ) := ∑ i ∈ Finset.range (z.2+1), z.2.choose i * Bf (z.1,i) * B (z.1,z.2-i)
  have hi : Computable₂ (fun z : A × ℕ => fun i : ℕ => z.2.choose i * Bf (z.1,i) * B (z.1,z.2-i)) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp
        (choose.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
        (hA.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)))
      (hB.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  have hC : Computable C := (nat_sum_range hi).comp Computable.id
    (Computable.succ.comp Computable.snd)
  refine ⟨fun a n => (sf a n).mul (sg a n), C, hC, fun a r n x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (sf a n) (sg a n) x
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1),
          (r.choose i : ℝ) * (Bf (a,i) * s a n ^ i) * (B (a,r-i) * s a n ^ (r-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _))
      · exact hfa a i n x
      · exact hgb a (r-i) n x
    _ = _ := by
      simp only [C, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by simpa using Finset.mem_range.mp hi
      rw [show (r.choose i : ℝ) * (Bf (a,i) * s a n ^ i) * (B (a,r-i) * s a n ^ (r-i)) =
        (r.choose i * Bf (a,i) * B (a,r-i)) * (s a n ^ i * s a n ^ (r-i)) by ring,
        ← pow_add, Nat.add_sub_of_le hir]

lemma Scaled.ite {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) (p : A → ℕ → Prop) [DecidableRel p] :
    Scaled s (fun a n => if p a n then f a n else g a n) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => by dsimp only; split_ifs <;> [exact sf a n; exact sg a n],
    fun z => Bf z + B z, Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  dsimp only
  split_ifs
  · exact (hfa a r n x).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) (pow_nonneg (hs a n) _))
  · exact (hgb a r n x).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) (pow_nonneg (hs a n) _))

lemma Scaled.sum_range {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n)
    {f : (A × ℕ) → ℕ → E → F} (hf : Scaled (fun a => s a.1) f)
    (N : A → ℕ) (hN : Computable N) : Scaled s (fun a n x => ∑ i ∈ Finset.range (N a), f (a,i) n x) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  have hi : Computable₂ (fun z : A × ℕ => fun i : ℕ => B ((z.1,i),z.2)) :=
    hB.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  refine ⟨fun a n => ContDiff.sum fun i _ => sf (a,i) n,
    fun z => ∑ i ∈ Finset.range (N z.1), B ((z.1,i),z.2),
    (nat_sum_range hi).comp Computable.id (hN.comp Computable.fst), fun a r n x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((sf (a,i) n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  simp only [Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => hfB (a,i) r n x)

lemma Scaled.comp {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) {g : A → F → G} (hg : Scaled (fun _ _ => 1) (fun a _ => g a)) :
    Scaled s (fun a n => g a ∘ f a n) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  let C (z : A × ℕ) := ∑ i ∈ Finset.range (z.2+1), B (z.1,i)
  let D (z : A × ℕ) := 1 + ∑ i ∈ Finset.range (z.2+1), Bf (z.1,i)
  have hC : Computable C := (nat_sum_range hB.to₂).comp Computable.fst
    (Computable.succ.comp Computable.snd)
  have hD : Computable D := Primrec.nat_add.to_comp.comp (Computable.const 1)
    ((nat_sum_range hA.to₂).comp Computable.fst (Computable.succ.comp Computable.snd))
  refine ⟨fun a n => (sg a 0).comp (sf a n), fun z => z.2.factorial * C z * D z ^ z.2,
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (factorial.to_comp.comp Computable.snd) hC)
      (nat_pow.to_comp.comp hD Computable.snd), fun a r n x => ?_⟩
  have hDone : (1 : ℝ) ≤ D (a,r) := by dsimp [D]; exact_mod_cast Nat.le_add_right 1 _
  have h := norm_iteratedFDeriv_comp_le (sg a 0) (sf a n)
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) x
    (C := (C (a,r) : ℝ)) (D := (D (a,r) : ℝ) * s a n) ?_ ?_
  · simpa only [Nat.cast_mul, Nat.cast_pow, mul_pow, mul_assoc] using h
  · intro i hi
    have hle : B (a,i) ≤ C (a,r) := Finset.single_le_sum (s := Finset.range (r+1)) (f := fun i => B (a,i)) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
    have ht : ‖iteratedFDeriv ℝ i (g a) (f a n x)‖ ≤ (B (a,i) : ℝ) := by simpa using hgb a i 0 (f a n x)
    exact ht.trans (by exact_mod_cast hle)
  · intro i hi hir
    have hai : (Bf (a,i) : ℝ) ≤ D (a,r) := by
      have h := Finset.single_le_sum (s := Finset.range (r+1)) (f := fun i => Bf (a,i))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : i < r+1))
      exact_mod_cast (by dsimp [D]; omega : Bf (a,i) ≤ D (a,r))
    have hai' := hai.trans (le_self_pow₀ hDone (by omega : i ≠ 0))
    calc
      _ ≤ (Bf (a,i) : ℝ) * s a n ^ i := hfa a i n x
      _ ≤ (D (a,r) : ℝ) ^ i * s a n ^ i := mul_le_mul_of_nonneg_right hai' (pow_nonneg (hs a n) _)
      _ = _ := (mul_pow _ _ _).symm

lemma Scaled.comp_linear {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) (L : A → ℕ → G →L[ℝ] E) (B : A → ℕ) (hB : Computable B)
    (hL : ∀ a n, ‖L a n‖ ≤ B a) : Scaled s (fun a n => f a n ∘ L a n) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => (sf a n).comp (L a n).contDiff, fun z => C z * B z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp hC (nat_pow.to_comp.comp (hB.comp Computable.fst) Computable.snd),
    fun a r n x => ?_⟩
  apply (Bounds.norm_comp_linear (f a n) (sf a n) (L a n) r x).trans
  push_cast
  calc
    _ ≤ ((C (a,r) : ℝ) * s a n ^ r) * (B a : ℝ) ^ r := by
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _)
      · exact hfC a r n _
      · exact hL a n
    _ = _ := by ring

lemma Scaled.comp_scaled_linear {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n) {f : A → E → F}
    (hf : Scaled (fun _ _ => 1) (fun a _ => f a))
    (L : A → ℕ → G →L[ℝ] E) (hL : ∀ a n, ‖L a n‖ ≤ s a n) :
    Scaled s (fun a n => f a ∘ L a n) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨fun a n => (sf a 0).comp (L a n).contDiff, B,hB, fun a r n x => ?_⟩
  apply (Bounds.norm_comp_linear (f a) (sf a 0) (L a n) r x).trans
  apply mul_le_mul (by simpa using hfB a r 0 (L a n x)) (pow_le_pow_left₀ (norm_nonneg _) (hL a n) _)
    (by positivity) (by positivity)

lemma Scaled.fixed {s : A → ℕ → ℝ} (hs : ∀ a n, 1 ≤ s a n) {f : A → E → F}
    (hf : Scaled (fun _ _ => 1) (fun a _ => f a)) : Scaled s (fun a _ => f a) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨sf,B,hB,fun a r n x => ?_⟩
  have h : ‖iteratedFDeriv ℝ r (f a) x‖ ≤ (B (a,r) : ℝ) := by simpa using hfB a r n x
  exact h.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (hs a n)))

end AlternatingNS.Effective

end RecursiveBoundsDevelopment

end OAI


