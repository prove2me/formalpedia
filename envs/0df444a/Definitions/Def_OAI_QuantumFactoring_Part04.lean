-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part04
-- name    : OAI_QuantumFactoring_Part04
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:00:37.20299+00:00
-- url     : https://prove2.me/theorems/b3eb588b-cad9-4506-8844-e816fe56f3e8
-- title:
--   Exact quantum factoring, part 4 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 4 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `CleanPermutation`, `QuantumCore`, `OrderTrial`, `OrderTrialFurther`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CleanPermutation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/QuantumCore.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderTrial.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderTrialFurther.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 4 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: CleanPermutation.lean, QuantumCore.lean, OrderTrial.lean, OrderTrialFurther.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part03

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CleanPermutation.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma packed_single_swap {n r : ℕ} (x y : Basis n) (j : Fin n) :
    packed r x y ∘ Equiv.swap (⟨j.val,by omega⟩ : Fin (n+n+r)) ⟨n+j.val,by omega⟩ =
      packed r (Function.update x j (y j)) (Function.update y j (x j)) := by
  funext i
  by_cases ha : i.val = j.val
  · have hi : i = (⟨j.val,by omega⟩ : Fin (n+n+r)) := Fin.ext ha
    simp only [hi]
    rw [Function.comp_apply, Equiv.swap_apply_left, packed_target]
    simp [packed, j.isLt]
  · by_cases hb : i.val = n+j.val
    · have hi : i = (⟨n+j.val,by omega⟩ : Fin (n+n+r)) := Fin.ext hb
      simp only [hi]
      rw [Function.comp_apply, Equiv.swap_apply_right, packed_input]
      simp [packed, j.isLt]
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (by intro h; exact ha (congrArg Fin.val h))
        (by intro h; exact hb (congrArg Fin.val h))]
      unfold packed
      split_ifs with hn hnn
      · rw [Function.update_of_ne]
        intro h; exact ha (congrArg Fin.val h)
      · rw [Function.update_of_ne]
        intro h
        have hh := congrArg Fin.val h
        dsimp at hh
        omega
      · rfl

def swapPrefix (n r : ℕ) : (k : ℕ) → k ≤ n → List (Instruction (n+n+r))
  | 0, _ => []
  | k+1, h => swapPrefix n r k (by omega) ++
      swapAt ⟨k,by omega⟩ ⟨n+k,by omega⟩ (by intro he; have hh := congrArg Fin.val he; dsimp at hh; omega)

lemma swapPrefix_length (n r k : ℕ) (hk : k ≤ n) :
    (swapPrefix n r k hk).length = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [swapPrefix, swapAt, ih (by omega)]; omega

lemma swapPrefix_basis {n r : ℕ} (x y : Basis n) (k : ℕ) (hk : k ≤ n) :
    (programMatrix (swapPrefix n r k hk)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r (fun i => if i.val<k then y i else x i)
        (fun i => if i.val<k then x i else y i)) := by
  induction k with
  | zero => simp [swapPrefix, programMatrix_nil]
  | succ k ih =>
    rw [swapPrefix, programMatrix_append, ← Matrix.mulVec_mulVec, ih (by omega),
      swapAt_basis, packed_single_swap _ _ (⟨k,by omega⟩ : Fin n)]
    congr 1
    congr 1 <;> funext i
    all_goals
      by_cases hi : i.val=k
      · have he : i = (⟨k,by omega⟩ : Fin n) := Fin.ext hi
        simp only [he]
        simp
      · rw [Function.update_of_ne (by intro he; exact hi (congrArg Fin.val he))]
        have he : (i.val < k+1) ↔ i.val<k := by omega
        simp only [he]

lemma swapBlocks_basis {n r : ℕ} (x y : Basis n) :
    (programMatrix (swapPrefix n r n le_rfl)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r y x) := by
  rw [swapPrefix_basis]
  congr 1
  congr 1 <;> funext i <;> simp [i.isLt]

/-- The standard clean implementation of a bijection uses a verified forward
and inverse Boolean network, two work registers, and only the named gates. -/
def cleanPermutation {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) : List (Instruction (n+n+r)) :=
  oracleOn f hf ++ swapPrefix n r n le_rfl ++ oracleOn g hg

lemma cleanPermutation_basis {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) (x : Basis n)
    (hfg : g.eval (f.eval x) = x) :
    (programMatrix (cleanPermutation f g hf hg)).mulVec
        (basisVector (packed r x (fun _ => false))) =
      basisVector (packed r (f.eval x) (fun _ => false)) := by
  rw [cleanPermutation, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleOn_basis]
  simp only [Bool.false_xor]
  rw [swapBlocks_basis, oracleOn_basis, hfg]
  simp

lemma cleanPermutation_length {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) :
    (cleanPermutation f g hf hg).length ≤ 4*f.net.count+4*g.net.count+7*n := by
  have h₁ := oracleOn_length f hf
  have h₂ := oracleOn_length g hg
  simp only [cleanPermutation, List.length_append, swapPrefix_length]
  omega

end ExactQuantumFactoring.BooleanNetwork


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/QuantumCore.lean =====
namespace OAI

section


/-! Exact integer arithmetic for the prescribed-mass order trial.
These are dependencies of the actual main theorem, not assumptions about an
unknown order and not a replacement target. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators

/-- Number of integers x<Q congruent to t modulo d, when t<d≤Q. -/
def sampleCount (Q d t : ℕ) : ℕ := (Q-1-t)/d+1

lemma sampleCount_bounds {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    Q ≤ t+sampleCount Q d t*d ∧ t+sampleCount Q d t*d ≤ Q+d := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  have hr := Nat.mod_lt (Q-1-t) hd
  have heq : (Q-1-t)%d + ((Q-1-t)/d)*d = Q-1-t := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (Q-1-t) d
  unfold sampleCount
  rw [Nat.add_mul, one_mul]
  omega

lemma lt_sampleCount_iff {Q d t i : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    i < sampleCount Q d t ↔ t+i*d < Q := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  unfold sampleCount
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
  omega

lemma sum_progression {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    (∑ i ∈ Finset.range (sampleCount Q d t), f (t+i*d)) =
      ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), f x := by
  apply Finset.sum_bij (fun i _ => t+i*d)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at *
    refine ⟨(lt_sampleCount_iff hd hdQ ht).mp hi, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · intro i hi j hj heq
    exact Nat.mul_right_cancel hd (Nat.add_left_cancel heq)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have heq : t+(x/d)*d=x := by
      have h := Nat.mod_add_div x d
      rw [hx.2] at h
      simpa only [Nat.mul_comm] using h
    refine ⟨x/d, ?_, heq⟩
    rw [Finset.mem_range, lt_sampleCount_iff hd hdQ ht, heq]
    exact hx.1
  · intro i hi
    rfl

/-- Literal nearest-bin rule floor(jQ/d+1/2), expressed entirely with integers. -/
def bin (Q d j : ℕ) : ℕ := (2*j*Q+d)/(2*d)

noncomputable def binError (Q d j : ℕ) : ℝ := (bin Q d j : ℝ) - (j:ℝ)*Q/d

lemma binError_bound {Q d j : ℕ} (hd : 0 < d) : |binError Q d j| ≤ 1/2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0 < 2*d)
    have heq := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d) + (2*d)*bin Q d j = 2*j*Q+d at heq
    nlinarith
  have h₁' : (bin Q d j:ℝ)*(2*d) ≤ 2*j*Q+d := by exact_mod_cast h₁
  have h₂' : (2:ℝ)*j*Q+d < ((bin Q d j:ℝ)+1)*(2*d) := by exact_mod_cast h₂
  have heq : binError Q d j*(d:ℝ) = (bin Q d j:ℝ)*d-(j:ℝ)*Q := by
    rw [binError, sub_mul, div_mul_cancel₀ _ hd'.ne']
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith

end ExactQuantumFactoring.OrderTrial



/-! Dependencies for the actual prescribed-probability order trial.
The phase below is proved to be exactly the quarter-linear interpolant in
sections/03-order-transform.tex. No oracle/order information is input. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators
open MeasureTheory intervalIntegral

/-- Real triangular wave, period one; quotient norm makes continuity explicit. -/
noncomputable def triangle (x : ℝ) : ℝ := 1 - 4 * ‖(x : UnitAddCircle)‖

lemma triangle_local {x : ℝ} (h : |x| ≤ 1/2) : triangle x = 1 - 4 * |x| := by
  unfold triangle
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using h)]

lemma triangle_add_int (x : ℝ) (k : ℤ) : triangle (x + k) = triangle x := by
  simp only [triangle, UnitAddCircle.norm_eq, round_add_intCast, Int.cast_add]
  congr 2
  ring_nf

lemma triangle_half (x : ℝ) : triangle (x + 1/2) = -triangle x := by
  let y : ℝ := x - round x
  have hy : |y| ≤ 1/2 := abs_sub_round x
  have hx : x = y + round x := by dsimp [y]; ring
  rw [hx]
  rw [show y + (round x : ℝ) + 1/2 = (y+1/2) + round x by ring,
    triangle_add_int, triangle_add_int]
  rcases le_total y 0 with hneg | hpos
  · have hy' : |y + 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [triangle_local hy, triangle_local hy', abs_of_nonpos hneg,
      abs_of_nonneg (by have := (abs_le.mp hy).1; linarith : 0 ≤ y+1/2)]
    ring
  · have hy' : |y - 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [show y+1/2 = (y-1/2) + (1 : ℤ) by norm_num; ring,
      triangle_add_int, triangle_local hy, triangle_local hy', abs_of_nonneg hpos,
      abs_of_nonpos (by have := (abs_le.mp hy).2; linarith : y-1/2 ≤ 0)]
    ring

lemma triangle_continuous : Continuous triangle := by
  exact continuous_const.sub (continuous_const.mul
    (AddCircle.continuous_mk' (1 : ℝ)).norm)

/-- Exact polygon phase, with clockwise orientation as in the forward shift. -/
noncomputable def phase (x : ℝ) : ℂ := ⟨triangle x, -triangle (x - 1/4)⟩

lemma phase_continuous : Continuous phase := by
  have h := (Complex.continuous_ofReal.comp triangle_continuous).sub
    ((Complex.continuous_ofReal.comp
      (triangle_continuous.comp (continuous_id.sub (continuous_const (y := (1/4 : ℝ)))))).mul
      (continuous_const (y := Complex.I)))
  convert h using 1
  funext x
  apply Complex.ext <;> simp [phase]

lemma phase_quarter (x : ℝ) : phase (x + 1/4) = -Complex.I * phase x := by
  have h := triangle_half (x - 1/4)
  rw [show x-1/4+1/2 = x+1/4 by ring] at h
  apply Complex.ext
  · simpa only [phase, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] using h
  · simp only [phase, neg_mul, Complex.neg_im, Complex.I_mul_im]
    congr 2
    ring

lemma phase_add_int (x : ℝ) (k : ℤ) : phase (x + k) = phase x := by
  apply Complex.ext
  · exact triangle_add_int _ _
  · change -triangle (x + k - 1/4) = -triangle (x-1/4)
    rw [show x + k - 1/4 = (x-1/4)+k by ring, triangle_add_int]

lemma phase_zero_quarter {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (t/4) = (1-t : ℂ) + (t : ℂ) * (-Complex.I) := by
  have ha : |t/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  have hb : |t/4-1/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  apply Complex.ext
  · change triangle (t/4) = _
    rw [triangle_local ha, abs_of_nonneg (by positivity : 0 ≤ t/4)]
    simp
    ring
  · change -triangle (t/4-1/4) = _
    rw [triangle_local hb, abs_of_nonpos (by linarith : t/4-1/4 ≤ 0)]
    simp
    ring

lemma triangle_quadratic_lower (x : ℝ) : 1/2 - 8*x^2 ≤ triangle x := by
  have hn : ‖(x : UnitAddCircle)‖ ≤ |x| := by
    rw [UnitAddCircle.norm_eq]
    simpa using round_le x 0
  have hs := sq_nonneg (|x| - 1/4)
  rw [triangle]
  nlinarith [sq_abs x]

lemma phase_add_quarters (x : ℝ) (q : ℤ) :
    phase (x + (q : ℝ)/4) = (-Complex.I)^q * phase x := by
  have hi : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  induction q using Int.induction_on with
  | zero => simp
  | succ q ih =>
      simp only [Int.cast_natCast] at ih
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one,
        show x + ((q : ℝ) + 1)/4 = (x + (q : ℝ)/4) + 1/4 by ring,
        phase_quarter, ih, zpow_add₀ hi]
      simp only [zpow_one]
      ring
  | pred q ih =>
      have h := phase_quarter (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4)
      rw [show x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4 + 1/4 =
          x + ((-(q : ℤ) : ℤ) : ℝ)/4 by push_cast; ring, ih] at h
      calc
        phase (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4) =
            (-Complex.I)⁻¹ * ((-Complex.I)^(-(q : ℤ)) * phase x) := by
          rw [h, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]
        _ = (-Complex.I)^(-(q : ℤ)-1) * phase x := by
          rw [show -(q : ℤ)-1 = -(q : ℤ)+(-1) by ring,
            zpow_add₀ hi, zpow_neg_one]
          ring

lemma phase_interpolates (q : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (((q : ℝ)+t)/4) = (1-t : ℂ)*(-Complex.I)^q +
      (t : ℂ)*(-Complex.I)^(q+1) := by
  rw [show ((q : ℝ)+t)/4 = t/4 + (q : ℝ)/4 by ring,
    phase_add_quarters, phase_zero_quarter ht0 ht1,
    zpow_add₀ (neg_ne_zero.mpr Complex.I_ne_zero)]
  simp only [zpow_one]
  ring

lemma phase_norm_le (x : ℝ) : ‖phase x‖ ≤ 1 := by
  let q : ℤ := ⌊4*x⌋
  let t : ℝ := 4*x-q
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le _)
  have ht1 : t ≤ 1 := by
    have h := Int.lt_floor_add_one (4*x)
    change 4*x - (⌊4*x⌋ : ℝ) ≤ 1
    linarith
  have hx : x = ((q : ℝ)+t)/4 := by dsimp [t]; ring
  rw [hx, phase_interpolates q ht0 ht1]
  calc
    _ ≤ ‖(1-t : ℂ)*(-Complex.I)^q‖ + ‖(t : ℂ)*(-Complex.I)^(q+1)‖ := norm_add_le _ _
    _ = 1 := by
      simp only [norm_mul, norm_zpow, norm_neg, Complex.norm_I, one_zpow, mul_one,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
      ring

lemma triangle_sub_le (x y : ℝ) : |triangle x - triangle y| ≤ 4*|x-y| := by
  have h₁ := abs_norm_sub_norm_le (x : UnitAddCircle) (y : UnitAddCircle)
  have h₂ : ‖(x : UnitAddCircle) - (y : UnitAddCircle)‖ ≤ |x-y| := by
    rw [← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq]
    simpa using round_le (x-y) 0
  have heq : triangle x - triangle y =
      -4 * (‖(x : UnitAddCircle)‖ - ‖(y : UnitAddCircle)‖) := by
    unfold triangle
    ring
  rw [heq, abs_mul]
  norm_num
  linarith

lemma phase_norm_sub_le (x y : ℝ) : ‖phase x-phase y‖ ≤ 8*|x-y| := by
  have h := Complex.norm_le_abs_re_add_abs_im (phase x-phase y)
  simp only [phase, Complex.sub_re, Complex.sub_im] at h
  rw [show -triangle (x-1/4) - -triangle (y-1/4) =
    -(triangle (x-1/4)-triangle (y-1/4)) by ring, abs_neg] at h
  have h₁ := triangle_sub_le x y
  have h₂ := triangle_sub_le (x-1/4) (y-1/4)
  rw [show (x-1/4)-(y-1/4) = x-y by ring] at h₂
  unfold phase
  linarith

lemma phase_lipschitz : LipschitzWith 8 phase := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using phase_norm_sub_le x y

lemma segment_phase_sub_le (a : ℝ) {η : ℝ} (hη : |η| ≤ 1/2) (v w : ℝ) :
    ‖phase (a+η*v)-phase (a+η*w)‖ ≤ 4*|v-w| := by
  have h := phase_norm_sub_le (a+η*v) (a+η*w)
  rw [show (a+η*v)-(a+η*w) = η*(v-w) by ring, abs_mul] at h
  nlinarith [abs_nonneg (v-w)]

lemma centered_quadratic_integral (c η : ℝ) :
    (∫ v in (0 : ℝ)..1, (1/2 - 8*(c+η*(v-1/2))^2)) =
      1/2 - 8*c^2 - (2/3)*η^2 := by
  have heq : (fun v : ℝ => 1/2 - 8*(c+η*(v-1/2))^2) =
      (fun v => (1/2-8*c^2+8*c*η-2*η^2) +
        (-16*c*η+8*η^2)*v + (-8*η^2)*v^2) := by
    funext v; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma centered_integral_re_lower {c η : ℝ} (hc : |c| ≤ 1/8) (hη : |η| ≤ 1/2) :
    5/24 ≤ (∫ v in (0 : ℝ)..1, phase (c+η*(v-1/2))).re := by
  have hf : Continuous (fun v : ℝ => phase (c+η*(v-1/2))) :=
    phase_continuous.comp (by fun_prop)
  have hq : Continuous (fun v : ℝ => 1/2-8*(c+η*(v-1/2))^2) := by fun_prop
  have h := integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hq.intervalIntegrable _ _) ((Complex.continuous_re.comp hf).intervalIntegrable _ _)
    (fun v _ => triangle_quadratic_lower (c+η*(v-1/2)))
  rw [centered_quadratic_integral] at h
  change 1/2-8*c^2-(2/3)*η^2 ≤
    ∫ v in (0:ℝ)..1, Complex.reCLM (phase (c+η*(v-1/2))) at h
  rw [Complex.reCLM.intervalIntegral_comp_comm (hf.intervalIntegrable _ _)] at h
  change 1/2-8*c^2-(2/3)*η^2 ≤
    (∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))).re at h
  have hc2 : c^2 ≤ (1/8 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg c) (by norm_num)).2 hc
  have hη2 : η^2 ≤ (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg η) (by norm_num)).2 hη
  nlinarith [sq_abs c, sq_abs η]

/-- The normalized interval average appearing in the dyadic majorant. -/
noncomputable def averagePhase (a η : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..1, phase (a+η*v)

lemma averagePhase_lower (a : ℝ) {η : ℝ} (hη : |η| ≤ 1/2) :
    (1/8 : ℝ) ≤ ‖averagePhase a η‖ := by
  let q : ℤ := round (4*(a+η/2))
  let c : ℝ := a+η/2-(q : ℝ)/4
  have hc : |c| ≤ 1/8 := by
    have h := abs_sub_round (4*(a+η/2))
    have hc4 : 4*c = 4*(a+η/2)-q := by dsimp [c]; ring
    rw [← hc4, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)] at h
    linarith
  have hf : (fun v : ℝ => phase (a+η*v)) =
      (fun v => (-Complex.I)^q * phase (c+η*(v-1/2))) := by
    funext v
    rw [← phase_add_quarters]
    congr 1
    dsimp [c]
    ring
  have hn : ‖averagePhase a η‖ = ‖∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))‖ := by
    unfold averagePhase
    rw [hf, intervalIntegral.integral_const_mul, norm_mul, norm_zpow]
    simp
  rw [hn]
  calc
    (1/8 : ℝ) ≤ 5/24 := by norm_num
    _ ≤ (∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))).re := centered_integral_re_lower hc hη
    _ ≤ _ := Complex.re_le_norm _

lemma averagePhase_upper (a η : ℝ) : ‖averagePhase a η‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun v _ => phase_norm_le (a+η*v))
  simpa only [averagePhase, sub_zero, abs_one, mul_one] using h

/-- `I(u)` in equation (majorant-integral), without a restriction on u needed
for its analytic bounds. -/
noncomputable def residueIntegral (d : ℕ) (u η : ℝ) : ℂ :=
  (d : ℂ)⁻¹ * averagePhase (u/d) η

lemma residueIntegral_bounds {d : ℕ} (hd : 0 < d) (u : ℝ) {η : ℝ}
    (hη : |η| ≤ 1/2) :
    1/(8*d : ℝ) ≤ ‖residueIntegral d u η‖ ∧ ‖residueIntegral d u η‖ ≤ 1/d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn : ‖residueIntegral d u η‖ = (d : ℝ)⁻¹ * ‖averagePhase (u/d) η‖ := by
    rw [residueIntegral, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hn]
  constructor
  · have h := mul_le_mul_of_nonneg_left (averagePhase_lower (u/d) hη)
      (inv_nonneg.mpr hd'.le)
    simpa only [one_div, mul_inv_rev] using h
  · simpa only [mul_one, one_div] using
      mul_le_mul_of_nonneg_left (averagePhase_upper (u/d) η) (inv_nonneg.mpr hd'.le)

/-- Quantitative rectangle rule with exactly the constant required in
(majorant-integral-bounds). -/
lemma rectangle_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖h • f a - ∫ v in a..a+h, f v‖ ≤ 2*h^2 := by
  have heq : (∫ v in a..a+h, (f a-f v)) = h • f a - ∫ v in a..a+h, f v := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_const]
    congr 1
    ring_nf
  rw [← heq]
  calc
    _ ≤ ∫ v in a..a+h, ‖f a-f v‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ v in a..a+h, 4*(v-a) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.sub hf).norm.intervalIntegrable _ _)
        ((show Continuous (fun v : ℝ => 4*(v-a)) by fun_prop).intervalIntegrable _ _)
      intro v hv
      have h₁ := hL a v
      rw [abs_of_nonpos (by linarith [hv.1] : a-v ≤ 0)] at h₁
      change ‖f a-f v‖ ≤ 4*(v-a)
      linarith
    _ = 2*h^2 := by
      rw [intervalIntegral.integral_const_mul]
      have hir : (∫ v in a..a+h, (v-a)) =
          (∫ v in a..a+h, v) - ∫ _ in a..a+h, a :=
        intervalIntegral.integral_sub (f := fun v : ℝ => v) (g := fun _ => a)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      rw [hir, integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

lemma rectangle_sum_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (M : ℕ) :
    ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v‖ ≤
      M*(2*h^2) := by
  have hInt₀ := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := volume) (a := fun i : ℕ => a+(i:ℝ)*h) (n := M)
    (fun i _ => hf.intervalIntegrable _ _)
  have hInt : (∑ i ∈ Finset.range M, ∫ v in (a+(i:ℝ)*h)..(a+((i:ℝ)+1)*h), f v) =
      ∫ v in a..a+M*h, f v := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using hInt₀
  rw [← hInt, Finset.smul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range M,
        ‖h • f (a+i*h) - ∫ v in (a+i*h)..(a+(i+1)*h), f v‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, (2*h^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hr := rectangle_error hf hL (a+(i:ℝ)*h) hh
      simpa only [show a+(i:ℝ)*h+h = a+((i:ℝ)+1)*h by ring] using hr
    _ = M*(2*h^2) := by simp

lemma integral_endpoint_error {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ v, ‖f v‖ ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb₁ : 1 ≤ b) :
    ‖(∫ v in a..b, f v) - ∫ v in (0:ℝ)..1, f v‖ ≤ a+(b-1) := by
  have heq : (∫ v in a..b, f v) - ∫ v in (0:ℝ)..1, f v =
      (∫ v in (1:ℝ)..b, f v) - ∫ v in (0:ℝ)..a, f v := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 1) (hf.intervalIntegrable 1 b)
    linear_combination h₁ - h₂
  rw [heq]
  have h₁ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1:ℝ)) (b := b) (fun v _ => hb v)
  have h₂ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := a) (fun v _ => hb v)
  rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hb₁)] at h₁
  rw [one_mul, sub_zero, abs_of_nonneg ha] at h₂
  calc
    _ ≤ ‖∫ v in (1:ℝ)..b, f v‖ + ‖∫ v in (0:ℝ)..a, f v‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma rectangle_sum_unit_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (hb : ∀ v, ‖f v‖ ≤ 1)
    {a h : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1) (ha₀ : 0 ≤ a) (ha₁ : a ≤ h)
    (M : ℕ) (hM₀ : 1 ≤ a+M*h) (hM₁ : a+M*h ≤ 1+h) :
    ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v‖ ≤ 6*h := by
  have h₁ := rectangle_sum_error hf hL a hh₀ M
  have h₂ := integral_endpoint_error hf hb ha₀ hM₀
  have hsplit : h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v =
      (h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v) +
      ((∫ v in a..a+M*h, f v) - ∫ v in (0:ℝ)..1, f v) := by abel
  rw [hsplit]
  calc
    _ ≤ ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v‖ +
      ‖(∫ v in a..a+M*h, f v) - ∫ v in (0:ℝ)..1, f v‖ := norm_add_le _ _
    _ ≤ M*(2*h^2) + a+(a+M*h-1) := by linarith
    _ ≤ 6*h := by
      have h₃ : (M:ℝ)*h ≤ 1+h := by linarith
      have h₄ := mul_le_mul_of_nonneg_right h₃ hh₀
      nlinarith [mul_nonneg hh₀ (sub_nonneg.mpr hh₁)]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderTrial.lean =====
namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open MeasureTheory intervalIntegral

lemma phase_bin_progression {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (j t i : ℕ) :
    phase ((bin Q d j : ℝ)*(t+i*d)/Q) =
      phase (((j*t)%d : ℕ)/ (d:ℝ) + binError Q d j*((t+i*d : ℕ):ℝ)/Q) := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr : (((j*t)%d : ℕ):ℝ) + (d:ℝ)*(((j*t)/d : ℕ):ℝ) = (j:ℝ)*t := by
    exact_mod_cast Nat.mod_add_div (j*t) d
  have hjt : (j:ℝ)*t/d = (((j*t)%d : ℕ):ℝ)/d + (((j*t)/d : ℕ):ℝ) := by
    rw [← hr, add_div, mul_div_cancel_left₀ _ hd']
  have heq : (bin Q d j : ℝ)*(t+i*d)/Q =
      (((j*t)%d : ℕ):ℝ)/d + binError Q d j*((t+i*d : ℕ):ℝ)/Q +
      (((j*t/d+j*i : ℕ):ℤ):ℝ) := by
    calc
      _ = (j:ℝ)*t/d+(j:ℝ)*i + binError Q d j*((t+i*d : ℕ):ℝ)/Q := by
        unfold binError
        push_cast
        field_simp
        ring
      _ = _ := by
        rw [hjt]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
        ring
  rw [heq, phase_add_int]

/-- Equation (order-P), before squaring the norm. -/
noncomputable def residueAmplitude (Q d j t : ℕ) : ℂ :=
  (Q:ℂ)⁻¹ * ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t),
    phase ((bin Q d j:ℝ)*x/Q)

noncomputable def residueProbability (Q d j t : ℕ) : ℝ :=
  ‖residueAmplitude Q d j t‖^2

lemma residueAmplitude_samples {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ∑ i ∈ Finset.range (sampleCount Q d t),
        phase (((j*t)%d : ℕ)/(d:ℝ) +
          binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q))) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  unfold residueAmplitude
  rw [← sum_progression (fun x => phase ((bin Q d j:ℝ)*x/Q)) hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_add, Nat.cast_mul, phase_bin_progression hQ hd]
  congr 1
  push_cast
  ring

lemma residueAmplitude_integral_error {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    ‖residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ ≤
      6/(Q:ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  let a : ℝ := t/Q
  let h : ℝ := d/Q
  let M := sampleCount Q d t
  let f : ℝ → ℂ := fun v => phase (((j*t)%d : ℕ)/(d:ℝ) + binError Q d j*v)
  have hh₀ : 0 ≤ h := div_nonneg hd'.le hQ'.le
  have hh₁ : h ≤ 1 := (div_le_one hQ').mpr (by exact_mod_cast hdQ)
  have ha₀ : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hQ'.le
  have ha₁ : a ≤ h := (div_le_div_iff_of_pos_right hQ').mpr (by exact_mod_cast ht.le)
  have he : a+(M:ℝ)*h = ((t+M*d : ℕ):ℝ)/Q := by dsimp [a,h]; push_cast; ring
  have hM := sampleCount_bounds hd hdQ ht
  have hM₀ : 1 ≤ a+(M:ℝ)*h := by
    rw [he]
    apply (one_le_div hQ').mpr
    exact_mod_cast hM.1
  have hM₁ : a+(M:ℝ)*h ≤ 1+h := by
    rw [he]
    have hsum : (1:ℝ)+h = ((Q+d : ℕ):ℝ)/Q := by dsimp [h]; push_cast; field_simp
    rw [hsum]
    apply (div_le_div_iff_of_pos_right hQ').mpr
    exact_mod_cast hM.2
  have hf : Continuous f := phase_continuous.comp (by fun_prop)
  have hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w| :=
    segment_phase_sub_le _ (binError_bound hd)
  have hb : ∀ v, ‖f v‖ ≤ 1 := fun v => phase_norm_le _
  have hr := rectangle_sum_unit_error hf hL hb hh₀ hh₁ ha₀ ha₁ M hM₀ hM₁
  have heq : residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j) =
      (d:ℂ)⁻¹ * (h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v) := by
    rw [residueAmplitude_samples hd hdQ ht]
    dsimp [residueIntegral, averagePhase, f, a, h, M]
    push_cast
    have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hQC : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d:ℝ)⁻¹*(6*h) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hd'.le)
    _ = 6/(Q:ℝ) := by dsimp [h]; field_simp

lemma residueAmplitude_norm_le {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    ‖residueAmplitude Q d j t‖ ≤ 1 := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  let s := (Finset.range Q).filter (fun x => x%d=t)
  have hc : (s.card:ℝ) ≤ Q := by exact_mod_cast (Finset.card_filter_le (s := Finset.range Q)
    (p := fun x => x%d=t) |>.trans_eq (Finset.card_range Q))
  rw [residueAmplitude, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Q:ℝ)⁻¹*∑ x ∈ s, ‖phase ((bin Q d j:ℝ)*x/Q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hQ'.le)
    _ ≤ (Q:ℝ)⁻¹*∑ _x ∈ s, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => phase_norm_le _))
        (inv_nonneg.mpr hQ'.le)
    _ ≤ (Q:ℝ)⁻¹*Q := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hQ'.le)
    _ = 1 := inv_mul_cancel₀ hQ'.ne'

lemma norm_square_difference_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖^2-‖w‖^2| ≤ 2*‖z-w‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h := abs_norm_sub_norm_le z w
  exact mul_le_mul (show ‖z‖+‖w‖ ≤ 2 by linarith) h (abs_nonneg _) (by norm_num)

/-- The key approximation (majorant-integral-bounds), for the exact source P. -/
lemma residueProbability_integral_error {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    |residueProbability Q d j t -
      ‖residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖^2| ≤ 32/(Q:ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hI := (residueIntegral_bounds hd (((j*t)%d : ℕ):ℝ) (binError_bound (Q := Q) (j := j) hd)).2
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hI₁ : ‖residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ ≤ 1 :=
    hI.trans ((div_le_one (lt_of_lt_of_le zero_lt_one hd')).mpr hd')
  have h := norm_square_difference_le (residueAmplitude_norm_le hQ d j t) hI₁
  have he := residueAmplitude_integral_error hd hdQ ht j
  unfold residueProbability
  calc
    _ ≤ 2*‖residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ := h
    _ ≤ 2*(6/(Q:ℝ)) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 32/(Q:ℝ) := by apply (le_div_iff₀ hQ').mpr; field_simp; norm_num

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Topology
open Set Filter

/-- A positive-part square. This supplies a globally C¹ rational spline primitive. -/
noncomputable def rampSq (x : ℝ) : ℝ := (max 0 x)^2

lemma rampSq_hasDerivAt (x : ℝ) : HasDerivAt rampSq (2*max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : rampSq =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [rampSq, max_eq_left hy.le]
    simpa only [max_eq_left hx.le, mul_zero] using!
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
  · have hl : HasDerivWithinAt rampSq 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr
      · intro y hy
        simp [rampSq, max_eq_left (show y ≤ 0 from hy)]
      · norm_num [rampSq]
    have hr : HasDerivWithinAt rampSq 0 (Ici 0) 0 := by
      have h : HasDerivAt (fun y : ℝ => y^2) 0 0 := by
        simpa using! (hasDerivAt_id (0:ℝ)).pow 2
      apply h.hasDerivWithinAt.congr
      · intro y hy
        simp only [rampSq, max_eq_right (show 0 ≤ y from hy)]
      · norm_num [rampSq]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, max_self, mul_zero] using hl.union hr
  · have he : rampSq =ᶠ[𝓝 x] fun y => y^2 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp only [rampSq, max_eq_right hy.le]
    simpa [max_eq_right hx.le] using!
      ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq he

lemma rampSq_continuous : Continuous rampSq := by
  unfold rampSq
  fun_prop

lemma rampSq_shift_hasDerivAt (x a : ℝ) :
    HasDerivAt (fun y => rampSq (y-a)) (2*max 0 (x-a)) x := by
  simpa only [mul_one] using!
    (rampSq_hasDerivAt (x-a)).comp x ((hasDerivAt_id x).sub_const a)

noncomputable def splineRe (x : ℝ) : ℝ :=
  -(x+1/2)+2*(x+1/2)^2-4*rampSq x+4*rampSq (x-1/2)-4*rampSq (x-1)

noncomputable def splineIm (x : ℝ) : ℝ :=
  2*(x+1/2)^2-4*rampSq (x+1/4)+4*rampSq (x-1/4)-
    4*rampSq (x-3/4)+4*rampSq (x-5/4)-1/4

noncomputable def splineReDeriv (x : ℝ) : ℝ :=
  -1+4*(x+1/2)-8*max 0 x+8*max 0 (x-1/2)-8*max 0 (x-1)

noncomputable def splineImDeriv (x : ℝ) : ℝ :=
  4*(x+1/2)-8*max 0 (x+1/4)+8*max 0 (x-1/4)-
    8*max 0 (x-3/4)+8*max 0 (x-5/4)

lemma splineRe_hasDerivAt (x : ℝ) : HasDerivAt splineRe (splineReDeriv x) x := by
  have h := (hasDerivAt_id x).add_const (1/2:ℝ)
  have h₀ := rampSq_hasDerivAt x
  have h₁ := rampSq_shift_hasDerivAt x (1/2)
  have h₂ := rampSq_shift_hasDerivAt x 1
  convert! ((((h.neg.add ((h.pow 2).const_mul 2)).sub (h₀.const_mul 4)).add
    (h₁.const_mul 4)).sub (h₂.const_mul 4)) using 1
  simp [splineReDeriv]
  ring

lemma splineIm_hasDerivAt (x : ℝ) : HasDerivAt splineIm (splineImDeriv x) x := by
  have h := (hasDerivAt_id x).add_const (1/2:ℝ)
  have h₀ : HasDerivAt (fun y => rampSq (y+1/4)) (2*max 0 (x+1/4)) x := by
    simpa only [mul_one] using!
      (rampSq_hasDerivAt (x+1/4)).comp x ((hasDerivAt_id x).add_const (1/4:ℝ))
  have h₁ := rampSq_shift_hasDerivAt x (1/4)
  have h₂ := rampSq_shift_hasDerivAt x (3/4)
  have h₃ := rampSq_shift_hasDerivAt x (5/4)
  convert! ((((((h.pow 2).const_mul 2).sub (h₀.const_mul 4)).add (h₁.const_mul 4)).sub
    (h₂.const_mul 4)).add (h₃.const_mul 4)).sub_const (1/4:ℝ) using 1
  simp [splineImDeriv]
  ring

noncomputable def spline (x : ℝ) : ℂ := (splineRe x : ℂ) + (splineIm x : ℂ)*Complex.I

lemma spline_hasDerivAt (x : ℝ) :
    HasDerivAt spline ((splineReDeriv x : ℂ)+(splineImDeriv x : ℂ)*Complex.I) x :=
  (splineRe_hasDerivAt x).ofReal_comp.add ((splineIm_hasDerivAt x).ofReal_comp.mul_const _)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open MeasureTheory intervalIntegral

lemma splineReDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineReDeriv x = triangle x := by
  unfold splineReDeriv
  by_cases h₀ : x ≤ 0
  · rw [max_eq_left h₀, max_eq_left (by linarith : x-1/2 ≤ 0),
      max_eq_left (by linarith : x-1 ≤ 0), triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonpos h₀]
    ring
  · have h₀' := le_of_not_ge h₀
    rw [max_eq_right h₀']
    by_cases h₁ : x ≤ 1/2
    · rw [max_eq_left (by linarith : x-1/2 ≤ 0), max_eq_left (by linarith : x-1 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith), abs_of_nonneg h₀']
      ring
    · have ht : triangle x = triangle (x-1) := by
        convert triangle_add_int (x-1) 1 using 1
        norm_num
      rw [ht, triangle_local (by rw [abs_le]; constructor <;> linarith),
        max_eq_right (by linarith : 0 ≤ x-1/2)]
      by_cases h₂ : x ≤ 1
      · rw [max_eq_left (by linarith : x-1 ≤ 0), abs_of_nonpos (by linarith : x-1 ≤ 0)]
        ring
      · rw [max_eq_right (by linarith : 0 ≤ x-1), abs_of_nonneg (by linarith : 0 ≤ x-1)]
        ring

lemma splineImDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineImDeriv x = -triangle (x-1/4) := by
  unfold splineImDeriv
  by_cases h₀ : x ≤ -(1/4)
  · have ht : triangle (x-1/4) = triangle (x+3/4) := by
      symm
      convert triangle_add_int (x-1/4) 1 using 1
      norm_num
      congr 1
      ring
    rw [max_eq_left (by linarith : x+1/4 ≤ 0),
      max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
      max_eq_left (by linarith : x-5/4 ≤ 0), ht,
      triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonneg (by linarith : 0 ≤ x+3/4)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x+1/4)]
    by_cases h₁ : x ≤ 1/4
    · rw [max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
        max_eq_left (by linarith : x-5/4 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith),
        abs_of_nonpos (by linarith : x-1/4 ≤ 0)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ x-1/4)]
      by_cases h₂ : x ≤ 3/4
      · rw [max_eq_left (by linarith : x-3/4 ≤ 0), max_eq_left (by linarith : x-5/4 ≤ 0),
          triangle_local (by rw [abs_le]; constructor <;> linarith),
          abs_of_nonneg (by linarith : 0 ≤ x-1/4)]
        ring
      · have ht : triangle (x-1/4) = triangle (x-5/4) := by
          convert triangle_add_int (x-5/4) 1 using 1
          norm_num
          congr 1
          ring
        rw [max_eq_right (by linarith : 0 ≤ x-3/4), ht,
          triangle_local (by rw [abs_le]; constructor <;> linarith)]
        by_cases h₃ : x ≤ 5/4
        · rw [max_eq_left (by linarith : x-5/4 ≤ 0), abs_of_nonpos (by linarith : x-5/4 ≤ 0)]
          ring
        · rw [max_eq_right (by linarith : 0 ≤ x-5/4), abs_of_nonneg (by linarith : 0 ≤ x-5/4)]
          ring

lemma spline_derivative {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    HasDerivAt spline (phase x) x := by
  have h := spline_hasDerivAt x
  rw [splineReDeriv_eq hx₀ hx₁, splineImDeriv_eq hx₀ hx₁] at h
  convert! h using 1
  apply Complex.ext <;> simp [phase]

lemma spline_zero : spline 0 = 0 := by
  norm_num [spline, splineRe, splineIm, rampSq]

lemma spline_integral {a b : ℝ} (ha₀ : -(1/2) ≤ a) (ha₁ : a ≤ 3/2)
    (hb₀ : -(1/2) ≤ b) (hb₁ : b ≤ 3/2) :
    (∫ v in a..b, phase v) = spline b-spline a := by
  apply integral_eq_sub_of_hasDerivAt _ (phase_continuous.intervalIntegrable _ _)
  intro x hx
  obtain ⟨hl,hu⟩ := hx
  apply spline_derivative
  · exact (le_min ha₀ hb₀).trans hl
  · exact hu.trans (max_le ha₁ hb₁)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

/-- Rational polynomial on a quarter interval; no real oracle is used in its data. -/
noncomputable def rampPiece (q a : ℤ) : ℚ[X] :=
  if a ≤ q then (X-C ((a:ℚ)/4))^2 else 0

noncomputable def evalReal (p : ℚ[X]) (x : ℝ) : ℝ := p.eval₂ (Rat.castHom ℝ) x

lemma evalReal_rampPiece (q a : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) :
    evalReal (rampPiece q a) x = rampSq (x-(a:ℝ)/4) := by
  by_cases h : a ≤ q
  · have h' : (a:ℝ) ≤ q := by exact_mod_cast h
    have hx : 0 ≤ x-(a:ℝ)/4 := by linarith
    simp only [rampPiece, ite_eq_left h, evalReal, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, rampSq, max_eq_right hx]
    norm_num
  · have h' : (q:ℝ)+1 ≤ a := by exact_mod_cast (show q+1 ≤ a by omega)
    have hx : x-(a:ℝ)/4 ≤ 0 := by linarith
    simp [rampPiece, h, evalReal, rampSq, max_eq_left hx]

noncomputable def splineRePiece (q : ℤ) : ℚ[X] :=
  -(X+C (1/2))+ C 2*(X+C (1/2))^2 - C 4*rampPiece q 0 +
    C 4*rampPiece q 2 - C 4*rampPiece q 4

noncomputable def splineImPiece (q : ℤ) : ℚ[X] :=
  C 2*(X+C (1/2))^2-C 4*rampPiece q (-1)+C 4*rampPiece q 1-
    C 4*rampPiece q 3+C 4*rampPiece q 5-C (1/4)

lemma evalReal_splineRePiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (splineRePiece q) x = splineRe x := by
  have h0 := evalReal_rampPiece q 0 h₀ h₁
  have h2 := evalReal_rampPiece q 2 h₀ h₁
  have h4 := evalReal_rampPiece q 4 h₀ h₁
  simp only [evalReal, splineRePiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change -(x+(1/2:ℚ))+ (2:ℚ)*(x+(1/2:ℚ))^2 - (4:ℚ)*evalReal (rampPiece q 0) x +
    (4:ℚ)*evalReal (rampPiece q 2) x - (4:ℚ)*evalReal (rampPiece q 4) x = splineRe x
  rw [h0,h2,h4]
  norm_num [splineRe]

lemma evalReal_splineImPiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (splineImPiece q) x = splineIm x := by
  have hm1 := evalReal_rampPiece q (-1) h₀ h₁
  have h1 := evalReal_rampPiece q 1 h₀ h₁
  have h3 := evalReal_rampPiece q 3 h₀ h₁
  have h5 := evalReal_rampPiece q 5 h₀ h₁
  simp only [evalReal, splineImPiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  change (2:ℚ)*(x+(1/2:ℚ))^2 - (4:ℚ)*evalReal (rampPiece q (-1)) x +
    (4:ℚ)*evalReal (rampPiece q 1) x - (4:ℚ)*evalReal (rampPiece q 3) x +
    (4:ℚ)*evalReal (rampPiece q 5) x - (1/4:ℚ) = splineIm x
  rw [hm1,h1,h3,h5]
  norm_num [splineIm]

lemma poly_add_degree {p q : ℚ[X]} {k : ℕ} (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) :
    (p+q).natDegree ≤ k := (natDegree_add_le _ _).trans (max_le hp hq)

lemma poly_sub_degree {p q : ℚ[X]} {k : ℕ} (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) :
    (p-q).natDegree ≤ k := (natDegree_sub_le _ _).trans (max_le hp hq)

lemma rampPiece_natDegree_le (q a : ℤ) : (rampPiece q a).natDegree ≤ 2 := by
  unfold rampPiece
  split_ifs
  · apply le_trans (Polynomial.natDegree_pow_le)
    have h : (X-C ((a:ℚ)/4)).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _) (by simp)
    omega
  · simp

lemma splineRePiece_natDegree_le (q : ℤ) : (splineRePiece q).natDegree ≤ 2 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  have hSq : ((X+C (1/2:ℚ))^2).natDegree ≤ 2 :=
    (Polynomial.natDegree_pow_le).trans (by omega)
  unfold splineRePiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · simpa only [natDegree_neg] using (hX.trans (by norm_num : 1 ≤ 2))
        · exact (natDegree_C_mul_le _ _).trans hSq
      · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)

lemma splineImPiece_natDegree_le (q : ℤ) : (splineImPiece q).natDegree ≤ 2 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  have hSq : ((X+C (1/2:ℚ))^2).natDegree ≤ 2 :=
    (Polynomial.natDegree_pow_le).trans (by omega)
  unfold splineImPiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · apply poly_sub_degree
          · exact (natDegree_C_mul_le _ _).trans hSq
          · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
        · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
      · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
  · simp

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderTrialFurther.lean =====
namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

lemma residueIntegral_eq_primitive {d : ℕ} (hd : 0 < d) {u η : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ d) (hη : |η| ≤ 1/2) (hη₀ : η ≠ 0) :
    residueIntegral d u η = (d:ℂ)⁻¹*(η:ℂ)⁻¹*(spline (u/d+η)-spline (u/d)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha₀ : 0 ≤ u/d := div_nonneg hu₀ hd'.le
  have ha₁ : u/d ≤ 1 := (div_le_one hd').mpr hu₁
  obtain ⟨hηl,hηu⟩ := abs_le.mp hη
  unfold residueIntegral averagePhase
  rw [integral_comp_add_mul phase hη₀, mul_zero, add_zero, mul_one,
    spline_integral (by linarith) (by linarith) (by linarith) (by linarith),
    Complex.real_smul, Complex.ofReal_inv, mul_assoc]

lemma residueIntegral_zero (d : ℕ) (u : ℝ) :
    residueIntegral d u 0 = (d:ℂ)⁻¹*phase (u/d) := by
  simp [residueIntegral, averagePhase]

noncomputable def rampLinear (q a : ℤ) : ℚ[X] := if a ≤ q then X-C ((a:ℚ)/4) else 0

lemma evalReal_rampLinear (q a : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) :
    evalReal (rampLinear q a) x = max 0 (x-(a:ℝ)/4) := by
  by_cases h : a ≤ q
  · have h' : (a:ℝ) ≤ q := by exact_mod_cast h
    have hx : 0 ≤ x-(a:ℝ)/4 := by linarith
    simp only [rampLinear, ite_eq_left h, evalReal, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, max_eq_right hx]
    norm_num
  · have h' : (q:ℝ)+1 ≤ a := by exact_mod_cast (show q+1 ≤ a by omega)
    have hx : x-(a:ℝ)/4 ≤ 0 := by linarith
    simp [rampLinear, h, evalReal, max_eq_left hx]

noncomputable def phaseRePiece (q : ℤ) : ℚ[X] :=
  -1+C 4*(X+C (1/2))-C 8*rampLinear q 0+C 8*rampLinear q 2-C 8*rampLinear q 4
noncomputable def phaseImPiece (q : ℤ) : ℚ[X] :=
  C 4*(X+C (1/2))-C 8*rampLinear q (-1)+C 8*rampLinear q 1-
    C 8*rampLinear q 3+C 8*rampLinear q 5

lemma evalReal_phaseRePiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (phaseRePiece q) x = splineReDeriv x := by
  have h0 := evalReal_rampLinear q 0 h₀ h₁
  have h2 := evalReal_rampLinear q 2 h₀ h₁
  have h4 := evalReal_rampLinear q 4 h₀ h₁
  simp only [evalReal, phaseRePiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change -1 + (4:ℚ)*(x+(1/2:ℚ)) - (8:ℚ)*evalReal (rampLinear q 0) x +
    (8:ℚ)*evalReal (rampLinear q 2) x - (8:ℚ)*evalReal (rampLinear q 4) x = splineReDeriv x
  rw [h0,h2,h4]
  norm_num [splineReDeriv]

lemma evalReal_phaseImPiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (phaseImPiece q) x = splineImDeriv x := by
  have hm1 := evalReal_rampLinear q (-1) h₀ h₁
  have h1 := evalReal_rampLinear q 1 h₀ h₁
  have h3 := evalReal_rampLinear q 3 h₀ h₁
  have h5 := evalReal_rampLinear q 5 h₀ h₁
  simp only [evalReal, phaseImPiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change (4:ℚ)*(x+(1/2:ℚ)) - (8:ℚ)*evalReal (rampLinear q (-1)) x +
    (8:ℚ)*evalReal (rampLinear q 1) x - (8:ℚ)*evalReal (rampLinear q 3) x +
    (8:ℚ)*evalReal (rampLinear q 5) x = splineImDeriv x
  rw [hm1,h1,h3,h5]
  norm_num [splineImDeriv]

lemma rampLinear_natDegree_le (q a : ℤ) : (rampLinear q a).natDegree ≤ 1 := by
  unfold rampLinear
  split_ifs
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp

lemma phaseRePiece_natDegree_le (q : ℤ) : (phaseRePiece q).natDegree ≤ 1 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  unfold phaseRePiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · simp
        · exact (natDegree_C_mul_le _ _).trans hX
      · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)

lemma phaseImPiece_natDegree_le (q : ℤ) : (phaseImPiece q).natDegree ≤ 1 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  unfold phaseImPiece
  apply poly_add_degree
  · apply poly_sub_degree
    · apply poly_add_degree
      · apply poly_sub_degree
        · exact (natDegree_C_mul_le _ _).trans hX
        · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
      · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial

@[simp] lemma evalReal_add (p q : ℚ[X]) (x : ℝ) : evalReal (p+q) x = evalReal p x+evalReal q x :=
  Polynomial.eval₂_add _ _
@[simp] lemma evalReal_sub (p q : ℚ[X]) (x : ℝ) : evalReal (p-q) x = evalReal p x-evalReal q x :=
  Polynomial.eval₂_sub _
@[simp] lemma evalReal_mul (p q : ℚ[X]) (x : ℝ) : evalReal (p*q) x = evalReal p x*evalReal q x :=
  Polynomial.eval₂_mul _ _
@[simp] lemma evalReal_pow (p : ℚ[X]) (k : ℕ) (x : ℝ) : evalReal (p^k) x = (evalReal p x)^k :=
  Polynomial.eval₂_pow _ _ _
@[simp] lemma evalReal_C (a : ℚ) (x : ℝ) : evalReal (C a) x = (a:ℝ) :=
  Polynomial.eval₂_C _ _
@[simp] lemma evalReal_X (x : ℝ) : evalReal (X:ℚ[X]) x = x := Polynomial.eval₂_X _ _
@[simp] lemma evalReal_comp (p q : ℚ[X]) (x : ℝ) :
    evalReal (p.comp q) x = evalReal p (evalReal q x) := Polynomial.eval₂_comp _

noncomputable def linearArg (d : ℕ) (η : ℚ) : ℚ[X] := C ((d:ℚ)⁻¹)*X+C η

@[simp] lemma evalReal_linearArg (d : ℕ) (η : ℚ) (x : ℝ) :
    evalReal (linearArg d η) x = x/d + (η:ℝ) := by
  simp only [linearArg, evalReal_add, evalReal_mul, evalReal_C, evalReal_X,
    Rat.cast_inv, Rat.cast_natCast]
  ring

lemma linearArg_natDegree_le (d : ℕ) (η : ℚ) : (linearArg d η).natDegree ≤ 1 := by
  apply poly_add_degree
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp

/-- The exact integral-coordinate polynomial, with the zero slope handled without division. -/
noncomputable def integralPiece (d : ℕ) (η : ℚ) (A G₀ G₁ : ℚ[X]) : ℚ[X] :=
  if η=0 then C ((d:ℚ)⁻¹)*A.comp (linearArg d 0)
  else C (((d:ℚ)*η)⁻¹)*(G₁.comp (linearArg d η)-G₀.comp (linearArg d 0))

lemma integralPiece_natDegree_le (d : ℕ) (η : ℚ) {A G₀ G₁ : ℚ[X]}
    (hA : A.natDegree ≤ 1) (h₀ : G₀.natDegree ≤ 2) (h₁ : G₁.natDegree ≤ 2) :
    (integralPiece d η A G₀ G₁).natDegree ≤ 2 := by
  unfold integralPiece
  split_ifs
  · apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_comp]
    exact (Nat.mul_le_mul hA (linearArg_natDegree_le _ _)).trans (by norm_num)
  · apply (natDegree_C_mul_le _ _).trans
    apply poly_sub_degree
    · rw [natDegree_comp]
      simpa using Nat.mul_le_mul h₁ (linearArg_natDegree_le d η)
    · rw [natDegree_comp]
      simpa using Nat.mul_le_mul h₀ (linearArg_natDegree_le d 0)

lemma evalReal_integralPiece (d : ℕ) (η : ℚ) (A G₀ G₁ : ℚ[X]) (x : ℝ) :
    evalReal (integralPiece d η A G₀ G₁) x =
      if η=0 then (d:ℝ)⁻¹*evalReal A (x/d)
      else ((d:ℝ)*(η:ℝ))⁻¹*(evalReal G₁ (x/d+η)-evalReal G₀ (x/d)) := by
  unfold integralPiece
  split_ifs <;> simp

noncomputable def massPiece (d : ℕ) (η : ℚ) (q₀ q₁ : ℤ) : ℚ[X] :=
  (integralPiece d η (phaseRePiece q₀) (splineRePiece q₀) (splineRePiece q₁))^2+
    (integralPiece d η (phaseImPiece q₀) (splineImPiece q₀) (splineImPiece q₁))^2

lemma massPiece_natDegree_le (d : ℕ) (η : ℚ) (q₀ q₁ : ℤ) :
    (massPiece d η q₀ q₁).natDegree ≤ 4 := by
  apply poly_add_degree
  · apply natDegree_pow_le.trans
    have h := integralPiece_natDegree_le d η (phaseRePiece_natDegree_le q₀)
      (splineRePiece_natDegree_le q₀) (splineRePiece_natDegree_le q₁)
    omega
  · apply natDegree_pow_le.trans
    have h := integralPiece_natDegree_le d η (phaseImPiece_natDegree_le q₀)
      (splineImPiece_natDegree_le q₀) (splineImPiece_natDegree_le q₁)
    omega

lemma massPiece_eq {d : ℕ} (hd : 0 < d) (η : ℚ) {u : ℝ} (hu₀ : 0 ≤ u)
    (hu₁ : u ≤ d) (hη : |(η:ℝ)| ≤ 1/2) (q₀ q₁ : ℤ)
    (hq₀l : (q₀:ℝ)/4 ≤ u/d) (hq₀u : u/d ≤ ((q₀:ℝ)+1)/4)
    (hq₁l : (q₁:ℝ)/4 ≤ u/d+η) (hq₁u : u/d+η ≤ ((q₁:ℝ)+1)/4) :
    evalReal (massPiece d η q₀ q₁) u = ‖residueIntegral d u η‖^2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha₀ : 0 ≤ u/d := div_nonneg hu₀ hd'.le
  have ha₁ : u/d ≤ 1 := (div_le_one hd').mpr hu₁
  simp only [massPiece, evalReal_add, evalReal_pow, evalReal_integralPiece]
  by_cases h : η=0
  · simp only [h, ite_true, Rat.cast_zero, residueIntegral_zero]
    rw [evalReal_phaseRePiece q₀ hq₀l hq₀u, evalReal_phaseImPiece q₀ hq₀l hq₀u,
      splineReDeriv_eq (by linarith) (by linarith),
      splineImDeriv_eq (by linarith) (by linarith), Complex.sq_norm]
    rw [show (d:ℂ)⁻¹ = (((d:ℝ)⁻¹:ℝ):ℂ) by simp]
    simp [phase, Complex.normSq_apply]
    ring
  · simp only [h, ite_false]
    rw [evalReal_splineRePiece q₀ hq₀l hq₀u, evalReal_splineImPiece q₀ hq₀l hq₀u,
      evalReal_splineRePiece q₁ hq₁l hq₁u, evalReal_splineImPiece q₁ hq₁l hq₁u,
      residueIntegral_eq_primitive hd hu₀ hu₁ hη (by exact_mod_cast h), Complex.sq_norm]
    rw [show (d:ℂ)⁻¹ = (((d:ℝ)⁻¹:ℝ):ℂ) by simp,
      show ((η:ℝ):ℂ)⁻¹ = (((η:ℝ)⁻¹:ℝ):ℂ) by simp]
    simp [spline, Complex.normSq_apply, mul_inv_rev]
    ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Upward coefficient rounding by a specified integer denominator. -/
def roundCoeff (D : ℕ) (a : ℚ) : ℚ := (⌈(D:ℚ)*a⌉:ℤ)/(D:ℚ)

lemma roundCoeff_error {D : ℕ} (hD : 0 < D) (a : ℚ) :
    0 ≤ roundCoeff D a-a ∧ roundCoeff D a-a ≤ 1/(D:ℚ) := by
  have hD' : (0:ℚ) < D := Nat.cast_pos.mpr hD
  have hl := Int.le_ceil ((D:ℚ)*a)
  have hu := Int.ceil_lt_add_one ((D:ℚ)*a)
  unfold roundCoeff
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hD').mpr
    linarith
  · rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hD').mpr
    rw [add_mul, div_mul_cancel₀ _ hD'.ne']
    linarith

lemma roundCoeff_error_real {D : ℕ} (hD : 0 < D) (a : ℚ) :
    0 ≤ (roundCoeff D a:ℝ)-(a:ℝ) ∧ (roundCoeff D a:ℝ)-(a:ℝ) ≤ 1/(D:ℝ) := by
  rcases roundCoeff_error hD a with ⟨hl, hu⟩
  constructor
  · have h : (0:ℝ) ≤ ((roundCoeff D a-a:ℚ):ℝ) := Rat.cast_nonneg.mpr hl
    simpa using h
  · have h : ((roundCoeff D a-a:ℚ):ℝ) ≤ ((1/(D:ℚ):ℚ):ℝ) := Rat.cast_le.mpr hu
    simpa using h

noncomputable def roundedValue (D : ℕ) (p : ℚ[X]) (u : ℚ) : ℚ :=
  ∑ q ∈ Finset.range 5, roundCoeff D (p.coeff q)*u^q

lemma roundedValue_error {D : ℕ} (hD : 0 < D) (p : ℚ[X])
    (hp : p.natDegree ≤ 4) {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ∧
      (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ≤
        (∑ q ∈ Finset.range 5, (u:ℝ)^q)/(D:ℝ) := by
  have hu' : (0:ℝ) ≤ u := by exact_mod_cast hu
  have he : (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) =
      ∑ q ∈ Finset.range 5, ((roundCoeff D (p.coeff q):ℝ)-(p.coeff q:ℝ))*(u:ℝ)^q := by
    rw [Polynomial.eval₂_eq_sum_range' _ (by omega : p.natDegree < 5)]
    simp only [roundedValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
      sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun q _ => mul_nonneg (roundCoeff_error_real hD _).1 (pow_nonneg hu' _))
  · calc
      _ ≤ ∑ q ∈ Finset.range 5, (1/(D:ℝ))*(u:ℝ)^q :=
        Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right
          (roundCoeff_error_real hD _).2 (pow_nonneg hu' _))
      _ = _ := by rw [← Finset.mul_sum]; ring

lemma five_powers_bound {u B : ℝ} (hB : 2 ≤ B) (hu₀ : 0 ≤ u) (huB : u ≤ B) :
    (∑ q ∈ Finset.range 5, u^q) ≤ B^8 := by
  have hB1 : 1 ≤ B := by linarith
  have hs : (∑ q ∈ Finset.range 5, u^q) ≤ 5*B^4 := by
    calc
      _ ≤ ∑ _q ∈ Finset.range 5, B^4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (pow_le_pow_left₀ hu₀ huB q).trans
          (pow_le_pow_right₀ hB1 (by simp only [Finset.mem_range] at hq; omega))
      _ = _ := by simp
  have hB4 : 16 ≤ B^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hB 4
    norm_num at h
    exact h
  have h48 : B^8 = (B^4)^2 := by ring
  rw [h48]
  nlinarith

lemma roundedValue_small_error {Q B : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (p : ℚ[X]) (hp : p.natDegree ≤ 4) {u : ℕ} (hu : u ≤ B) :
    0 ≤ (roundedValue (Q*B^8) p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ∧
      (roundedValue (Q*B^8) p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ≤ 1/(Q:ℝ) := by
  have hB₀ : 0 < B := by omega
  have hD := Nat.mul_pos hQ (pow_pos hB₀ 8)
  have h := roundedValue_error hD p hp (Nat.cast_nonneg u)
  simp only [Rat.cast_natCast] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB₀
  have hg := five_powers_bound (by exact_mod_cast hB : (2:ℝ) ≤ B)
    (Nat.cast_nonneg u) (by exact_mod_cast hu)
  calc
    _ ≤ (B:ℝ)^8/(Q*B^8) := by
      push_cast
      exact div_le_div_of_nonneg_right hg (mul_nonneg hQ'.le (pow_nonneg hB'.le _))
    _ = 1/(Q:ℝ) := by field_simp

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Exact rational form of the nearest-bin error. -/
def binErrorRat (Q d j : ℕ) : ℚ := (bin Q d j : ℚ)-(j:ℚ)*Q/d

@[simp] lemma binErrorRat_cast (Q d j : ℕ) :
    (binErrorRat Q d j:ℝ) = binError Q d j := by simp [binErrorRat, binError]

/-- Half-open quarter assignment, computed only by rational arithmetic. -/
def quarterIndex (x : ℚ) : ℤ := ⌊4*x⌋

lemma quarterIndex_bounds (x : ℚ) :
    (quarterIndex x:ℝ)/4 ≤ (x:ℝ) ∧ (x:ℝ) ≤ ((quarterIndex x:ℝ)+1)/4 := by
  have hl := Int.floor_le (4*x)
  have hu := (Int.lt_floor_add_one (4*x)).le
  change (quarterIndex x:ℚ) ≤ 4*x at hl
  change 4*x ≤ (quarterIndex x:ℚ)+1 at hu
  have hl' : (quarterIndex x:ℝ) ≤ 4*(x:ℝ) := by exact_mod_cast hl
  have hu' : 4*(x:ℝ) ≤ (quarterIndex x:ℝ)+1 := by exact_mod_cast hu
  constructor <;> linarith

noncomputable def selectedMass (d : ℕ) (η u : ℚ) : ℚ[X] :=
  massPiece d η (quarterIndex (u/d)) (quarterIndex (u/d+η))

lemma selectedMass_natDegree_le (d : ℕ) (η u : ℚ) :
    (selectedMass d η u).natDegree ≤ 4 := massPiece_natDegree_le _ _ _ _

lemma selectedMass_eq {d : ℕ} (hd : 0 < d) (η : ℚ) {u : ℕ} (hu : u ≤ d)
    (hη : |(η:ℝ)| ≤ 1/2) :
    evalReal (selectedMass d η u) u = ‖residueIntegral d u η‖^2 := by
  have h₀ := quarterIndex_bounds ((u:ℚ)/d)
  have h₁ := quarterIndex_bounds ((u:ℚ)/d+η)
  push_cast at h₀ h₁
  exact massPiece_eq hd η (Nat.cast_nonneg u) (by exact_mod_cast hu) hη _ _
    h₀.1 h₀.2 h₁.1 h₁.2

/-- Literal majorant from (majorant-construction), retaining Q and B as arguments. -/
noncomputable def majorant (Q B d j u : ℕ) : ℚ :=
  roundedValue (Q*B^8) (selectedMass d (binErrorRat Q d j) u) u + 64/(Q:ℚ)

lemma majorant_ideal_error {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) {u : ℕ} (hu : u ≤ d) :
    64/(Q:ℝ) ≤ (majorant Q B d j u:ℝ)-‖residueIntegral d u (binError Q d j)‖^2 ∧
      (majorant Q B d j u:ℝ)-‖residueIntegral d u (binError Q d j)‖^2 ≤ 65/(Q:ℝ) := by
  have h := roundedValue_small_error hQ hB (selectedMass d (binErrorRat Q d j) u)
    (selectedMass_natDegree_le _ _ _) (hu.trans hdB)
  change 0 ≤ _-evalReal _ _ ∧ _-evalReal _ _ ≤ _ at h
  rw [selectedMass_eq hd _ hu (by simpa using binError_bound (Q:=Q) (j:=j) hd),
    binErrorRat_cast] at h
  simp only [majorant, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  simp only [div_eq_mul_inv] at h ⊢
  constructor <;> linarith [h.1, h.2]

lemma majorant_nonneg {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) {u : ℕ} (hu : u ≤ d) :
    0 ≤ majorant Q B d j u := by
  have h := (majorant_ideal_error hQ hB hd hdB j hu).1
  have hQ' : (0:ℝ) ≤ 64/(Q:ℝ) := by positivity
  have h' : (0:ℝ) ≤ majorant Q B d j u := by nlinarith [sq_nonneg ‖residueIntegral d u (binError Q d j)‖]
  exact_mod_cast h'

/-- Source majorant-error, with the stronger explicit margin 32/Q..97/Q. -/
lemma majorant_probability_error {Q B d t : ℕ} (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (hdQ : d ≤ Q) (ht : t < d) (j : ℕ) :
    32/(Q:ℝ) ≤ (majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t ∧
      (majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t ≤ 97/(Q:ℝ) := by
  have he := residueProbability_integral_error hd hdQ ht j
  rw [abs_le] at he
  have hm := majorant_ideal_error (hd.trans_le hdQ) hB hd hdB j (Nat.mod_lt (j*t) hd).le
  simp only [div_eq_mul_inv] at he hm ⊢
  constructor <;> linarith [he.1, he.2, hm.1, hm.2]

/-- Source half-sum, initially a mathematical sum; bounded-piece evaluation follows. -/
noncomputable def majorantSum (Q B d j : ℕ) : ℚ :=
  (∑ u ∈ Finset.range d, majorant Q B d j u)/2

lemma majorantSum_lower {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) :
    1/(128*(d:ℝ)) ≤ (majorantSum Q B d j:ℝ) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (d:ℝ)*(1/(8*(d:ℝ)))^2 ≤
      ∑ u ∈ Finset.range d, (majorant Q B d j u:ℝ) := by
    calc
      _ = ∑ _u ∈ Finset.range d, (1/(8*(d:ℝ)))^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        have hl := (residueIntegral_bounds hd (u:ℝ) (binError_bound (Q:=Q) (j:=j) hd)).1
        have hp : 0 ≤ 1/(8*(d:ℝ)) := by positivity
        have hl2 := sq_le_sq₀ hp (norm_nonneg _) |>.mpr hl
        have hm := (majorant_ideal_error hQ hB hd hdB j (u:=u) (by simp only [Finset.mem_range] at hu; omega)).1
        have hQ' : (0:ℝ) ≤ 64/(Q:ℝ) := by positivity
        linarith
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  have he : (d:ℝ)*(1/(8*(d:ℝ)))^2/2 = 1/(128*(d:ℝ)) := by field_simp; ring
  rw [← he]
  linarith

lemma majorantSum_upper {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) :
    (majorantSum Q B d j:ℝ) ≤ 1/(2*(d:ℝ))+65*d/(2*(Q:ℝ)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (∑ u ∈ Finset.range d, (majorant Q B d j u:ℝ)) ≤
      (d:ℝ)*((1/(d:ℝ))^2+65/(Q:ℝ)) := by
    calc
      _ ≤ ∑ _u ∈ Finset.range d, ((1/(d:ℝ))^2+65/(Q:ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        have hl := (residueIntegral_bounds hd (u:ℝ) (binError_bound (Q:=Q) (j:=j) hd)).2
        have hp : 0 ≤ 1/(d:ℝ) := by positivity
        have hl2 := (sq_le_sq₀ (norm_nonneg _) hp).mpr hl
        have hm := (majorant_ideal_error hQ hB hd hdB j (u:=u) (by simp only [Finset.mem_range] at hu; omega)).2
        linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  have he : (d:ℝ)*((1/(d:ℝ))^2+65/(Q:ℝ))/2 =
      1/(2*(d:ℝ))+65*d/(2*(Q:ℝ)) := by field_simp
  rw [← he]
  linarith

end ExactQuantumFactoring.OrderTrial



end

end OAI


