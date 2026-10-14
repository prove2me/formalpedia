-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part06
-- name    : OAI_QuantumFactoring_Part06
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:07:37.480642+00:00
-- url     : https://prove2.me/theorems/3e33abfa-088a-4b9a-90d0-30b1c6da8510
-- title:
--   Exact quantum factoring, part 6 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 6 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `TriangularCircuit`, `TriangularKernel`, `TriangularPreparation`, `OrderSampleCircuit`, `InitialOrderState`, `PrimalityAuxiliaryPrime`, `Primality`, `PrimalityRootCount`, `PrimalityArithmetic`, `PrimalityCorrectness`, `CyclicAlgebra`, `CyclicPrimality`, `AKSCriteria`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. This part also makes small compatibility edits for Lean 4.33.1 / Mathlib 0df444a: in PrimalityAuxiliaryPrime.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'` (monoid version; the semiring version now also requires nonnegativity); in PrimalityArithmetic.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TriangularCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TriangularKernel.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TriangularPreparation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderSampleCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/InitialOrderState.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PrimalityAuxiliaryPrime.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/Primality.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PrimalityRootCount.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PrimalityArithmetic.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PrimalityCorrectness.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicAlgebra.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicPrimality.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AKSCriteria.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 6 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: TriangularCircuit.lean, TriangularKernel.lean, TriangularPreparation.lean, OrderSampleCircuit.lean, InitialOrderState.lean, PrimalityAuxiliaryPrime.lean, Primality.lean, PrimalityRootCount.lean, PrimalityArithmetic.lean, PrimalityCorrectness.lean, CyclicAlgebra.lean, CyclicPrimality.lean, AKSCriteria.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in PrimalityAuxiliaryPrime.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'` (monoid version; the semiring version now also requires nonnegativity); in PrimalityArithmetic.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'`.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part05

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

abbrev work (b : ℕ) := 159*b+6
abbrev width (b : ℕ) := (b+b)+(b+b)+work b

noncomputable def encode (b : ℕ) (u : Bits b × ZMod (2^b)) : Basis (width b) :=
  packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)

lemma encode_injective (b : ℕ) : Function.Injective (encode b) := by
  intro u v h
  have he : Fin.append u.1 ((basisResidue b).symm u.2) =
      Fin.append v.1 ((basisResidue b).symm v.2) := by
    funext i
    have hh := congrFun h (⟨i.val,by dsimp [width,work]; omega⟩ : Fin (width b))
    simpa only [encode, packed_input] using hh
  apply Prod.ext
  · funext i
    have hh := congrFun he (i.castAdd b)
    simpa only [Fin.append_left] using hh
  · apply (basisResidue b).symm.injective
    funext i
    have hh := congrFun he (Fin.natAdd b i)
    simpa only [Fin.append_right] using hh

def dataWire {b : ℕ} (j : Fin b) : Fin (width b) := ⟨j.val,by have := j.isLt; dsimp [width,work]; omega⟩

lemma encode_bit {b : ℕ} (u : Bits b × ZMod (2^b)) (j : Fin b) :
    encode b u (dataWire j) = u.1 j := by
  change packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)
    (⟨(j.castAdd b).val,by dsimp [width,work]; omega⟩ : Fin (width b)) = _
  rw [packed_input, Fin.append_left]

lemma encode_update {b : ℕ} (u : Bits b × ZMod (2^b)) (j : Fin b) (c : Bool) :
    Function.update (encode b u) (dataWire j) c = encode b (Function.update u.1 j c,u.2) := by
  unfold encode
  rw [show dataWire j = (⟨(j.castAdd b).val,by dsimp [width,work]; omega⟩ : Fin (width b)) by rfl,
    packed_update_input, append_update_left]

lemma translation_count_forward {b : ℕ} (j : Fin b) :
    (ControlledTranslation.forward (rowNetwork j)).net.count ≤ work b := by
  have h := ControlledTranslation.forward_count (rowNetwork j)
  rw [rowNetwork_count] at h
  dsimp [work]
  omega

lemma translation_count_backward {b : ℕ} (j : Fin b) :
    (ControlledTranslation.backward (rowNetwork j)).net.count ≤ work b := by
  have h := ControlledTranslation.backward_count (rowNetwork j)
  rw [rowNetwork_count] at h
  dsimp [work]
  omega

def translation {b : ℕ} (j : Fin b) : List (Instruction (width b)) :=
  cleanPermutation (ControlledTranslation.forward (rowNetwork j))
    (ControlledTranslation.backward (rowNetwork j))
    (translation_count_forward j) (translation_count_backward j)

noncomputable def rowPerm {b : ℕ} (j : Fin b) : Equiv.Perm (Bits b × ZMod (2^b)) where
  toFun u := (u.1,u.2+(rowShift j u.1 : ZMod (2^b)))
  invFun u := (u.1,u.2-(rowShift j u.1 : ZMod (2^b)))
  left_inv u := by simp
  right_inv u := by simp

lemma translate_encode {b : ℕ} (j : Fin b) (u : Bits b × ZMod (2^b)) :
    ControlledTranslation.translate (fun d => bitsValue ((rowNetwork j).eval d))
      (Fin.append u.1 ((basisResidue b).symm u.2)) =
      Fin.append u.1 ((basisResidue b).symm (u.2+(rowShift j u.1 : ZMod (2^b)))) := by
  simp only [ControlledTranslation.translate, ControlledTranslation.dataPart_append,
    ControlledTranslation.phasePart_append, bitsValue_residue_add]
  rw [basisResidue_eq, rowNetwork_number]

lemma translation_basis {b : ℕ} (j : Fin b) (u : Bits b × ZMod (2^b)) :
    (programMatrix (translation j)).mulVec (basisVector (encode b u)) =
      basisVector (encode b (rowPerm j u)) := by
  unfold translation encode
  rw [cleanPermutation_basis _ _ _ _ _ (ControlledTranslation.forward_backward _ _),
    ControlledTranslation.forward_correct, translate_encode]
  rfl

lemma translation_apply {b : ℕ} (j : Fin b) (ψ : Bits b × ZMod (2^b) → ℂ) :
    (programMatrix (translation j)).mulVec (encodeState (encode b) ψ) =
      encodeState (encode b) (ψ ∘ (rowPerm j).symm) :=
  matrix_encode_permutation _ _ _ (translation_basis j) ψ

def rowCircuit {b : ℕ} (j : Fin b) : List (Instruction (width b)) :=
  [hadamardAt (dataWire j)] ++ translation j

lemma rowCircuit_apply {b : ℕ} (j : Fin b) (ψ : Bits b × ZMod (2^b) → ℂ) :
    (programMatrix (rowCircuit j)).mulVec (encodeState (encode b) ψ) =
      encodeState (encode b) (fun u =>
        (ψ (Function.update u.1 j false,u.2-(rowShift j u.1 : ZMod (2^b))) +
          (if u.1 j then (-1:ℂ) else 1)*
            ψ (Function.update u.1 j true,u.2-(rowShift j u.1 : ZMod (2^b)))) /
              (Real.sqrt 2:ℂ)) := by
  rw [rowCircuit, programMatrix_append, programMatrix_singleton, ← Matrix.mulVec_mulVec,
    encoded_hadamard (encode b) j (dataWire j) (fun u => encode_bit u j)
      (fun u c => encode_update u j c), translation_apply]
  congr 1
  funext u
  exact localHadamard_apply j ψ ((rowPerm j).symm u)

def triPrefix (b : ℕ) : (k : ℕ) → k ≤ b → List (Instruction (width b))
  | 0, _ => []
  | k+1, h => triPrefix b k (by omega) ++ rowCircuit ⟨k,by omega⟩

lemma triPrefix_apply {b : ℕ} (x : Bits b) (χ : ZMod (2^b) → ℂ) (k : ℕ) (hk : k ≤ b) :
    (programMatrix (triPrefix b k hk)).mulVec
        (encodeState (encode b) (fun u => if u.1=x then χ u.2 else 0)) =
      encodeState (encode b) (fun u =>
        evolve (fun j z => (rowShift j z : ZMod (2^b))) x χ k hk u.1 u.2) := by
  induction k with
  | zero => rw [triPrefix, programMatrix_nil, Matrix.one_mulVec]; rfl
  | succ k ih =>
    rw [triPrefix, programMatrix_append, ← Matrix.mulVec_mulVec, ih (by omega), rowCircuit_apply]
    rfl

lemma rowCircuit_length {b : ℕ} (j : Fin b) :
    (rowCircuit j).length ≤ 998*b+49 := by
  have h := cleanPermutation_length (ControlledTranslation.forward (rowNetwork j))
    (ControlledTranslation.backward (rowNetwork j))
    (translation_count_forward j) (translation_count_backward j)
  have hf := ControlledTranslation.forward_count (rowNetwork j)
  have hg := ControlledTranslation.backward_count (rowNetwork j)
  rw [rowNetwork_count] at hf hg
  change (translation j).length ≤ _ at h
  simp only [rowCircuit, List.length_append, List.length_singleton]
  omega

lemma triPrefix_length (b k : ℕ) (hk : k ≤ b) :
    (triPrefix b k hk).length ≤ k*(998*b+49) := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    have hp := ih (by omega)
    have hr := rowCircuit_length (⟨k,by omega⟩ : Fin b)
    simp only [triPrefix, List.length_append]
    nlinarith

end ExactQuantumFactoring.Triangular


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularKernel.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open OrderTrial

lemma phase_half (x : ℝ) : phase (x+1/2) = -phase x := by
  rw [show x+1/2 = (x+1/4)+1/4 by ring, phase_quarter, phase_quarter]
  simp only [neg_mul, mul_neg, neg_neg, ← mul_assoc, Complex.I_mul_I]
  ring

lemma phase_nat_half (x : ℝ) (h : ℕ) :
    phase (x+(h:ℝ)/2) = (-1:ℂ)^h*phase x := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show x+((h+1:ℕ):ℝ)/2 = (x+(h:ℝ)/2)+1/2 by push_cast; ring,
      phase_half, ih, pow_succ]
    ring

lemma phase_product {b : ℕ} (hb : 1 ≤ b) (x y : Bits b) :
    phase ((inputNumber x : ℝ)*outputNumber y/(2:ℝ)^b) =
      (-1:ℂ)^dot x y * phase ((∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b) := by
  have hq : (2:ℝ)^b ≠ 0 := by positivity
  have hh : 2*(2:ℝ)^(b-1) = (2:ℝ)^b := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hb]
  have hd := congrArg (Nat.cast : ℕ → ℝ) (product_decomposition x y)
  push_cast at hd
  have he : (inputNumber x : ℝ)*outputNumber y/(2:ℝ)^b =
      (∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b + (dot x y : ℝ)/2 +
        (∑ i, ∑ j, highTerm x y i j : ℕ) := by
    push_cast
    rw [hd]
    field_simp
    nlinarith [hh]
  rw [he]
  have hp := phase_add_int
    ((∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b + (dot x y : ℝ)/2)
    ((∑ i, ∑ j, highTerm x y i j : ℕ) : ℤ)
  simp only [Int.cast_natCast] at hp
  rw [hp, phase_nat_half]

noncomputable def residuePhase (a : ℕ) (z : ZMod (2^(a+2))) : ℂ :=
  phaseState (2^a) z.val

lemma residuePhase_correlation (a D : ℕ) :
    (∑ z : ZMod (2^(a+2)), star (residuePhase a (z+(D:ZMod (2^(a+2))))) *
      residuePhase a z) = phase ((D:ℝ)/(2:ℝ)^(a+2)) := by
  have hQ : 2^(a+2) = 4*2^a := by ring
  rw [← Equiv.sum_comp (ZMod.finEquiv (2^(a+2))).toEquiv]
  have hv {n : ℕ} [NeZero n] (z : Fin n) : ((ZMod.finEquiv n).toEquiv z).val = z.val := by
    cases n with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ n => rfl
  simp only [residuePhase, ZMod.val_add, ZMod.val_natCast,
    hv, Nat.add_mod_mod]
  change (∑ x : Fin (2^(a+2)), (fun t : ℕ => star (phaseState (2^a)
    ((t+D) % 2^(a+2))) * phaseState (2^a) t) x.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => star (phaseState (2^a)
    ((t+D) % 2^(a+2))) * phaseState (2^a) t) (2^(a+2)), hQ,
    phaseState_overlap (by positivity)]
  congr 1
  push_cast
  ring

/-- The full triangular coherent path expansion has exactly the manuscript's
selected kernel, after the phase register is tested in its prepared state. -/
theorem selected_kernel (a : ℕ) (x y : Bits (a+2)) :
    (∑ z : ZMod (2^(a+2)), star (residuePhase a z) *
      evolve (fun j v => (rowShift j v : ZMod (2^(a+2)))) x (residuePhase a)
        (a+2) le_rfl y z) =
      (Real.sqrt ((2:ℝ)^(a+2)) : ℂ)⁻¹ *
        phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(a+2)) := by
  rw [selected_evolve, pathWeight_full, pathShift_rows,
    residuePhase_correlation, phase_product (by omega), hadamard_normalization]
  ring

end ExactQuantumFactoring.Triangular


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularPreparation.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

def phaseRegister (b : ℕ) : Register b (width b) where
  toFun i := ⟨b+i.val,by dsimp [width,work]; have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change b+i.val=b+j.val at hh
    omega

lemma encode_phase {b : ℕ} (u : Bits b × ZMod (2^b)) :
    encode b u ∘ phaseRegister b = (basisResidue b).symm u.2 := by
  funext i
  change packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)
    (⟨(Fin.natAdd b i).val,by dsimp [width,work]; omega⟩ : Fin (width b)) = _
  rw [packed_input, Fin.append_right]

lemma encode_outside_phase {b : ℕ} (x : Bits b) (z z' : ZMod (2^b))
    (i : (phaseRegister b).Unused) : encode b (x,z) i.val = encode b (x,z') i.val := by
  by_cases hi : i.val.val < b+b
  · have hlo : i.val.val < b := by
      by_contra hn
      have hv : phaseRegister b ⟨i.val.val-b,by omega⟩ = i.val := by
        apply Fin.ext
        change b+(i.val.val-b) = i.val.val
        omega
      exact i.property _ hv
    have he : i.val = (⟨(Fin.castAdd b (⟨i.val.val,hlo⟩ : Fin b)).val,
        by dsimp [width,work]; omega⟩ : Fin (width b)) := Fin.ext rfl
    rw [he]
    simp only [encode, packed_input, Fin.append_left]
  · simp [encode, packed, hi]

lemma encode_replace_phase {b : ℕ} (x : Bits b) (z : ZMod (2^b)) (v : Basis b) :
    (phaseRegister b).replace (encode b (x,z)) v = encode b (x,basisResidue b v) := by
  apply (phaseRegister b).split.injective
  apply Prod.ext
  · rw [Register.replace, Equiv.apply_symm_apply]
    change v = encode b (x,basisResidue b v) ∘ phaseRegister b
    rw [encode_phase, Equiv.symm_apply_apply]
  · funext i
    change (phaseRegister b).replace (encode b (x,z)) v i.val = _
    rw [Register.replace_outside]
    exact encode_outside_phase x z _ i

def preparation (a : ℕ) : List (Instruction (width (a+2))) :=
  (preparePhase (a+2) (by omega)).map (Instruction.place (phaseRegister (a+2)))

lemma preparation_length (a : ℕ) : (preparation a).length = a+5 := by
  simp [preparation, preparePhase_length]

lemma preparation_basis (a : ℕ) (x : Bits (a+2)) :
    (programMatrix (preparation a)).mulVec (basisVector (encode (a+2) (x,0))) =
      encodeState (encode (a+2)) (fun u => if u.1=x then residuePhase a u.2 else 0) := by
  classical
  rw [preparation, Register.placed_basis_state, encode_phase]
  have hz : (basisResidue (a+2)).symm 0 = (fun _ => false) := by
    apply (basisResidue (a+2)).injective
    rw [Equiv.apply_symm_apply, basisResidue_zero]
  rw [hz]
  unfold encodeState
  simp only [preparePhase_label, encode_replace_phase, Fintype.sum_prod_type,
    ite_smul, zero_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Equiv.sum_comp (basisResidue (a+2))]
  apply Finset.sum_congr rfl
  intro v _
  rw [residuePhase, basisResidue_val]

/-- Preparation, actual clean triangular gate program, inverse preparation.
The success event is the all-zero phase and scratch register; it is not enforced. -/
def transform (a : ℕ) : List (Instruction (width (a+2))) :=
  preparation a ++ triPrefix (a+2) (a+2) le_rfl ++
    (preparation a).reverse.map Instruction.reverse

lemma transform_length (a : ℕ) :
    (transform a).length ≤ (a+2)*(998*(a+2)+49)+2*(a+5) := by
  have h := triPrefix_length (a+2) (a+2) le_rfl
  simp only [transform, List.length_append, List.length_map, List.length_reverse,
    preparation_length]
  omega

/-- The exact selected matrix entry of an actual fixed-gate circuit. -/
theorem transform_selected (a : ℕ) (x y : Bits (a+2)) :
    (programMatrix (transform a)).mulVec (basisVector (encode (a+2) (x,0)))
      (encode (a+2) (y,0)) =
      (Real.sqrt ((2:ℝ)^(a+2)) : ℂ)⁻¹ *
        OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(a+2)) := by
  classical
  rw [transform, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    preparation_basis, triPrefix_apply, programMatrix_reverse]
  change (programMatrix (preparation a)).conjTranspose.mulVec _ _ = _
  rw [encoded_adjoint_test (encode (a+2)) (encode_injective (a+2)) _ _ _ _
    (preparation_basis a y)]
  simp only [Fintype.sum_prod_type, apply_ite, star_zero, zero_mul, ite_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact selected_kernel a x y

end ExactQuantumFactoring.Triangular


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderSampleCircuit.lean =====
namespace OAI

section
open scoped BigOperators


/-! Actual modular-power/triangular-transform order sampler. All arithmetic
inputs are read-only wires; the modular output remains coherent. -/
namespace ExactQuantumFactoring.OrderSample
open scoped BigOperators
open BooleanNetwork Triangular

abbrev inputWidth (w b : ℕ) := (w+w)+Triangular.width b

noncomputable def inputWord {w b : ℕ} (a m : Basis w) (x : Basis b) :
    Basis (inputWidth w b) := Fin.append (Fin.append a m) (Triangular.encode b (x,0))

def powerInputs (w b : ℕ) : BooleanNetwork (inputWidth w b) ((w+w)+b) :=
  select (Fin.addCases (Fin.castAdd (Triangular.width b))
    (fun i => Fin.natAdd (w+w) (Triangular.dataWire i)))

lemma powerInputs_eval {w b : ℕ} (a m : Basis w) (x : Basis b) :
    (powerInputs w b).eval (inputWord a m x) = Fin.append (Fin.append a m) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [powerInputs,eval_select,Function.comp_apply,Fin.addCases_left,inputWord,
      Fin.append_left]
  · simp only [powerInputs,eval_select,Function.comp_apply,Fin.addCases_right,inputWord,
      Fin.append_right,Triangular.encode_bit]

def powerNetwork (w b : ℕ) : BooleanNetwork (inputWidth w b) w :=
  (powerInputs w b).comp (BitArithmetic.modularPower w b)

lemma powerNetwork_count (w b : ℕ) : (powerNetwork w b).net.count ≤
    w+b*(3672*w*w+436*w+36) := by
  simpa only [powerNetwork,count_comp,powerInputs,count_select,zero_add] using
    BitArithmetic.modularPower_count w b

lemma powerNetwork_value {w b : ℕ} (a m : Basis w) (x : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((powerNetwork w b).eval (inputWord a m x))).toNat =
      (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat := by
  rw [powerNetwork,eval_comp,powerInputs_eval,BitArithmetic.modularPower_value _ _ _ hm,
    BitArithmetic.horner_full]

lemma powerNetwork_eq {w b : ℕ} (a m : Basis w) (x : Basis b) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (powerNetwork w b).eval (inputWord a m x)=u ↔
      (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat=(bitsValue u).toNat := by
  rw [← powerNetwork_value a m x hm]
  constructor
  · intro h; rw [h]
  · intro h
    exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)

abbrev scratch (w b : ℕ) := w+b*(3672*w*w+436*w+36)
abbrev width (w b : ℕ) := inputWidth w b+w+scratch w b

def program (w s : ℕ) : List (Instruction (width w (s+2))) :=
  sampleProgram (powerNetwork w (s+2)) (powerNetwork_count w (s+2))
    (rightProgram (w+w) (Triangular.transform s))

lemma program_length (w s : ℕ) : (program w s).length ≤
    4*scratch w (s+2)+2*w+(s+2)*(998*(s+2)+49)+2*(s+5) := by
  have hh := sampleProgram_length (powerNetwork w (s+2)) (powerNetwork_count w (s+2))
    (rightProgram (w+w) (Triangular.transform s))
  have ht := Triangular.transform_length s
  have hp := powerNetwork_count w (s+2)
  simp only [rightProgram,List.length_map] at hh
  change (program w s).length ≤ _ at hh
  dsimp [scratch] at ⊢
  omega

noncomputable def word {w b : ℕ} (a m : Basis w) (x : Basis b) (u : Basis w) :
    Basis (width w b) := packed (scratch w b) (inputWord a m x) u

noncomputable def uniformInput (w b : ℕ) (a m : Basis w) : State (width w b) :=
  encodeState (fun x : Basis b => word a m x (fun _ => false))
    (fun _ => (Real.sqrt ((2:ℝ)^b):ℂ)⁻¹)

lemma transform_entry {w s : ℕ} (a m : Basis w) (x y : Basis (s+2)) :
    programMatrix (rightProgram (w+w) (Triangular.transform s))
      (inputWord a m y) (inputWord a m x) =
    (Real.sqrt ((2:ℝ)^(s+2)):ℂ)⁻¹ *
      OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(s+2)) := by
  rw [inputWord,inputWord,rightProgram_entry]
  have hh := Triangular.transform_selected s x y
  simpa only [matrix_basisVector] using hh

/-- The physically produced selected amplitude, expressed as a finite word sum. -/
lemma program_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (program w s)).mulVec (uniformInput w (s+2) a m) (word a m y u) =
      ((2:ℂ)^(s+2))⁻¹ * ∑ x : Basis (s+2),
        if (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(s+2)) else 0 := by
  classical
  rw [program,uniformInput]
  change (programMatrix (sampleProgram _ _ _)).mulVec
    (encodeState (fun x : Basis (s+2) => packed _ (inputWord a m x) (fun _ => false)) _)
    (packed _ (inputWord a m y) u) = _
  rw [sampleProgram_encoded_amplitude]
  simp_rw [powerNetwork_eq a m _ u hm,transform_entry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · have hh : (Real.sqrt ((2:ℝ)^(s+2)):ℂ)^2 = (2:ℂ)^(s+2) := by
      rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity),Complex.ofReal_pow]
      rfl
    rw [← hh]
    ring
  · simp

lemma inputNumber_sum (b : ℕ) (f : ℕ → ℂ) :
    (∑ x : Basis b, f (inputNumber x)) = ∑ x ∈ Finset.range (2^b), f x := by
  let e : Basis b ≃ Fin (2^b) := Equiv.ofBijective _ (Triangular.inputNumber_bijective b)
  rw [← Fin.sum_univ_eq_sum_range]
  exact e.sum_comp (fun x => f x.val)

/-- Exactly 1/Q times the coherent modular-power residue sum of Section3. -/
theorem program_amplitude_range {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (program w s)).mulVec (uniformInput w (s+2) a m) (word a m y u) =
      ((2^(s+2):ℕ):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^(s+2)),
        if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((outputNumber y:ℝ)*x/(2^(s+2):ℕ)) else 0 := by
  rw [program_amplitude a m y u hm]
  push_cast
  simp_rw [mul_comm (inputNumber _ : ℝ) (outputNumber y : ℝ)]
  congr 1
  exact inputNumber_sum (s+2) (fun x =>
    if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
    then OrderTrial.phase ((outputNumber y:ℝ)*x/(2:ℝ)^(s+2)) else 0)

end ExactQuantumFactoring.OrderSample


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/InitialOrderState.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma encodeState_comp {α : Type*} [Fintype α] {p q : ℕ}
    (e : α → Basis p) (f : Basis p → Basis q) (ψ : α → ℂ) :
    encodeState f (encodeState e ψ) = encodeState (f ∘ e) ψ := by
  classical
  change encodeState f (∑ a, ψ a • basisVector (e a)) = _
  rw [encodeState_sum]
  simp_rw [encodeState_smul,encodeState_basis]
  rfl

namespace Triangular

def dataRegister (b : ℕ) : Register b (width b) :=
  ⟨dataWire,by
    intro i j h
    exact Fin.ext (congrArg (fun t : Fin (width b) => t.val) h)⟩

lemma encode_data {b : ℕ} (u : Bits b × ZMod (2^b)) :
    encode b u ∘ dataRegister b = u.1 := by
  funext i
  exact encode_bit u i

lemma encode_outside_data {b : ℕ} (x y : Bits b) (z : ZMod (2^b))
    (i : (dataRegister b).Unused) : encode b (x,z) i.val = encode b (y,z) i.val := by
  have hi : ¬i.val.val < b := by
    intro hi
    exact i.property ⟨i.val.val,hi⟩ rfl
  by_cases hh : i.val.val < b+b
  · have he : i.val = (⟨(Fin.natAdd b (⟨i.val.val-b,by omega⟩ : Fin b)).val,
        by dsimp [width,work]; omega⟩ : Fin (width b)) := by
      apply Fin.ext
      change i.val.val = b+(i.val.val-b)
      omega
    rw [he]
    simp only [encode,packed_input,Fin.append_right]
  · simp [encode,packed,hh]

lemma encode_replace_data {b : ℕ} (x y : Bits b) (z : ZMod (2^b)) :
    (dataRegister b).replace (encode b (x,z)) y = encode b (y,z) := by
  apply (dataRegister b).split.injective
  apply Prod.ext
  · rw [Register.replace,Equiv.apply_symm_apply]
    exact (encode_data (y,z)).symm
  · funext i
    change (dataRegister b).replace (encode b (x,z)) y i.val = _
    rw [Register.replace_outside]
    exact encode_outside_data x y z i

def uniformPreparation (b : ℕ) : List (Instruction (width b)) :=
  (hadamardPrefix b b le_rfl).map (Instruction.place (dataRegister b))

lemma uniformPreparation_length (b : ℕ) : (uniformPreparation b).length=b := by
  simp [uniformPreparation,hadamardPrefix_length]

lemma uniformPreparation_zero (b : ℕ) :
    (programMatrix (uniformPreparation b)).mulVec
      (basisVector (encode b ((fun _ => false),0))) =
    encodeState (fun x => encode b (x,0))
      (fun _ => (Real.sqrt ((2:ℝ)^b):ℂ)⁻¹) := by
  rw [uniformPreparation,Register.placed_basis_state,encode_data,hadamards_zero]
  change encodeState (fun y => (dataRegister b).replace (encode b ((fun _ => false),0)) y)
    (fun _ => (Real.sqrt 2:ℂ)⁻¹^b) = _
  simp_rw [encode_replace_data,hadamard_normalization]

end Triangular
namespace OrderSample

def initial (w b : ℕ) : List (Instruction (width w b)) :=
  firstProgram w (scratch w b) (rightProgram (w+w) (Triangular.uniformPreparation b))

lemma initial_length (w b : ℕ) : (initial w b).length=b := by
  simp [initial,firstProgram_length,rightProgram,Triangular.uniformPreparation_length]

lemma initial_zero (w b : ℕ) (a m : Basis w) :
    (programMatrix (initial w b)).mulVec
      (basisVector (word a m (fun _ => false) (fun _ => false))) = uniformInput w b a m := by
  rw [initial,word,firstProgram_basis,inputWord,rightProgram_basis,
    Triangular.uniformPreparation_zero,encodeState_comp,encodeState_comp]
  rfl

def completeSampler (w s : ℕ) : List (Instruction (width w (s+2))) :=
  initial w (s+2) ++ program w s

lemma completeSampler_length (w s : ℕ) : (completeSampler w s).length ≤
    (s+2)+4*scratch w (s+2)+2*w+(s+2)*(998*(s+2)+49)+2*(s+5) := by
  have h := program_length w s
  simp only [completeSampler,List.length_append,initial_length]
  omega

/-- Physical sampler starts from a computational basis vector, not an assumed
uniform state. Its selected entry is the exact residue-class interference sum. -/
theorem completeSampler_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (completeSampler w s)).mulVec
      (basisVector (word a m (fun _ => false) (fun _ => false))) (word a m y u) =
      ((2^(s+2):ℕ):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^(s+2)),
        if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((Triangular.outputNumber y:ℝ)*x/(2^(s+2):ℕ)) else 0 := by
  rw [completeSampler,programMatrix_append,← Matrix.mulVec_mulVec,initial_zero]
  exact program_amplitude_range a m y u hm

end OrderSample
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimalityAuxiliaryPrime.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- A quantitative bound at the manuscript's unchanged cutoff n^8. We reuse
Mathlib's proved Chebyshev bound instead of repeating its binomial argument. -/
lemma primorial_gt_cutoff {n : ℕ} (hn : 128 ≤ n) :
    2^(n^6) < primorial (n^8) := by
  have hnR : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hlog8 : Real.log ((n : ℝ)^8+1) ≤ 1+8*(n : ℝ) := by
    have h8 : (1 : ℝ) ≤ (n : ℝ)^8 := one_le_pow₀ hn1
    calc
      Real.log ((n : ℝ)^8+1) ≤ Real.log (2*(n : ℝ)^8) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + 8*Real.log (n : ℝ) := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 1+8*(n : ℝ) := by linarith
  have hsqrt : Real.sqrt ((n : ℝ)^8) = (n : ℝ)^4 := by
    rw [show (n : ℝ)^8 = ((n : ℝ)^4)^2 by ring, Real.sqrt_sq (by positivity)]
  have ht := Chebyshev.theta_ge (n^8)
  simp only [Nat.cast_pow, hsqrt, Real.log_pow, Nat.cast_ofNat] at ht
  have h6pos : (0 : ℝ) < (n : ℝ)^6 := by positivity
  have h6one : (1 : ℝ) ≤ (n : ℝ)^6 := one_le_pow₀ hn1
  have hn6 : (n : ℝ) ≤ (n : ℝ)^6 := le_self_pow₀ hn1 (by decide : 6 ≠ 0)
  have h56 : (n : ℝ)^5 ≤ (n : ℝ)^6 := pow_le_pow_right₀ hn1 (by decide)
  have h86 : (128 : ℝ)^2*(n : ℝ)^6 ≤ (n : ℝ)^8 := by
    calc
      (128 : ℝ)^2*(n : ℝ)^6 ≤ (n : ℝ)^2*(n : ℝ)^6 := by gcongr
      _ = (n : ℝ)^8 := by ring
  have hmain : (n : ℝ)^6 < Chebyshev.theta (n^8) := by
    have hmul := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ (n : ℝ)^8 by positivity)
    have hlogmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 16*(n : ℝ)^4 by positivity)
    have hlogmul' : 16*(n : ℝ)^4*Real.log (n : ℝ) ≤ 16*(n : ℝ)^5 := by
      calc
        _ ≤ 16*(n : ℝ)^4*(n : ℝ) := hlogmul
        _ = _ := by ring
    nlinarith only [ht, hmul, hlogmul', hlog8, h86, h6one, hn6, h56]
  have hlogpow : Real.log ((2^(n^6) : ℕ) : ℝ) <
      Real.log (primorial (n^8) : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial] at hmain
    simp only [← Nat.cast_pow, Nat.floor_natCast] at hmain
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    exact (mul_lt_mul_of_pos_left hl2' h6pos).trans_le (by simpa only [Nat.cast_pow, mul_one] using hmain.le)
  have := (Real.log_lt_log_iff (by positivity) (by exact_mod_cast primorial_pos (n^8))).mp hlogpow
  exact_mod_cast this

/-- The finite integer excluded by the auxiliary-prime search. -/
def badProduct (n m : ℕ) : ℕ := m * ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1)

lemma badProduct_pos {n m : ℕ} (hm : 2 ≤ m) : 0 < badProduct n m := by
  apply Nat.mul_pos (by omega)
  apply Finset.prod_pos
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjm : 2 ≤ m^j := by
    exact hm.trans (Nat.le_pow (by omega))
  omega

lemma badProduct_lt_cutoff {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n) :
    badProduct n m < 2^(n^6) := by
  have hp : ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1) ≤ m^(n^4) := by
    calc
      ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1) ≤ ∏ _j ∈ Finset.Icc 1 (n^2), m^(n^2) := by
        apply Finset.prod_le_prod'
        intro j hj
        exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (Finset.mem_Icc.mp hj).2)
      _ = m^(n^4) := by simp [← pow_mul]; congr 1; ring
  have hexp : n*(1+n^4) < n^6 := by
    have hn1 : 1 ≤ n := by omega
    have hn4 : 1 ≤ n^4 := Nat.one_le_pow _ _ hn1
    have hn2 : 2*n ≤ n^2 := by nlinarith
    have h56 : n^5 < n^6 := Nat.pow_lt_pow_right (by omega) (by decide)
    have h46 : 2*n^5 ≤ n^6 := by
      calc
        2*n^5 = (2*n)*n^4 := by ring
        _ ≤ n^2*n^4 := Nat.mul_le_mul_right _ hn2
        _ = n^6 := by ring
    have hn5 : n < n^5 := by simpa using Nat.pow_lt_pow_right (by omega : 1 < n) (by decide : 1 < 5)
    nlinarith
  calc
    badProduct n m ≤ m^(1+n^4) := by simpa [badProduct, pow_add] using Nat.mul_le_mul_left m hp
    _ < (2^n)^(1+n^4) := Nat.pow_lt_pow_left hmb (by omega)
    _ = 2^(n*(1+n^4)) := (pow_mul _ _ _).symm
    _ < 2^(n^6) := Nat.pow_lt_pow_right (by decide) hexp

/-- The auxiliary prime searched for by the source algorithm exists within n^8;
no number-theoretic existence oracle is included in the algorithm. -/
theorem auxiliary_prime_exists {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n) :
    ∃ s : ℕ, s.Prime ∧ s ≤ n^8 ∧ s.Coprime m ∧ n^2 < orderOf (m : ZMod s) := by
  have hpgt := primorial_gt_cutoff hn
  have hb := badProduct_lt_cutoff hn hm hmb
  have hex : ∃ s ∈ Nat.primesLE (n^8), ¬ s ∣ badProduct n m := by
    by_contra h
    have hall : ∀ s ∈ Nat.primesLE (n^8), s ∣ badProduct n m := by simpa using h
    have hd : primorial (n^8) ∣ badProduct n m := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_primes_dvd _ (fun s hs => (Nat.mem_primesLE.mp hs).2.prime) hall
    exact (not_lt_of_ge (Nat.le_of_dvd (badProduct_pos hm) hd)) (hb.trans hpgt)
  obtain ⟨s,hs,hbad⟩ := hex
  have hs' := (Nat.mem_primesLE.mp hs).2
  have hsm : ¬ s ∣ m := fun hd => hbad (dvd_mul_of_dvd_left hd _)
  have hcop := hs'.coprime_iff_not_dvd.mpr hsm
  refine ⟨s,hs',(Nat.mem_primesLE.mp hs).1,hcop,?_⟩
  let : Fact s.Prime := ⟨hs'⟩
  have hopos : 0 < orderOf (m : ZMod s) :=
    ((ZMod.isUnit_iff_coprime m s).mpr hcop.symm).isOfFinOrder.orderOf_pos
  by_contra h
  have ho : orderOf (m : ZMod s) ∈ Finset.Icc 1 (n^2) := Finset.mem_Icc.mpr ⟨hopos,by omega⟩
  have hpow : s ∣ m^(orderOf (m : ZMod s))-1 := by
    rw [← ZMod.natCast_eq_zero_iff (b := s)]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_one, Nat.cast_pow,
      pow_orderOf_eq_one, sub_self]
  exact hbad (dvd_mul_of_dvd_right (hpow.trans (Finset.dvd_prod_of_mem (fun j => m^j-1) ho)) m)

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/Primality.lean =====
namespace OAI

section


/-! Necessary exact primality component of Appendix A.  The tests are polynomial
congruences, not a primality oracle.  These lemmas start the appendix's actual
root-count proof; no polynomial-time implementation is assumed here. -/
namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The evaluation form of an introspective exponent modulo X^s-1. -/
def Introspective {F : Type*} [CommRing F] (s k : ℕ) (f : F[X]) : Prop :=
  ∀ z : F, z^s = 1 → (f.eval z)^k = f.eval (z^k)

lemma Introspective.one {F : Type*} [CommRing F] (s : ℕ) (f : F[X]) :
    Introspective s 1 f := by intro z _; simp

lemma Introspective.mul_exp {F : Type*} [CommRing F] {s k l : ℕ} {f : F[X]}
    (hk : Introspective s k f) (hl : Introspective s l f) :
    Introspective s (k*l) f := by
  intro z hz
  rw [pow_mul, hk z hz, hl]
  · rw [pow_mul]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]

lemma Introspective.pow_exp {F : Type*} [CommRing F] {s k : ℕ} {f : F[X]}
    (hk : Introspective s k f) (u : ℕ) : Introspective s (k^u) f := by
  induction u with
  | zero => simpa using Introspective.one s f
  | succ u hu => simpa [pow_succ] using hu.mul_exp hk

lemma Introspective.mul_poly {F : Type*} [CommRing F] {s k : ℕ} {f g : F[X]}
    (hf : Introspective s k f) (hg : Introspective s k g) :
    Introspective s k (f*g) := by
  intro z hz
  simp only [eval_mul, mul_pow]
  rw [hf z hz, hg z hz]

lemma Introspective.prod {F ι : Type*} [CommRing F] {s k : ℕ}
    (S : Finset ι) (f : ι → F[X]) (hf : ∀ i ∈ S, Introspective s k (f i)) :
    Introspective s k (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro z _; simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul_poly
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A successful congruence test implies the evaluation identity at every
s-th root. This implication includes the zero polynomial case correctly. -/
lemma introspective_of_congruence {F : Type*} [CommRing F] {s k : ℕ} {f : F[X]}
    (h : X^s - 1 ∣ f^k - f.comp (X^k)) : Introspective s k f := by
  intro z hz
  obtain ⟨q, hq⟩ := h
  have hzq := congrArg (Polynomial.eval z) hq
  simpa [hz, sub_eq_zero] using hzq

lemma natCast_frobenius {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : ℕ) : (a : F)^p = (a : F) := by
  exact map_natCast (frobenius F p) a

lemma linear_frobenius {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (s a : ℕ) : Introspective s p (X + C (a : F)) := by
  intro z _
  simp only [eval_add, eval_X, eval_C]
  rw [add_pow_char, natCast_frobenius]

/-- Every product tested in the root count propagates along m^u p^v, precisely
as in equation (A.4); no division by its value at a root is involved. -/
lemma propagate {F ι : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (s m : ℕ) (S : Finset ι) (a : ι → ℕ)
    (htest : ∀ i ∈ S, Introspective s m (X+C (a i : F))) (u v : ℕ) :
    Introspective s (m^u*p^v) (∏ i ∈ S, (X+C (a i : F))) := by
  apply Introspective.mul_exp
  · exact (Introspective.prod S _ htest).pow_exp u
  · exact (Introspective.prod S _ (fun i _ => linear_frobenius p s (a i))).pow_exp v

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimalityRootCount.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The nonnegative exponent orbit. In a finite group this is the manuscript's H;
using its submonoid presentation makes the m^u p^v representatives explicit. -/
def residueOrbit (s m p : ℕ) : Submonoid (ZMod s) :=
  Submonoid.closure {(m : ZMod s), (p : ZMod s)}

lemma residueOrbit_rep {s m p : ℕ} (x : residueOrbit s m p) :
    ∃ u v : ℕ, ((m^u*p^v : ℕ) : ZMod s) = x.val := by
  simpa using (Submonoid.mem_closure_pair (m : ZMod s) (p : ZMod s) x.val).mp x.property

noncomputable def residueRoot {F : Type*} [Field F] {s m p : ℕ}
    (w : F) (x : residueOrbit s m p) : F := w^x.val.val

lemma residueRoot_injective {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) :
    Function.Injective (residueRoot (s := s) (m := m) (p := p) w) := by
  intro x y hxy
  apply Subtype.ext
  apply ZMod.val_injective
  exact hw.pow_inj (ZMod.val_lt x.val) (ZMod.val_lt y.val) hxy

lemma eval_eq_on_orbit {F : Type*} [Field F] {s m p : ℕ} {w : F}
    (hw : w^s = 1) {f g : F[X]}
    (hfm : Introspective s m f) (hfp : Introspective s p f)
    (hgm : Introspective s m g) (hgp : Introspective s p g)
    (hfg : f.eval w = g.eval w) (x : residueOrbit s m p) :
    f.eval (residueRoot w x) = g.eval (residueRoot w x) := by
  obtain ⟨u,v,hrep⟩ := residueOrbit_rep x
  have hf := ((hfm.pow_exp u).mul_exp (hfp.pow_exp v)) w hw
  have hg := ((hgm.pow_exp u).mul_exp (hgp.pow_exp v)) w hw
  have hk : residueRoot w x = w^(m^u*p^v) := by
    unfold residueRoot
    rw [← hrep, ZMod.val_natCast, ← pow_eq_pow_mod _ hw]
  rw [hk, ← hf, ← hg, hfg]

/-- The lower-bound injection is proved by h distinct roots of f-g, not by
assuming any tested product has a nonzero value. -/
lemma eval_injective_low_degree {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) {f g : F[X]}
    (hfm : Introspective s m f) (hfp : Introspective s p f)
    (hgm : Introspective s m g) (hgp : Introspective s p g)
    (hfg : f.eval w = g.eval w)
    (hf : f.natDegree < Nat.card (residueOrbit s m p))
    (hg : g.natDegree < Nat.card (residueOrbit s m p)) : f = g := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite (residueOrbit s m p)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq f g (residueRoot_injective (m := m) (p := p) hw)
  · exact eval_eq_on_orbit hw.pow_eq_one hfm hfp hgm hgp hfg
  · simpa [Nat.card_eq_fintype_card] using max_lt hf hg

noncomputable def subsetPolynomial {F : Type*} [Field F] (S : Finset F) : F[X] :=
  ∏ a ∈ S, (X-C a)

lemma subsetPolynomial_injective {F : Type*} [Field F] :
    Function.Injective (subsetPolynomial (F := F)) := by
  intro S T h
  have hr := congrArg Polynomial.roots h
  simpa [subsetPolynomial, Polynomial.roots_prod_X_sub_C, Finset.val_inj] using hr

lemma subsetPolynomial_degree {F : Type*} [Field F] (S : Finset F) :
    (subsetPolynomial S).natDegree = S.card :=
  Polynomial.natDegree_finsetProd_X_sub_C_eq_card S id

lemma subsetPolynomial_introspective {F : Type*} [Field F] {s k : ℕ}
    (S : Finset F) (hf : ∀ a ∈ S, Introspective s k (X-C a)) :
    Introspective s k (subsetPolynomial S) := Introspective.prod S _ hf

/-- The entire lower/upper root count, prior to arithmetic estimates: a collision
of two distinct integer exponents bounds the number of subset products. -/
lemma subset_count_le_collision {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) (S : Finset F) {t k₁ k₂ : ℕ}
    (ht : t < Nat.card (residueOrbit s m p))
    (hm : ∀ a ∈ S, Introspective s m (X-C a))
    (hp : ∀ a ∈ S, Introspective s p (X-C a))
    (hk₁ : ∀ a ∈ S, Introspective s k₁ (X-C a))
    (hk₂ : ∀ a ∈ S, Introspective s k₂ (X-C a))
    (hk : w^k₁ = w^k₂) (hne : k₁ ≠ k₂) :
    S.card.choose t ≤ max k₁ k₂ := by
  classical
  let T := S.powersetCard t
  let values := T.image (fun A => (subsetPolynomial A).eval w)
  have he : Set.InjOn (fun A => (subsetPolynomial A).eval w) T := by
    intro A hA B hB hAB
    obtain ⟨hAS,hAt⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨hBS,hBt⟩ := Finset.mem_powersetCard.mp hB
    apply subsetPolynomial_injective
    exact eval_injective_low_degree hw
      (subsetPolynomial_introspective A (fun a ha => hm a (hAS ha)))
      (subsetPolynomial_introspective A (fun a ha => hp a (hAS ha)))
      (subsetPolynomial_introspective B (fun a ha => hm a (hBS ha)))
      (subsetPolynomial_introspective B (fun a ha => hp a (hBS ha))) hAB
      (by simpa [subsetPolynomial_degree, hAt] using ht)
      (by simpa [subsetPolynomial_degree, hBt] using ht)
  have hv : values.card = S.card.choose t := by
    rw [Finset.card_image_of_injOn he, Finset.card_powersetCard]
  have hpoly : (X^k₁-X^k₂ : F[X]) ≠ 0 := by
    intro hz
    have heq := congrArg Polynomial.natDegree (sub_eq_zero.mp hz)
    exact hne (by simpa using heq)
  have hroots : values.val ⊆ (X^k₁-X^k₂ : F[X]).roots := by
    intro z hz
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hAS,_⟩ := Finset.mem_powersetCard.mp hA
    rw [Polynomial.mem_roots hpoly]
    have h₁ := subsetPolynomial_introspective A (fun a ha => hk₁ a (hAS ha)) w hw.pow_eq_one
    have h₂ := subsetPolynomial_introspective A (fun a ha => hk₂ a (hAS ha)) w hw.pow_eq_one
    simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X]
    rw [h₁,h₂,hk,sub_self]
  calc
    S.card.choose t = values.card := hv.symm
    _ ≤ (X^k₁-X^k₂ : F[X]).natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ max k₁ k₂ := by simpa using Polynomial.natDegree_sub_le (X^k₁ : F[X]) (X^k₂)

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimalityArithmetic.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

lemma orbit_order_le (s m p : ℕ) [NeZero s] :
    orderOf (m : ZMod s) ≤ Nat.card (residueOrbit s m p) := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  let f : Fin (orderOf (m : ZMod s)) → residueOrbit s m p := fun i =>
    ⟨(m : ZMod s)^i.val, (Submonoid.mem_closure_pair _ _ _).mpr
      ⟨i.val,0,by simp⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact pow_injOn_Iio_orderOf i.isLt j.isLt (congrArg Subtype.val he)
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

lemma orbit_card_le {s m p : ℕ} [Fact s.Prime]
    (hm : (m : ZMod s) ≠ 0) (hp : (p : ZMod s) ≠ 0) :
    Nat.card (residueOrbit s m p) ≤ s-1 := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  have hn : ∀ x : residueOrbit s m p, x.val ≠ 0 := by
    intro x
    obtain ⟨u,v,huv⟩ := residueOrbit_rep x
    rw [← huv]
    exact_mod_cast mul_ne_zero (pow_ne_zero u hm) (pow_ne_zero v hp)
  let f : residueOrbit s m p → (ZMod s)ˣ := fun x => Units.mk0 x.val (hn x)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Units.val hxy
  simpa [Nat.card_eq_fintype_card, Nat.totient_prime (Fact.out : s.Prime)] using Fintype.card_le_of_injective f hf

/-- Pigeonhole collision in the square of side floor(sqrt |H|)+1. -/
lemma orbit_collision (s m p : ℕ) [NeZero s] :
    ∃ u v u' v' : ℕ,
      u ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      v ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      u' ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      v' ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      (u,v) ≠ (u',v') ∧
      ((m^u*p^v : ℕ) : ZMod s) = ((m^u'*p^v' : ℕ) : ZMod s) := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  let q := Nat.sqrt (Nat.card (residueOrbit s m p))
  let f : Fin (q+1) × Fin (q+1) → residueOrbit s m p := fun x =>
    ⟨(m : ZMod s)^x.1.val*(p : ZMod s)^x.2.val,
      (Submonoid.mem_closure_pair _ _ _).mpr ⟨x.1.val,x.2.val,rfl⟩⟩
  have hb : Fintype.card (residueOrbit s m p) <
      Fintype.card (Fin (q+1) × Fin (q+1)) := by
    simpa [Fintype.card_prod, Nat.card_eq_fintype_card, q] using
      Nat.lt_succ_sqrt (Nat.card (residueOrbit s m p))
  obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hb
  refine ⟨a.1.val,a.2.val,b.1.val,b.2.val,
    Nat.le_of_lt_succ a.1.isLt,Nat.le_of_lt_succ a.2.isLt,
    Nat.le_of_lt_succ b.1.isLt,Nat.le_of_lt_succ b.2.isLt,?_,?_⟩
  · intro h
    apply hab
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact Fin.ext (congrArg Prod.snd h)
  · simpa [f] using congrArg Subtype.val he

lemma prime_factorization_positive {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime)
    (hqm : q ∣ m) : 0 < m.factorization q := by
  exact hq.factorization_pos_of_dvd hm hqm

/-- Distinct exponent pairs represent distinct natural numbers, using the other
prime divisor of m. This is where the perfect-power test is essential. -/
lemma exponent_pair_injective {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hqm : q ∣ m) (hpq : p ≠ q) :
    Function.Injective (fun uv : ℕ × ℕ => m^uv.1*p^uv.2) := by
  intro a b hab
  dsimp at hab
  have hfac := congrArg (fun k : ℕ => k.factorization q) hab
  have hpq0 : p.factorization q = 0 := by
    rw [hp.factorization]
    simp [hpq]
  simp only [Nat.factorization_mul (pow_ne_zero _ hm) (pow_ne_zero _ hp.ne_zero),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hpq0, mul_zero, add_zero] at hfac
  have hu : a.1 = b.1 := Nat.mul_right_cancel (prime_factorization_positive hm hq hqm) hfac
  have hv : a.2 = b.2 := by
    rw [hu] at hab
    have h := Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hm) _) hab
    exact Nat.pow_right_injective hp.two_le h
  exact Prod.ext hu hv

lemma exponent_bound {m p q u v : ℕ} (hm : 1 ≤ m) (hp : p ≤ m)
    (hu : u ≤ q) (hv : v ≤ q) : m^u*p^v ≤ m^(2*q) := by
  calc
    m^u*p^v ≤ m^q*m^q := Nat.mul_le_mul (Nat.pow_le_pow_right hm hu)
      ((Nat.pow_le_pow_left hp v).trans (Nat.pow_le_pow_right hm hv))
    _ = m^(2*q) := by rw [← pow_add]; congr 1; omega

/-- Elementary combinatorial bound used in the appendix. Pair the descending
factors M-i with c*(t-i), so no real logarithms or asymptotics are assumed. -/
lemma power_le_choose_mul {c s t : ℕ} (ht : t ≤ s) :
    c^t ≤ (c*s).choose t := by
  have hd : c^t * t.factorial ≤ (c*s).descFactorial t := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_prod_range]
    calc
      c^t * ∏ i ∈ Finset.range t, (t-i) =
          ∏ i ∈ Finset.range t, c*(t-i) := by simp [Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ Finset.range t, (c*s-i) := by
        apply Finset.prod_le_prod'
        intro i hi
        have hi' := Finset.mem_range.mp hi
        by_cases hc : c = 0
        · simp [hc]
        · have hc' : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc
          rw [Nat.mul_sub_left_distrib]
          have hct : c*t ≤ c*s := Nat.mul_le_mul_left c ht
          have hci : i ≤ c*i := Nat.le_mul_of_pos_left i (by omega)
          omega
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hd
  exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_comm] using hd) (Nat.factorial_pos t)

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimalityCorrectness.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The actual first rejection test in the appendix. -/
def PerfectPower (m : ℕ) : Prop := ∃ b e : ℕ, 2 ≤ b ∧ 2 ≤ e ∧ b^e = m

lemma other_prime_divisor {m p : ℕ} (_hm : 2 ≤ m) (hcom : ¬ m.Prime)
    (hpow : ¬ PerfectPower m) (hp : p.Prime) (hpm : p ∣ m) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ p ≠ q := by
  by_contra hn
  have hu : IsPrimePow m := isPrimePow_iff_unique_prime_dvd.mpr
    ⟨p, ⟨hp,hpm⟩, fun q hq => by
      by_contra he
      exact hn ⟨q,hq.1,hq.2,Ne.symm he⟩⟩
  obtain ⟨q,e,hq,he,hqe⟩ := (isPrimePow_nat_iff m).mp hu
  have he2 : 2 ≤ e := by
    by_contra h
    have : e = 1 := by omega
    subst e
    simp only [pow_one] at hqe
    exact hcom (hqe ▸ hq)
  exact hpow ⟨q,e,hq.two_le,he2,hqe⟩

lemma sqrt_exponent_lt {n h : ℕ} (hn : 3 ≤ n) (hh : n^2 < h) :
    n * Nat.sqrt h < h := by
  have hsq := Nat.sqrt_le h
  have hnl : n ≤ Nat.sqrt h := Nat.le_sqrt'.mpr hh.le
  by_cases he : n = Nat.sqrt h
  · rw [← he]
    simpa [pow_two] using hh
  · have hlt : n < Nat.sqrt h := by omega
    have hpos : 0 < Nat.sqrt h := by omega
    calc
      n * Nat.sqrt h < Nat.sqrt h * Nat.sqrt h := Nat.mul_lt_mul_of_pos_right hlt hpos
      _ ≤ h := hsq

lemma upper_lt_lower {n m h : ℕ} (hn : 3 ≤ n) (hm : m < 2^n) (hh : n^2 < h) :
    m^(2*Nat.sqrt h) < 8^(h-1) := by
  have hnh := sqrt_exponent_lt hn hh
  have h3 : 3 < h := by nlinarith
  have hqpos : 0 < 2*Nat.sqrt h := by
    have := (Nat.sqrt_pos.mpr (show 0 < h by omega)); omega
  calc
    m^(2*Nat.sqrt h) < (2^n)^(2*Nat.sqrt h) := Nat.pow_lt_pow_left hm (by omega)
    _ = 2^(2*(n*Nat.sqrt h)) := by rw [← pow_mul]; congr 1; ring
    _ < 2^(2*h) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ < 2^(3*(h-1)) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ = 8^(h-1) := by rw [pow_mul]; norm_num

/-- This is the appendix's entire root-count contradiction, over an arbitrary
characteristic-p extension with a primitive s-th root. -/
lemma root_count_contradiction {F : Type*} [Field F] {n m s p q : ℕ}
    [Fact s.Prime] [Fact p.Prime] [CharP F p]
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    (hms : (m : ZMod s) ≠ 0) (hps : (p : ZMod s) ≠ 0)
    (hpbig : 8*s < p) (hpm : p ∣ m) (hq : q.Prime) (hqm : q ∣ m) (hpq : p ≠ q)
    (horder : n^2 < orderOf (m : ZMod s))
    {w : F} (hw : IsPrimitiveRoot w s)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s → Introspective s m (X+C (a : F))) : False := by
  classical
  let S : Finset F := (Finset.Icc 1 (8*s)).image (fun a : ℕ => -(a : F))
  have hScard : S.card = 8*s := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb he
      apply CharP.natCast_injOn_Iio F p
      · exact lt_of_le_of_lt (Finset.mem_Icc.mp ha).2 hpbig
      · exact lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hpbig
      · exact neg_injective he
  have hSm : ∀ a ∈ S, Introspective s m (X-C a) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    simpa using htest b (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
  have hSp : ∀ a ∈ S, Introspective s p (X-C a) := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    simpa using (linear_frobenius (F := F) p s b)
  let h := Nat.card (residueOrbit s m p)
  have hlarge : n^2 < h := horder.trans_le (orbit_order_le s m p)
  have hsmall : h ≤ s-1 := orbit_card_le hms hps
  obtain ⟨u,v,u',v',hu,hv,hu',hv',hne,hcon⟩ := orbit_collision s m p
  have hne' : m^u*p^v ≠ m^u'*p^v' :=
    fun he => hne (exponent_pair_injective (by omega) Fact.out hq hqm hpq he)
  have hew : w^(m^u*p^v) = w^(m^u'*p^v') := by
    conv_lhs => rw [pow_eq_pow_mod _ hw.pow_eq_one]
    conv_rhs => rw [pow_eq_pow_mod _ hw.pow_eq_one]
    congr 1
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcon
  have hc := subset_count_le_collision hw S (t := h-1) (by change h-1 < h; omega)
    hSm hSp (fun a ha => ((hSm a ha).pow_exp u).mul_exp ((hSp a ha).pow_exp v))
    (fun a ha => ((hSm a ha).pow_exp u').mul_exp ((hSp a ha).pow_exp v')) hew hne'
  rw [hScard] at hc
  have hpmle : p ≤ m := Nat.le_of_dvd (by omega) hpm
  have hupp : max (m^u*p^v) (m^u'*p^v') ≤ m^(2*Nat.sqrt h) :=
    max_le (exponent_bound (by omega) hpmle hu hv)
      (exponent_bound (by omega) hpmle hu' hv')
  have hlow : 8^(h-1) ≤ (8*s).choose (h-1) := power_le_choose_mul (by omega)
  exact (not_lt_of_ge (hlow.trans (hc.trans hupp))) (upper_lt_lower hn hmb hlarge)

/-- The source congruence test, represented without an assumed polynomial
identity or an assumed primality oracle. -/
def CongruenceTest (m s a : ℕ) : Prop :=
  (X^s-1 : (ZMod m)[X]) ∣ (X+C (a : ZMod m))^m - (X^m+C (a : ZMod m))

lemma congruenceTest_to_introspective {F : Type*} [Field F] {m s p a : ℕ}
    [CharP F p] (hpm : p ∣ m) (ht : CongruenceTest m s a) :
    Introspective s m (X+C (a : F)) := by
  apply introspective_of_congruence
  have h := Polynomial.map_dvd (ZMod.castHom hpm F) ht
  simpa [CongruenceTest, Polynomial.add_comp] using h

/-- Soundness of the accepting, large-input branch of the exact appendix test.
The small branch is literal trial division. -/
theorem large_branch_prime {n m s : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    (hs : s.Prime) (hcop : s.Coprime m) (horder : n^2 < orderOf (m : ZMod s))
    (hpow : ¬ PerfectPower m)
    (hsmall : ∀ d : ℕ, 2 ≤ d → d ≤ 8*s → ¬ d ∣ m)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s → CongruenceTest m s a) : m.Prime := by
  by_contra hcom
  obtain ⟨p,hp,hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  obtain ⟨q,hq,hqm,hpq⟩ := other_prime_divisor hm hcom hpow hp hpm
  let : Fact s.Prime := ⟨hs⟩
  let : Fact p.Prime := ⟨hp⟩
  have hpbig : 8*s < p := by
    by_contra h
    exact hsmall p hp.two_le (by omega) hpm
  have hms : (m : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hs.coprime_iff_not_dvd).mp hcop
  have hps : (p : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hs hp).mp hd
    nlinarith [hs.two_le]
  have hsp : (s : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hs.pos (by nlinarith)
  let : NeZero (s : ZMod p) := ⟨hsp⟩
  obtain ⟨w,hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod p)) s
  exact root_count_contradiction (by omega) hm hmb hms hps hpbig hpm hq hqm hpq horder hw
    (fun a ha hb => congruenceTest_to_introspective hpm (htest a ha hb))

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicAlgebra.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- Exactly s coefficients with cyclic convolution, the concrete algebra
(Z/mZ)[X]/(X^s-1) used in the appendix. -/
abbrev Cyclic (R : Type*) [Semiring R] (s : ℕ) := AddMonoidAlgebra R (Fin s)

noncomputable def cyclicOf {R : Type*} [Semiring R] {s : ℕ} (v : Fin s → R) : Cyclic R s :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm v)

@[simp] lemma cyclicOf_coeff {R : Type*} [Semiring R] {s : ℕ} (v : Fin s → R) (i : Fin s) :
    (cyclicOf v).coeff i = v i := rfl

lemma cyclic_mul_coeff {R : Type*} [Semiring R] {s : ℕ} [NeZero s]
    (a b : Cyclic R s) (k : Fin s) :
    (a*b).coeff k = ∑ i : Fin s, a.coeff i * b.coeff (k-i) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum_fintype]
  · congr 1
    ext i
    rw [sub_eq_add_neg,add_comm k]
  · intro i
    simp

/-- The residue class of X. No exponentially long polynomial is constructed. -/
noncomputable def cyclicX {R : Type*} [Semiring R] (s : ℕ) [NeZero s] : Cyclic R s :=
  AddMonoidAlgebra.single 1 1

noncomputable def cyclicC {R : Type*} [Semiring R] (s : ℕ) [NeZero s] (a : R) : Cyclic R s :=
  AddMonoidAlgebra.single 0 a

lemma cyclicC_nat {R : Type*} [Semiring R] (s : ℕ) [NeZero s] (a : ℕ) :
    cyclicC s (a : R) = (a : Cyclic R s) := by
  induction a with
  | zero => simp [cyclicC]
  | succ a ih =>
    rw [Nat.cast_succ,Nat.cast_succ,← ih]
    simp [cyclicC,AddMonoidAlgebra.single_add,AddMonoidAlgebra.one_def]

/-- Primes satisfy the literal cyclic-array test by characteristic-p Frobenius. -/
lemma cyclic_prime_test {m s : ℕ} [NeZero s] (hm : m.Prime) (a : ℕ) :
    (cyclicX (R := ZMod m) s + cyclicC s (a : ZMod m))^m =
      cyclicX s ^m + cyclicC s (a : ZMod m) := by
  let : Fact m.Prime := ⟨hm⟩
  let : CharP (Cyclic (ZMod m) s) m :=
    charP_of_injective_ringHom (f := AddMonoidAlgebra.singleZeroRingHom)
      AddMonoidAlgebra.single_right_injective m
  rw [cyclicC_nat,add_pow_char,natCast_frobenius]

noncomputable def rootPower {F : Type*} [CommRing F] {s : ℕ} [NeZero s]
    (z : F) (hz : z^s=1) : Multiplicative (Fin s) →* F where
  toFun i := z^i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change z^((i.toAdd+j.toAdd).val)=z^i.toAdd.val*z^j.toAdd.val
    rw [Fin.val_add,← pow_eq_pow_mod _ hz,pow_add]

noncomputable def cyclicEval {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (f : R →+* F) (z : F) (hz : z^s=1) : Cyclic R s →+* F :=
  AddMonoidAlgebra.liftNCRingHom f (rootPower z hz) (fun _ _ => Commute.all _ _)

lemma cyclicEval_X {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (hs : 2 ≤ s) (f : R →+* F) (z : F) (hz : z^s=1) :
    cyclicEval f z hz (cyclicX s) = z := by
  simp [cyclicEval,cyclicX,rootPower, Nat.mod_eq_of_lt (by omega : 1 < s)]

lemma cyclicEval_C {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (f : R →+* F) (z : F) (hz : z^s=1) (a : R) :
    cyclicEval f z hz (cyclicC s a) = f a := by
  simp [cyclicEval,cyclicC,rootPower]

/-- Equality of the two concrete coefficient arrays gives exactly the
introspective identity needed by the appendix's root-count contradiction. -/
lemma cyclic_test_introspective {F : Type*} [Field F] {m s p a : ℕ}
    [NeZero s] [CharP F p] (hs : 2 ≤ s) (hpm : p ∣ m)
    (h : (cyclicX (R := ZMod m) s + cyclicC s (a : ZMod m))^m =
      cyclicX s ^m + cyclicC s (a : ZMod m)) :
    Introspective s m (Polynomial.X+Polynomial.C (a : F)) := by
  intro z hz
  have hh := congrArg (cyclicEval (ZMod.castHom hpm F) z hz) h
  simpa only [map_pow,map_add,cyclicEval_X hs,cyclicEval_C,map_natCast,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_natCast] using hh

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicPrimality.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality

theorem cyclic_large_branch_prime {n m s : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    [NeZero s] (hs : s.Prime) (hcop : s.Coprime m) (horder : n^2 < orderOf (m : ZMod s))
    (hpow : ¬ PerfectPower m)
    (hsmall : ∀ d : ℕ, 2 ≤ d → d ≤ 8*s → ¬ d ∣ m)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s →
      (cyclicX (R := ZMod m) s+cyclicC s (a : ZMod m))^m=
        cyclicX s^m+cyclicC s (a : ZMod m)) : m.Prime := by
  by_contra hcom
  obtain ⟨p,hp,hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  obtain ⟨q,hq,hqm,hpq⟩ := other_prime_divisor hm hcom hpow hp hpm
  let : Fact s.Prime := ⟨hs⟩
  let : Fact p.Prime := ⟨hp⟩
  have hpbig : 8*s < p := by
    by_contra h
    exact hsmall p hp.two_le (by omega) hpm
  have hms : (m : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hs.coprime_iff_not_dvd).mp hcop
  have hps : (p : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hs hp).mp hd
    nlinarith [hs.two_le]
  have hsp : (s : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hs.pos (by nlinarith)
  let : NeZero (s : ZMod p) := ⟨hsp⟩
  obtain ⟨w,hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod p)) s
  exact root_count_contradiction (by omega) hm hmb hms hps hpbig hpm hq hqm hpq horder hw
    (fun a ha hb => cyclic_test_introspective hs.two_le hpm (htest a ha hb))


end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AKSCriteria.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.Primality

lemma prime_not_perfectPower {m : ℕ} (hm : m.Prime) : ¬ PerfectPower m := by
  rintro ⟨b,e,hb,he,h⟩
  have hd : b ∣ m := by rw [← h]; exact dvd_pow_self b (by omega)
  have hbm : b=m := (hm.eq_one_or_self_of_dvd b hd).resolve_left (by omega)
  subst b
  have hlt : m < m^e := by
    simpa using Nat.pow_lt_pow_right (by omega : 1 < m) (by omega : 1 < e)
  omega

lemma order_tests_iff {m s k : ℕ} (hs : s.Prime) (hcop : s.Coprime m) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → m^j%s ≠ 1) ↔ k < orderOf (m : ZMod s) := by
  let : Fact s.Prime := ⟨hs⟩
  have ho : 0 < orderOf (m : ZMod s) :=
    ((ZMod.isUnit_iff_coprime m s).mpr hcop.symm).isOfFinOrder.orderOf_pos
  have hp (j : ℕ) : m^j%s=1 ↔ (m : ZMod s)^j=1 := by
    constructor
    · intro h
      have : ((m^j%s : ℕ) : ZMod s)=(1 : ZMod s) := by
        simpa only [Nat.cast_one] using congrArg (fun a : ℕ => (a : ZMod s)) h
      simpa only [ZMod.natCast_mod,Nat.cast_pow,Nat.cast_one] using this
    · intro h
      have := congrArg ZMod.val h
      simpa only [← Nat.cast_pow,ZMod.val_natCast,ZMod.val_one] using this
  constructor
  · intro h
    by_contra hn
    exact h _ ho (by omega) ((hp _).mpr (pow_orderOf_eq_one (m : ZMod s)))
  · intro h j hj hk hh
    exact pow_ne_one_of_lt_orderOf (by omega) (hk.trans_lt h) ((hp j).mp hh)

lemma prime_of_no_small_divisor {m B : ℕ} (hm : 2 ≤ m) (hb : m ≤ B)
    (h : ∀ d : ℕ, 2 ≤ d → d ≤ B → d < m → ¬ d ∣ m) : m.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hm,?_⟩
  intro d hd hdm
  by_contra hne
  have hd2 : 2 ≤ d := by
    by_contra hn
    have : d=0 := by omega
    subst d
    simp only [Nat.zero_dvd] at hdm
    omega
  exact h d hd2 (by omega) hd hdm

end ExactQuantumFactoring.Primality


end

end OAI


