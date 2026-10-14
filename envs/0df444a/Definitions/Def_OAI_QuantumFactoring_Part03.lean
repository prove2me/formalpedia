-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part03
-- name    : OAI_QuantumFactoring_Part03
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T06:58:41.49986+00:00
-- url     : https://prove2.me/theorems/89b6a8c3-fa35-42f7-be59-0ac3ad79c627
-- title:
--   Exact quantum factoring, part 3 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 3 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `TriangularAlgebra`, `HornerEncoding`, `RegisterCircuit`, `RegisterBasis`, `EncodedStates`, `RegisterEncoded`, `BooleanOracle`, `OracleLayout`, `PackedPrograms`, `PackedEncoding`, `CoherentSampling`, `AppendRegister`, `ControlledTranslation`, `RowNetwork`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TriangularAlgebra.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/HornerEncoding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RegisterCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RegisterBasis.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/EncodedStates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RegisterEncoded.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanOracle.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OracleLayout.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PackedPrograms.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PackedEncoding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CoherentSampling.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AppendRegister.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ControlledTranslation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RowNetwork.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 3 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: TriangularAlgebra.lean, HornerEncoding.lean, RegisterCircuit.lean, RegisterBasis.lean, EncodedStates.lean, RegisterEncoded.lean, BooleanOracle.lean, OracleLayout.lean, PackedPrograms.lean, PackedEncoding.lean, CoherentSampling.lean, AppendRegister.lean, ControlledTranslation.lean, RowNetwork.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part02

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularAlgebra.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

lemma pathShift_prefix {A : Type*} [AddCommGroup A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) (k : ℕ) (hk : k ≤ b) :
    pathShift δ x y k hk =
      ∑ j : Fin k, δ (j.castLE hk) (hybrid x y (j.val+1)) := by
  induction k with
  | zero => simp [pathShift]
  | succ k ih =>
    rw [pathShift, ih (by omega), Fin.sum_univ_castSucc]
    rfl

lemma pathShift_full_sum {A : Type*} [AddCommGroup A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) :
    pathShift δ x y b le_rfl = ∑ j : Fin b, δ j (hybrid x y (j.val+1)) := by
  rw [pathShift_prefix]
  rfl

lemma pathWeight_prefix {b : ℕ} (x y : Bits b) (k : ℕ) (hk : k ≤ b) :
    pathWeight x y k hk = ∏ j : Fin k, hEntry (x (j.castLE hk)) (y (j.castLE hk)) := by
  induction k with
  | zero => simp [pathWeight]
  | succ k ih => rw [pathWeight, ih (by omega), Fin.prod_univ_castSucc]; rfl

def dot {b : ℕ} (x y : Bits b) : ℕ := ∑ i : Fin b, (x i).toNat*(y i).toNat

lemma hEntry_pow (a c : Bool) :
    hEntry a c = (-1:ℂ)^(a.toNat*c.toNat) * (Real.sqrt 2 : ℂ)⁻¹ := by
  cases a <;> cases c <;> simp [hEntry, div_eq_mul_inv]

lemma pathWeight_full {b : ℕ} (x y : Bits b) :
    pathWeight x y b le_rfl = (-1:ℂ)^dot x y * (Real.sqrt 2 : ℂ)⁻¹^b := by
  rw [pathWeight_prefix]
  simp only [hEntry_pow, Fin.castLE_refl, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma selected_evolve {A : Type*} [AddCommGroup A] [Fintype A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ) :
    (∑ z, star (χ z) * evolve δ x χ b le_rfl y z) =
      pathWeight x y b le_rfl *
        ∑ z, star (χ (z+pathShift δ x y b le_rfl)) * χ z := by
  simp only [evolve_full]
  calc
    _ = pathWeight x y b le_rfl * ∑ z, star (χ z) * χ (z-pathShift δ x y b le_rfl) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      congr 1
      symm
      simpa only [Equiv.coe_addRight, add_sub_cancel_right] using
        Equiv.sum_comp (Equiv.addRight (pathShift δ x y b le_rfl))
          (fun z => star (χ z) * χ (z-pathShift δ x y b le_rfl))

/-- The input word is reversed physically, while the output wire j is k_j. -/
def inputNumber {b : ℕ} (x : Bits b) : ℕ := ∑ i, 2^(b-1-i.val)*(x i).toNat
def outputNumber {b : ℕ} (y : Bits b) : ℕ := ∑ j, 2^j.val*(y j).toNat

def lowTerm {b : ℕ} (x y : Bits b) (i j : Fin b) : ℕ :=
  if j.val < i.val then 2^(b-1-i.val+j.val)*(x i).toNat*(y j).toNat else 0

def highTerm {b : ℕ} (x y : Bits b) (i j : Fin b) : ℕ :=
  if i.val < j.val then 2^(j.val-i.val-1)*(x i).toNat*(y j).toNat else 0

lemma productTerm {b : ℕ} (x y : Bits b) (i j : Fin b) :
    (2^(b-1-i.val)*(x i).toNat) * (2^j.val*(y j).toNat) =
      lowTerm x y i j +
        (if i=j then 2^(b-1)*(x i).toNat*(y i).toNat else 0) +
          2^b*highTerm x y i j := by
  have he : (2^(b-1-i.val)*(x i).toNat) * (2^j.val*(y j).toNat) =
      2^(b-1-i.val+j.val)*(x i).toNat*(y j).toNat := by rw [pow_add]; ring
  rw [he]
  by_cases hij : i.val < j.val
  · have hn : i ≠ j := by intro h; subst j; omega
    have hw : b-1-i.val+j.val = b+(j.val-i.val-1) := by have := i.isLt; omega
    simp only [lowTerm, highTerm, ite_eq_right (by omega : ¬j.val < i.val), ite_eq_left hij,
      ite_eq_right hn, hw, pow_add]
    ring
  · by_cases hji : j.val < i.val
    · have hn : i ≠ j := by intro h; subst j; omega
      simp [lowTerm, highTerm, hij, hji, hn]
    · have heq : i=j := Fin.ext (by omega)
      subst j
      have hw : b-1-i.val+i.val = b-1 := by have := i.isLt; omega
      simp [lowTerm, highTerm, hw]

lemma product_decomposition {b : ℕ} (x y : Bits b) :
    inputNumber x * outputNumber y =
      (∑ i, ∑ j, lowTerm x y i j) + 2^(b-1)*dot x y +
        2^b*(∑ i, ∑ j, highTerm x y i j) := by
  unfold inputNumber outputNumber
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, productTerm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [dot, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One shift after H_j combines all the prescribed mutually commuting
controlled power-of-two shifts in that row. -/
def rowShift {b : ℕ} (j : Fin b) (z : Bits b) : ℕ :=
  ∑ i, if j.val < i.val then 2^(b-1-i.val+j.val)*(z i).toNat*(z j).toNat else 0

lemma rowShift_hybrid {b : ℕ} (x y : Bits b) (j : Fin b) :
    rowShift j (hybrid x y (j.val+1)) = ∑ i, lowTerm x y i j := by
  unfold rowShift
  apply Finset.sum_congr rfl
  intro i _
  unfold lowTerm
  by_cases hi : j.val < i.val
  · simp [hi, hybrid, show ¬i.val < j.val+1 by omega]
  · simp [hi]

lemma pathShift_rows {A : Type*} [Ring A]
    {b : ℕ} (x y : Bits b) :
    pathShift (fun j z => (rowShift j z : A)) x y b le_rfl =
      ((∑ i, ∑ j, lowTerm x y i j : ℕ) : A) := by
  rw [pathShift_full_sum]
  simp only [rowShift_hybrid, Nat.cast_sum]
  exact Finset.sum_comm

end ExactQuantumFactoring.Triangular


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/HornerEncoding.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

namespace BitArithmetic

lemma horner_sum {b : ℕ} (e : Basis b) (k : ℕ) (hk : k ≤ b) :
    horner e k hk = ∑ i : Fin k, 2^(k-1-i.val)*(e (i.castLE hk)).toNat := by
  induction k with
  | zero => simp [horner]
  | succ k ih =>
    rw [horner,ih (by omega),Fin.sum_univ_castSucc,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have he : k+1-1-i.val = (k-1-i.val)+1 := by have := i.isLt; omega
      rw [show (i.castSucc : Fin (k+1)).val = i.val from rfl,he,pow_succ]
      have hi : ((i.castSucc).castLE hk) = i.castLE (by omega : k ≤ b) := Fin.ext rfl
      rw [hi]
      ring
    · simp only [Fin.val_last,Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_mul]
      rfl

lemma horner_full {b : ℕ} (e : Basis b) :
    horner e b le_rfl = Triangular.inputNumber e := by
  rw [horner_sum]
  rfl

end BitArithmetic

lemma Triangular.outputNumber_value {b : ℕ} (x : Basis b) :
    outputNumber x = (bitsValue x).toNat := (bitsValue_toNat x).symm

/-- The physical input word reversal is an explicit wire permutation. -/
def reverseBits (b : ℕ) : Equiv.Perm (Basis b) where
  toFun x := x ∘ Fin.rev
  invFun x := x ∘ Fin.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma Triangular.inputNumber_reverse {b : ℕ} (x : Basis b) :
    inputNumber x = (bitsValue (reverseBits b x)).toNat := by
  rw [bitsValue_toNat]
  unfold inputNumber
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin b))]
  apply Finset.sum_congr rfl
  intro i _
  change 2^(b-1-(b-(i.val+1)))*(x (Fin.rev i)).toNat =
    2^i.val*(x (Fin.rev i)).toNat
  have he : b-1-(b-(i.val+1)) = i.val := by have := i.isLt; omega
  rw [he]

lemma Triangular.inputNumber_lt {b : ℕ} (x : Basis b) : inputNumber x < 2^b := by
  rw [inputNumber_reverse]
  exact (bitsValue _).isLt

lemma Triangular.inputNumber_bijective (b : ℕ) :
    Function.Bijective (fun x : Basis b =>
      (⟨inputNumber x,inputNumber_lt x⟩ : Fin (2^b))) := by
  have h := (bitsEquiv b).bijective.comp (reverseBits b).bijective
  have he : (fun x : Basis b => (⟨inputNumber x,inputNumber_lt x⟩ : Fin (2^b))) =
    fun x => ((bitsEquiv b (reverseBits b x)).toFin) := by
    funext x
    apply Fin.ext
    exact inputNumber_reverse x
  rw [he]
  exact (BitVec.equivFin (m := b)).bijective.comp h

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RegisterCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

/-- A physical placement of a register uses distinct existing qubits. -/
abbrev Register (p q : ℕ) := Fin p ↪ Fin q

namespace Register

abbrev Unused {p q : ℕ} (w : Register p q) := {i : Fin q // ∀ j, w j ≠ i}

noncomputable def split {p q : ℕ} (w : Register p q) :
    Basis q ≃ Basis p × (w.Unused → Bool) := by
  classical
  exact {
    toFun := fun x => (x ∘ w, fun i => x i.val)
    invFun := fun x i => if h : ∃ j, w j = i then x.1 h.choose
      else x.2 ⟨i, by simpa only [not_exists] using h⟩
    left_inv := by
      intro x; funext i; dsimp
      split_ifs with h
      · simp only [h.choose_spec]
      · rfl
    right_inv := by
      intro x; apply Prod.ext
      · funext j; dsimp
        have h : ∃ j', w j' = w j := ⟨j,rfl⟩
        rw [dite_eq_left h]
        exact congrArg x.1 (w.injective h.choose_spec)
      · funext i; dsimp
        rw [dite_eq_right (by simpa only [not_exists] using i.property)] }

noncomputable def liftMatrix {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) : Matrix (Basis q) (Basis q) ℂ :=
  Matrix.reindex w.split.symm w.split.symm
    (A ⊗ₖ (1 : Matrix (w.Unused → Bool) (w.Unused → Bool) ℂ))

lemma liftMatrix_one {p q : ℕ} (w : Register p q) : w.liftMatrix 1 = 1 := by
  classical
  rw [liftMatrix, Matrix.one_kronecker_one]
  exact map_one (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)

lemma liftMatrix_mul {p q : ℕ} (w : Register p q)
    (A B : Matrix (Basis p) (Basis p) ℂ) :
    w.liftMatrix (A * B) = w.liftMatrix A * w.liftMatrix B := by
  classical
  change (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)
    ((A * B) ⊗ₖ (1 : Matrix (w.Unused → Bool) (w.Unused → Bool) ℂ)) =
    (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm) (A ⊗ₖ 1) *
    (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm) (B ⊗ₖ 1)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)]
  congr 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

lemma liftMatrix_unitary {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) (hA : A ∈ Matrix.unitaryGroup (Basis p) ℂ) :
    w.liftMatrix A ∈ Matrix.unitaryGroup (Basis q) ℂ :=
  unitary_reindex _ _ (tensor_unitary _ _ hA (one_mem _))

end Register

def Instruction.place {p q : ℕ} (w : Register p q) (o : Instruction p) : Instruction q :=
  ⟨o.gate, w ∘ o.wire, w.injective.comp o.distinct⟩

lemma Instruction.place_matrix {p q : ℕ} (w : Register p q) (o : Instruction p) :
    (o.place w).matrix = w.liftMatrix o.matrix := by
  classical
  ext x y
  let A := ∀ i : Fin q, (∀ j, w (o.wire j) ≠ i) → x i = y i
  let B := ∀ i : Fin p, (∀ j, o.wire j ≠ i) → x (w i) = y (w i)
  let C := (fun i : w.Unused => x i.val) = (fun i : w.Unused => y i.val)
  have he : A ↔ B ∧ C := by
    constructor
    · intro h
      constructor
      · intro i hi
        apply h (w i)
        intro j hh
        exact hi j (w.injective hh)
      · funext i
        apply h i.val
        intro j
        exact i.property (o.wire j)
    · rintro ⟨hB,hC⟩ i hi
      by_cases hh : ∃ j, w j = i
      · obtain ⟨j,rfl⟩ := hh
        exact hB j (fun k hk => hi k (congrArg w hk))
      · exact congrFun hC ⟨i,by simpa only [not_exists] using hh⟩
  change (if A then o.gate.matrix (List.ofFn (x ∘ w ∘ o.wire))
      (List.ofFn (y ∘ w ∘ o.wire)) else 0) =
      (if B then o.gate.matrix (List.ofFn (x ∘ w ∘ o.wire))
        (List.ofFn (y ∘ w ∘ o.wire)) else 0) * if C then 1 else 0
  simp only [he]
  split_ifs <;> simp_all

lemma programMatrix_place {p q : ℕ} (w : Register p q) (ops : List (Instruction p)) :
    programMatrix (ops.map (Instruction.place w)) = w.liftMatrix (programMatrix ops) := by
  induction ops with
  | nil => simp [programMatrix_nil, Register.liftMatrix_one]
  | cons o ops ih =>
    rw [List.map_cons, programMatrix_cons, programMatrix_cons, ih,
      Instruction.place_matrix, Register.liftMatrix_mul]

/-- Tensor states in the actual physical wire order. -/
noncomputable def Register.pairState {p q : ℕ} (w : Register p q)
    (v : State p) (z : (w.Unused → Bool) → ℂ) : State q :=
  fun x => v (w.split x).1 * z (w.split x).2

lemma Register.liftMatrix_pairState {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) (v : State p) (z : (w.Unused → Bool) → ℂ) :
    (w.liftMatrix A).mulVec (w.pairState v z) = w.pairState (A.mulVec v) z := by
  classical
  ext x
  change (∑ y, (A (w.split x).1 (w.split y).1 *
      if (w.split x).2 = (w.split y).2 then 1 else 0) *
      (v (w.split y).1 * z (w.split y).2)) =
    (∑ u, A (w.split x).1 u * v u) * z (w.split x).2
  rw [← Equiv.sum_comp w.split.symm]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp [Finset.sum_mul, mul_assoc]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RegisterBasis.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Replace just one placed register, keeping every other physical wire. -/
noncomputable def Register.replace {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p) : Basis q :=
  w.split.symm (y, (w.split x).2)

lemma Register.replace_inside {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p)
    (i : Fin p) : w.replace x y (w i) = y i := by
  have h := congrArg Prod.fst (w.split.apply_symm_apply (y, (w.split x).2))
  exact congrFun h i

lemma Register.replace_outside {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p)
    (i : w.Unused) : w.replace x y i.val = x i.val := by
  have h := congrArg Prod.snd (w.split.apply_symm_apply (y, (w.split x).2))
  exact congrFun h i

lemma Register.pairState_basis {p q : ℕ} (w : Register p q) (x : Basis q) :
    w.pairState (basisVector (x ∘ w)) (basisVector (w.split x).2) = basisVector x := by
  classical
  funext y
  change (if (w.split y).1 = (w.split x).1 then (1 : ℂ) else 0) *
    (if (w.split y).2 = (w.split x).2 then 1 else 0) = if y = x then 1 else 0
  by_cases hy : y = x
  · subst y; simp
  · have hh : ¬ ((w.split y).1 = (w.split x).1 ∧ (w.split y).2 = (w.split x).2) := by
      intro h; exact hy (w.split.injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp hh with h | h <;> simp [hy,h]

lemma Register.pairState_replace_basis {p q : ℕ} (w : Register p q) (x : Basis q) (v : Basis p) :
    w.pairState (basisVector v) (basisVector (w.split x).2) = basisVector (w.replace x v) := by
  have h := w.pairState_basis (w.replace x v)
  have he : w.split (w.replace x v) = (v, (w.split x).2) := w.split.apply_symm_apply _
  change w.pairState (basisVector (w.split (w.replace x v)).1)
    (basisVector (w.split (w.replace x v)).2) = _ at h
  simpa only [he] using h

lemma placed_basis {p q : ℕ} (w : Register p q) (ops : List (Instruction p))
    (x : Basis q) (v : Basis p)
    (h : (programMatrix ops).mulVec (basisVector (x ∘ w)) = basisVector v) :
    (programMatrix (ops.map (Instruction.place w))).mulVec (basisVector x) =
      basisVector (w.replace x v) := by
  rw [programMatrix_place, ← w.pairState_basis x, w.liftMatrix_pairState, h,
    w.pairState_replace_basis]

/-- SWAP is three named CNOT gates, not an extra primitive. -/
def swapAt {q : ℕ} (a b : Fin q) (h : a ≠ b) : List (Instruction q) :=
  [cnotAt a b h, cnotAt b a h.symm, cnotAt a b h]

lemma swapAt_basis {q : ℕ} (a b : Fin q) (h : a ≠ b) (x : Basis q) :
    (programMatrix (swapAt a b h)).mulVec (basisVector x) =
      basisVector (x ∘ Equiv.swap a b) := by
  rw [swapAt, programMatrix_cons, programMatrix_cons, programMatrix_singleton,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    cnotAt_basis, cnotAt_basis, cnotAt_basis]
  congr 1
  funext i
  by_cases ha : i = a
  · subst i; simp only [Function.comp_apply, Function.update_self,
      Function.update_of_ne h, Function.update_of_ne h.symm, Equiv.swap_apply_left]
    cases x a <;> cases x b <;> rfl
  · by_cases hb : i = b
    · subst i; simp [Function.comp_apply, h, h.symm]
    · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne ha hb,
        Function.update_of_ne ha, Function.update_of_ne hb]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EncodedStates.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- Embed a logical finite state in concrete basis words, including clean work. -/
noncomputable def encodeState {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) : State q := by
  classical
  exact ∑ a, ψ a • basisVector (e a)

lemma encodeState_apply {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) (x : Basis q) :
    encodeState e ψ x = ∑ a, if x=e a then ψ a else 0 := by
  classical
  simp only [encodeState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVector]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma encodeState_at {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e) (ψ : α → ℂ) (a : α) :
    encodeState e ψ (e a) = ψ a := by
  classical
  rw [encodeState_apply]
  simp [he.eq_iff]

lemma encodeState_outside {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) (x : Basis q) (hx : x ∉ Set.range e) :
    encodeState e ψ x = 0 := by
  classical
  rw [encodeState_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [ite_eq_right]
  intro h
  exact hx ⟨a,h.symm⟩

lemma encodeState_basis {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (a : α) : encodeState e (basisVector a) = basisVector (e a) := by
  classical
  simp [encodeState, basisVector, ite_smul]

lemma encodeState_add {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ χ : α → ℂ) :
    encodeState e (ψ+χ) = encodeState e ψ + encodeState e χ := by
  classical
  simp only [encodeState, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma encodeState_smul {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (c : ℂ) (ψ : α → ℂ) :
    encodeState e (c • ψ) = c • encodeState e ψ := by
  classical
  simp only [encodeState, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma encodeState_sum {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}
    (e : α → Basis q) (ψ : β → α → ℂ) :
    encodeState e (∑ b, ψ b) = ∑ b, encodeState e (ψ b) := by
  classical
  simp only [encodeState, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- A basis-level implementation law extends to every coherent superposition. -/
lemma matrix_encodeState {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (e : α → Basis p) (f : β → Basis q) (U : Matrix (Basis q) (Basis p) ℂ)
    (V : Matrix β α ℂ)
    (h : ∀ a, U.mulVec (basisVector (e a)) = encodeState f (fun b => V b a))
    (ψ : α → ℂ) : U.mulVec (encodeState e ψ) = encodeState f (V.mulVec ψ) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]
  simp_rw [← encodeState_smul]
  rw [← encodeState_sum]
  congr 1
  funext b
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma matrix_encode_permutation {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (U : Matrix (Basis q) (Basis q) ℂ) (v : Equiv.Perm α)
    (h : ∀ a, U.mulVec (basisVector (e a)) = basisVector (e (v a)))
    (ψ : α → ℂ) : U.mulVec (encodeState e ψ) = encodeState e (ψ ∘ v.symm) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]
  unfold encodeState
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.sum_comp v (fun a => (ψ ∘ v.symm) a • basisVector (e a))

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RegisterEncoded.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma Register.replace_injective {p q : ℕ} (w : Register p q) (x : Basis q) :
    Function.Injective (w.replace x) := by
  intro u v h
  funext i
  have hh := congrFun h (w i)
  simpa only [Register.replace_inside] using hh

lemma Register.placed_basis_state {p q : ℕ} (w : Register p q)
    (ops : List (Instruction p)) (x : Basis q) :
    (programMatrix (ops.map (Instruction.place w))).mulVec (basisVector x) =
      encodeState (w.replace x) ((programMatrix ops).mulVec (basisVector (x ∘ w))) := by
  classical
  rw [programMatrix_place, ← w.pairState_basis x, w.liftMatrix_pairState]
  unfold encodeState
  simp_rw [← w.pairState_replace_basis]
  funext y
  simp only [Register.pairState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    basisVector]
  simp

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanOracle.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace BoolNet

/-- Only the actual trace, not unrelated output registers, must start at zero. -/
lemma program_eval_range {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) (x : Basis q)
    (hfresh : ∀ i : Fin q, n ≤ i.val → i.val < k → x i = false) :
    (∀ i : Fin k, (BooleanProgram.eval (p.program h) x) (i.castLE h) =
      p.eval (fun j => x (j.castLE (p.input_le.trans h))) i) ∧
    (∀ i : Fin q, k ≤ i.val → (BooleanProgram.eval (p.program h) x) i = x i) := by
  induction p with
  | input => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | @add k p o ih =>
    have hk : k ≤ q := by omega
    obtain ⟨hpre, hrest⟩ := ih hk (fun i hi hik => hfresh i hi (by omega))
    have hy : (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩ = false := by
      rw [hrest _ (by simp)]
      exact hfresh _ p.input_le (by simp)
    have hv : (o.compileOp h).value (BooleanProgram.eval (p.program hk) x) =
        o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk)))) := by
      rw [BoolNode.compileOp_value]
      congr 1
      funext i
      exact hpre i
    have heval : BooleanProgram.eval ((p.add o).program h) x =
        Function.update (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩
          (o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk))))) := by
      simp only [program, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (o.compileOp h).eval (BooleanProgram.eval (p.program hk) x) = _
      rw [BooleanOp.eval_fresh _ _ hy, hv]
      rfl
    rw [heval]
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [eval_add_last]
        exact Function.update_self _ _ _
      · rw [eval_add_castSucc]
        rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change j.val = k at hh; omega)]
        exact hpre j
    · intro i hi
      rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega)]
      exact hrest i (by omega)

end BoolNet

namespace BooleanNetwork

/-- Copy disjoint source wires into a separate target register, by XOR. -/
def copyPrefix {k m : ℕ} (source : Fin m → Fin k) : (t : ℕ) → t ≤ m → BooleanProgram (k+m)
  | 0, _ => []
  | t+1, h => copyPrefix source t (by omega) ++
    [⟨Fin.natAdd k ⟨t, by omega⟩, .copy ((source ⟨t, by omega⟩).castAdd m)
      (by intro he; have hh := congrArg Fin.val he; simp at hh; omega)⟩]

lemma copyPrefix_length {k m : ℕ} (source : Fin m → Fin k) (t : ℕ) (h : t ≤ m) :
    (copyPrefix source t h).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [copyPrefix, ih]

lemma copyPrefix_eval {k m : ℕ} (source : Fin m → Fin k) (t : ℕ) (h : t ≤ m)
    (x : Basis (k+m)) (i : Fin (k+m)) :
    (copyPrefix source t h).eval x i =
      if hi : k ≤ i.val ∧ i.val < k+t then
        Bool.xor (x i) (x ((source ⟨i.val-k, by omega⟩).castAdd m)) else x i := by
  induction t generalizing i with
  | zero => simp [copyPrefix, BooleanProgram.eval]
  | succ t ih =>
    simp only [copyPrefix, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (BooleanOp.copy ((source ⟨t, by omega⟩).castAdd m) _).eval
      ((copyPrefix source t (by omega)).eval x) i = _
    by_cases hit : i.val = k+t
    · have he : i = Fin.natAdd k ⟨t, Nat.lt_of_succ_le h⟩ := Fin.ext hit
      subst i
      rw [BooleanOp.eval_at]
      simp only [BooleanOp.value]
      rw [ih, ih]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      rw [dite_eq_right (by omega), dite_eq_right (by have := (source ⟨t, by omega⟩).isLt; omega),
        dite_eq_left (by omega)]
      simp
    · rw [BooleanOp.eval_away _ _ (by intro he; exact hit (congrArg Fin.val he))]
      rw [ih]
      by_cases hn : k ≤ i.val ∧ i.val < k+t
      · rw [dite_eq_left hn, dite_eq_left (by omega)]
      · rw [dite_eq_right hn, dite_eq_right (by omega)]

/-- Actual fixed-gate compute/copy/uncompute, with all trace wires restored. -/
def oracle {n m : ℕ} (c : BooleanNetwork n m) : List (Instruction (c.width+m)) :=
  let p := c.net.program (Nat.le_add_right c.width m)
  p.compile ++ (copyPrefix c.output m le_rfl).compile ++
    p.compile.reverse.map Instruction.reverse

lemma oracle_length {n m : ℕ} (c : BooleanNetwork n m) :
    c.oracle.length ≤ 4*c.net.count + 2*m := by
  unfold oracle
  simp only [List.length_append, List.length_map, List.length_reverse]
  have hp := c.net.compile_length (Nat.le_add_right c.width m)
  have hc := BooleanProgram.compile_length (copyPrefix c.output m le_rfl)
  rw [copyPrefix_length] at hc
  omega

/-- The basis-state whose trace is zero and whose target is toggled by c(x). -/
def oracleOutput {n m : ℕ} (c : BooleanNetwork n m) (x : Basis (c.width+m)) : Basis (c.width+m) :=
  fun i => if h : c.width ≤ i.val then
    Bool.xor (x i) (c.eval (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _))))
      ⟨i.val-c.width, by omega⟩) else x i

lemma oracle_basis {n m : ℕ} (c : BooleanNetwork n m) (x : Basis (c.width+m))
    (hfresh : ∀ i : Fin (c.width+m), n ≤ i.val → i.val < c.width → x i = false) :
    (programMatrix c.oracle).mulVec (basisVector x) = basisVector (c.oracleOutput x) := by
  let p := c.net.program (Nat.le_add_right c.width m)
  have hx := c.net.program_eval_range (Nat.le_add_right c.width m) x hfresh
  have hout (i : Fin (c.width+m)) (hi : i.val < c.width) : c.oracleOutput x i = x i := by
    simp only [oracleOutput, dite_eq_right (Nat.not_le.mpr hi)]
  have hy := c.net.program_eval_range (Nat.le_add_right c.width m) (c.oracleOutput x)
    (fun i hin hik => (hout i hik).trans (hfresh i hin hik))
  have hin : (fun j : Fin n => c.oracleOutput x
      (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) =
      (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) := by
    funext j
    apply hout
    change j.val < c.width
    exact j.isLt.trans_le c.net.input_le
  rw [hin] at hy
  have he : (copyPrefix c.output m le_rfl).eval (p.eval x) = p.eval (c.oracleOutput x) := by
    funext i
    rw [copyPrefix_eval]
    by_cases hi : c.width ≤ i.val
    · rw [dite_eq_left ⟨hi, i.isLt⟩, hx.2 i hi, hy.2 i hi]
      have hs : p.eval x ((c.output ⟨i.val-c.width, by omega⟩).castAdd m) =
          c.net.eval (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _))))
            (c.output ⟨i.val-c.width, by omega⟩) := hx.1 _
      rw [hs]
      simp only [oracleOutput, dite_eq_left hi, eval, Function.comp_apply]
    · rw [dite_eq_right (by tauto)]
      have hik : i.val < c.width := by omega
      exact (hx.1 ⟨i.val,hik⟩).trans (hy.1 ⟨i.val,hik⟩).symm
  change (programMatrix (p.compile ++ (copyPrefix c.output m le_rfl).compile ++
    p.compile.reverse.map Instruction.reverse)).mulVec (basisVector x) = _
  rw [programMatrix_append, programMatrix_append, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, BooleanProgram.compile_basis, BooleanProgram.compile_basis, he,
    BooleanProgram.uncompute]

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OracleLayout.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

/-- Input, output, then zero work space; this same layout is used by the
classical subroutines inside the coherent controller. -/
def packed {n m : ℕ} (r : ℕ) (x : Basis n) (y : Basis m) : Basis (n+m+r) :=
  fun i => if h : i.val < n then x ⟨i.val,h⟩
    else if h' : i.val < n+m then y ⟨i.val-n,by omega⟩ else false

lemma packed_input {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin n) :
    packed r x y ⟨i.val,by omega⟩ = x i := by simp [packed, i.isLt]

lemma packed_target {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin m) :
    packed r x y ⟨n+i.val,by omega⟩ = y i := by simp [packed, i.isLt]

lemma packed_work {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin (n+m+r))
    (hi : n+m ≤ i.val) : packed r x y i = false := by
  simp [packed, show ¬ i.val<n by omega, show ¬ i.val<n+m by omega]

def oracleIndex (n m width i : ℕ) : ℕ :=
  if i < n then i else if i < width then n+m+(i-n) else n+(i-width)

/-- Place the oracle's retained trace after its output rather than between the
input and output. A larger reservoir of work wires is permitted. -/
def oraclePlacement {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    Register (c.width+m) (n+m+r) where
  toFun i := ⟨oracleIndex n m c.width i.val, by
    have := c.net.width_eq
    have := i.isLt
    unfold oracleIndex
    split_ifs <;> omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have hh : oracleIndex n m c.width i.val = oracleIndex n m c.width j.val :=
      congrArg Fin.val he
    unfold oracleIndex at hh
    split_ifs at hh <;> have hi := i.isLt <;> have hj := j.isLt <;>
      have hn := c.net.input_le <;> omega

lemma oraclePlacement_val {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin (c.width+m)) :
    (oraclePlacement c hr i).val = oracleIndex n m c.width i.val := rfl

lemma oraclePlacement_input {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin n) :
    oraclePlacement c hr (i.castLE (c.net.input_le.trans (Nat.le_add_right _ _))) =
      ⟨i.val,by omega⟩ := by
  apply Fin.ext
  simp [oraclePlacement_val, oracleIndex, i.isLt]

lemma oraclePlacement_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin m) :
    oraclePlacement c hr ⟨c.width+i.val,by omega⟩ = ⟨n+i.val,by omega⟩ := by
  have hn := c.net.input_le
  apply Fin.ext
  simp [oraclePlacement_val, oracleIndex, show ¬c.width+i.val<n by omega]

lemma oraclePlacement_work {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin (c.width+m)) (hin : n ≤ i.val) (hiw : i.val < c.width) :
    n+m ≤ (oraclePlacement c hr i).val := by
  rw [oraclePlacement_val]
  simp only [oracleIndex, ite_eq_right (Nat.not_lt.mpr hin), ite_eq_left hiw]
  omega

def oracleOn {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    List (Instruction (n+m+r)) := c.oracle.map (Instruction.place (oraclePlacement c hr))

lemma oracleOn_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    (oracleOn c hr).length ≤ 4*c.net.count+2*m := by
  simpa [oracleOn] using oracle_length c

lemma oracleOn_basis {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (x : Basis n) (y : Basis m) :
    (programMatrix (oracleOn c hr)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r x (fun i => Bool.xor (y i) (c.eval x i))) := by
  let w := oraclePlacement c hr
  have hz : ∀ i : Fin (c.width+m), n ≤ i.val → i.val < c.width →
      (packed r x y ∘ w) i = false := by
    intro i hin hiw
    exact packed_work x y _ (oraclePlacement_work c hr i hin hiw)
  rw [oracleOn, placed_basis w c.oracle (packed r x y) _ (oracle_basis c _ hz)]
  congr 1
  have heval : (fun j : Fin n => (packed r x y ∘ w)
      (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) = x := by
    funext j
    rw [Function.comp_apply, oraclePlacement_input, packed_input]
  funext i
  by_cases hi : ∃ j, w j = i
  · obtain ⟨j,rfl⟩ := hi
    rw [Register.replace_inside]
    unfold oracleOutput
    rw [heval]
    by_cases hj : c.width ≤ j.val
    · rw [dite_eq_left hj]
      have hw : w j = (⟨n+(j.val-c.width),by have := j.isLt; omega⟩ : Fin (n+m+r)) := by
        apply Fin.ext
        simp only [w, oraclePlacement_val, oracleIndex,
          ite_eq_right (show ¬j.val<n by have := c.net.input_le; omega),
          ite_eq_right (Nat.not_lt.mpr hj)]
      change ((packed r x y) (w j) ^^ c.eval x ⟨j.val-c.width,by omega⟩) = _
      rw [hw, packed_target x y ⟨j.val-c.width,by omega⟩,
        packed_target x (fun i => y i ^^ c.eval x i) ⟨j.val-c.width,by omega⟩]
    · rw [dite_eq_right hj]
      by_cases hn : j.val < n
      · have hj' : j = (⟨j.val,hn⟩ : Fin n).castLE
          (c.net.input_le.trans (Nat.le_add_right _ _)) := rfl
        rw [hj', Function.comp_apply, oraclePlacement_input, packed_input, packed_input]
      · rw [Function.comp_apply, packed_work x y _ (oraclePlacement_work c hr j (by omega) (by omega)),
          packed_work x _ _ (oraclePlacement_work c hr j (by omega) (by omega))]
  · have hout : ∀ j, w j ≠ i := by simpa only [not_exists] using hi
    rw [Register.replace_outside w _ _ ⟨i,hout⟩]
    have hir : n+m ≤ i.val := by
      by_contra hn
      by_cases hin : i.val < n
      · exact hi ⟨(⟨i.val,hin⟩ : Fin n).castLE
          (c.net.input_le.trans (Nat.le_add_right _ _)), by
            rw [oraclePlacement_input]⟩
      · exact hi ⟨⟨c.width+(i.val-n),by omega⟩, by
          rw [oraclePlacement_target c hr ⟨i.val-n,by omega⟩]
          apply Fin.ext; dsimp; omega⟩
    rw [packed_work x y i hir, packed_work x _ i hir]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PackedPrograms.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

def firstRegister (n m r : ℕ) : Register n (n+m+r) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t : Fin (n+m+r) => t.val) h

lemma packed_first {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ firstRegister n m r = x := by
  funext i
  exact packed_input x y i

lemma packed_injective {n m r : ℕ} (y : Basis m) :
    Function.Injective (fun x : Basis n => packed r x y) := by
  intro x z h
  have hh := congrArg (fun t => t ∘ firstRegister n m r) h
  simpa only [packed_first] using hh

lemma packed_replace_first {n m r : ℕ} (x u : Basis n) (y : Basis m) :
    (firstRegister n m r).replace (packed r x y) u = packed r u y := by
  funext i
  by_cases hi : i.val<n
  · have he : i = firstRegister n m r ⟨i.val,hi⟩ := rfl
    rw [he, Register.replace_inside]
    exact (packed_input u y ⟨i.val,hi⟩).symm
  · have hout : ∀ j : Fin n, firstRegister n m r j ≠ i := by
      intro j he
      have hh := congrArg Fin.val he
      change j.val = i.val at hh
      omega
    rw [Register.replace_outside _ _ _ ⟨i,hout⟩]
    simp [packed,hi]

def firstProgram {n : ℕ} (m r : ℕ) (ops : List (Instruction n)) :
    List (Instruction (n+m+r)) := ops.map (Instruction.place (firstRegister n m r))

lemma firstProgram_length {n : ℕ} (m r : ℕ) (ops : List (Instruction n)) :
    (firstProgram m r ops).length = ops.length := by simp [firstProgram]

lemma firstProgram_state {n m r : ℕ} (ops : List (Instruction n)) (y : Basis m)
    (ψ : State n) :
    (programMatrix (firstProgram m r ops)).mulVec (encodeState (fun x => packed r x y) ψ) =
      encodeState (fun x => packed r x y) ((programMatrix ops).mulVec ψ) := by
  refine matrix_encodeState (fun x => packed r x y) (fun x => packed r x y)
    (programMatrix (firstProgram m r ops)) (programMatrix ops) ?_ ψ
  intro x
  rw [firstProgram, Register.placed_basis_state, packed_first]
  have he : (fun u => (firstRegister n m r).replace (packed r x y) u) =
      (fun u => packed r u y) := funext (fun u => packed_replace_first x u y)
  exact congrArg₂ (fun (e : Basis n → Basis (n+m+r)) (v : State n) => encodeState e v)
    he (matrix_basisVector (programMatrix ops) x)

lemma firstProgram_basis {n m r : ℕ} (ops : List (Instruction n)) (y : Basis m)
    (x : Basis n) :
    (programMatrix (firstProgram m r ops)).mulVec (basisVector (packed r x y)) =
      encodeState (fun z => packed r z y) ((programMatrix ops).mulVec (basisVector x)) := by
  rw [← encodeState_basis (fun z => packed r z y) x]
  exact firstProgram_state ops y _

lemma BooleanNetwork.oracleOn_state {n m r : ℕ} (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ψ : State n) :
    (programMatrix (oracleOn c hr)).mulVec
      (encodeState (fun x => packed r x (fun _ => false)) ψ) =
      encodeState (fun x => packed r x (c.eval x)) ψ := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, oracleOn_basis, Bool.false_xor]
  rfl

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PackedEncoding.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma packed_injective {n m r : ℕ} :
    Function.Injective (fun xy : Basis n × Basis m => packed r xy.1 xy.2) := by
  intro x y h
  apply Prod.ext
  · funext i
    have hh := congrFun h (⟨i.val,by omega⟩ : Fin (n+m+r))
    simpa only [packed_input] using hh
  · funext i
    have hh := congrFun h (⟨n+i.val,by omega⟩ : Fin (n+m+r))
    simpa only [packed_target] using hh

lemma packed_update_input {n m r : ℕ} (x : Basis n) (y : Basis m) (j : Fin n) (c : Bool) :
    Function.update (packed r x y) (⟨j.val,by omega⟩ : Fin (n+m+r)) c =
      packed r (Function.update x j c) y := by
  funext i
  by_cases hi : i.val=j.val
  · have he : i = (⟨j.val,by omega⟩ : Fin (n+m+r)) := Fin.ext hi
    simp only [he, Function.update_self, packed_input]
  · rw [Function.update_of_ne (by intro h; exact hi (congrArg Fin.val h))]
    unfold packed
    split_ifs with hn hm
    · rw [Function.update_of_ne]
      intro h; exact hi (congrArg Fin.val h)
    · rfl
    · rfl

lemma packed_update_target {n m r : ℕ} (x : Basis n) (y : Basis m) (j : Fin m) (c : Bool) :
    Function.update (packed r x y) (⟨n+j.val,by omega⟩ : Fin (n+m+r)) c =
      packed r x (Function.update y j c) := by
  funext i
  by_cases hi : i.val=n+j.val
  · have he : i = (⟨n+j.val,by omega⟩ : Fin (n+m+r)) := Fin.ext hi
    simp only [he, Function.update_self, packed_target]
  · rw [Function.update_of_ne (by intro h; exact hi (congrArg Fin.val h))]
    unfold packed
    split_ifs with hn hm
    · rfl
    · rw [Function.update_of_ne]
      intro h
      have hh := congrArg Fin.val h
      dsimp at hh
      omega
    · rfl

lemma append_update_left {p b : ℕ} (d : Basis p) (z : Basis b) (j : Fin p) (c : Bool) :
    Function.update (Fin.append d z) (j.castAdd b) c = Fin.append (Function.update d j c) z := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · by_cases hk : k = j
    · subst k; simp
    · rw [Function.update_of_ne (by intro h; apply hk; apply Fin.ext; exact congrArg (fun i : Fin (p+b) => i.val) h),
        Fin.append_left, Fin.append_left, Function.update_of_ne hk]
  · rw [Function.update_of_ne (by intro h; have hh := congrArg Fin.val h; simp at hh; omega),
      Fin.append_right, Fin.append_right]

/-- Taking an adjoint and reading a basis outcome implements exactly the
correlation with the prepared state, without an idealized projection gate. -/
lemma encoded_adjoint_test {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e)
    (U : Matrix (Basis q) (Basis q) ℂ) (v : Basis q) (χ ψ : α → ℂ)
    (h : U.mulVec (basisVector v) = encodeState e χ) :
    U.conjTranspose.mulVec (encodeState e ψ) v = ∑ a, star (χ a)*ψ a := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    matrix_basisVector, Matrix.conjTranspose_apply]
  rw [matrix_basisVector] at h
  apply Finset.sum_congr rfl
  intro a _
  have ha := congrFun h (e a)
  rw [encodeState_at e he] at ha
  rw [ha]
  ring

end ExactQuantumFactoring.BooleanNetwork


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CoherentSampling.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma packed_eq_iff {n m r : ℕ} (x z : Basis n) (y u : Basis m) :
    packed r x y = packed r z u ↔ x=z ∧ y=u := by
  constructor
  · intro h
    have hh := BooleanNetwork.packed_injective (n := n) (m := m) (r := r)
      (a₁ := (x,y)) (a₂ := (z,u)) h
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma encoded_packed_coordinate {n m r : ℕ} (y u : Basis m) (ψ : State n)
    (z : Basis n) :
    encodeState (fun x => packed r x y) ψ (packed r z u) = if u=y then ψ z else 0 := by
  classical
  rw [encodeState_apply]
  simp only [packed_eq_iff]
  by_cases hu : u=y
  · simp [hu]
  · simp [hu]

/-- Retain the modular value register while interfering the exponent register;
no copy of the exponent or hidden measurement is inserted. -/
def sampleProgram {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction n)) : List (Instruction (n+m+r)) :=
  oracleOn c hr ++ firstProgram m r ops

lemma sampleProgram_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction n)) :
    (sampleProgram c hr ops).length ≤ 4*c.net.count+2*m+ops.length := by
  have h := oracleOn_length c hr
  simp only [sampleProgram,List.length_append,firstProgram_length]
  omega

lemma sampleProgram_amplitude {n m r : ℕ} (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ops : List (Instruction n)) (ψ : State n)
    (z : Basis n) (u : Basis m) :
    (programMatrix (sampleProgram c hr ops)).mulVec
      (encodeState (fun x => packed r x (fun _ => false)) ψ) (packed r z u) =
      ∑ x, if c.eval x=u then programMatrix ops z x * ψ x else 0 := by
  classical
  rw [sampleProgram,programMatrix_append,← Matrix.mulVec_mulVec,oracleOn_state]
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,firstProgram_basis]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,encoded_packed_coordinate,
    matrix_basisVector]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.eval x=u
  · simp only [h,ite_true]
    ring
  · simp only [h,ite_false,show u ≠ c.eval x from Ne.symm h,mul_zero]

/-- Coherent sampling on an explicitly encoded logical subspace. Inactive
quantum registers stay present; normalization need not be inferred by analogy
with a stochastic oracle. -/
lemma sampleProgram_encoded_amplitude {α : Type*} [Fintype α]
    {n m r : ℕ} (e : α → Basis n) (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ops : List (Instruction n)) (ψ : α → ℂ)
    (z : Basis n) (u : Basis m) :
    (programMatrix (sampleProgram c hr ops)).mulVec
      (encodeState (fun x => packed r (e x) (fun _ => false)) ψ) (packed r z u) =
      ∑ x, if c.eval (e x)=u then programMatrix ops z (e x) * ψ x else 0 := by
  classical
  rw [sampleProgram,programMatrix_append,← Matrix.mulVec_mulVec]
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,firstProgram_basis]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,encoded_packed_coordinate,
    matrix_basisVector]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.eval (e x)=u
  · simp only [h,ite_true]
    ring
  · simp only [h,ite_false,show u ≠ c.eval (e x) from Ne.symm h,mul_zero]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AppendRegister.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

def rightRegister (p q : ℕ) : Register q (p+q) := ⟨Fin.natAdd p, Fin.natAdd_injective q p⟩

lemma append_rightRegister {p q : ℕ} (x : Basis p) (y : Basis q) :
    Fin.append x y ∘ rightRegister p q = y := by
  funext i
  exact Fin.append_right _ _ i

lemma append_right_injective {p q : ℕ} (x : Basis p) :
    Function.Injective (Fin.append x : Basis q → Basis (p+q)) := by
  intro y z h
  have hh := congrArg (fun v => v ∘ rightRegister p q) h
  simpa only [append_rightRegister] using hh

lemma append_replace_right {p q : ℕ} (x : Basis p) (y z : Basis q) :
    (rightRegister p q).replace (Fin.append x y) z = Fin.append x z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : ∀ k, rightRegister p q k ≠ j.castAdd q := by
      intro k h
      have hh := congrArg Fin.val h
      change p+k.val=j.val at hh
      have := j.isLt
      omega
    rw [Register.replace_outside _ _ _ ⟨j.castAdd q,hj⟩]
    simp only [Fin.append_left]
  · change (rightRegister p q).replace (Fin.append x y) z (rightRegister p q j) = _
    rw [Register.replace_inside,Fin.append_right]

def rightProgram {q : ℕ} (p : ℕ) (ops : List (Instruction q)) :
    List (Instruction (p+q)) := ops.map (Instruction.place (rightRegister p q))

lemma rightProgram_basis {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (y : Basis q) :
    (programMatrix (rightProgram p ops)).mulVec (basisVector (Fin.append x y)) =
      encodeState (Fin.append x) ((programMatrix ops).mulVec (basisVector y)) := by
  rw [rightProgram,Register.placed_basis_state,append_rightRegister]
  congr 1
  funext z
  exact append_replace_right x y z

lemma rightProgram_entry {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (y z : Basis q) :
    programMatrix (rightProgram p ops) (Fin.append x z) (Fin.append x y) =
      programMatrix ops z y := by
  have hh := congrFun (rightProgram_basis ops x y) (Fin.append x z)
  simpa only [encodeState_at _ (append_right_injective x),matrix_basisVector] using hh

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ControlledTranslation.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace ControlledTranslation

def dataPart {p b : ℕ} (x : Basis (p+b)) : Basis p := fun i => x (i.castAdd b)
def phasePart {p b : ℕ} (x : Basis (p+b)) : Basis b := fun i => x (Fin.natAdd p i)

def addInput {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (b+b) :=
  (select (Fin.natAdd p)).pair ((select (fun i => i.castAdd b)).comp δ)

def forward {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (p+b) :=
  (select (fun i => i.castAdd b)).pair ((addInput δ).comp (BitArithmetic.add b))

def backward {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (p+b) :=
  (select (fun i => i.castAdd b)).pair ((addInput δ).comp (BitArithmetic.sub b))

def translate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) : Basis (p+b) :=
  Fin.append (dataPart x) (fun i => (bitsValue (phasePart x) + δ (dataPart x)).getLsbD i.val)

def untranslate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) : Basis (p+b) :=
  Fin.append (dataPart x) (fun i => (bitsValue (phasePart x) - δ (dataPart x)).getLsbD i.val)

lemma input_words {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    BitArithmetic.leftWord ((addInput δ).eval x) = bitsValue (phasePart x) ∧
      BitArithmetic.rightWord ((addInput δ).eval x) = bitsValue (δ.eval (dataPart x)) := by
  simp only [addInput, eval_pair, eval_comp, eval_select, BitArithmetic.leftWord,
    BitArithmetic.rightWord, Function.comp_apply, Fin.append_left, Fin.append_right]
  exact ⟨rfl,rfl⟩

lemma forward_correct {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (forward δ).eval x = translate (fun d => bitsValue (δ.eval d)) x := by
  rw [forward, eval_pair, eval_comp]
  unfold translate
  congr 1
  funext i
  rw [BitArithmetic.add_correct, (input_words δ x).1, (input_words δ x).2]

lemma backward_correct {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (backward δ).eval x = untranslate (fun d => bitsValue (δ.eval d)) x := by
  rw [backward, eval_pair, eval_comp]
  unfold untranslate
  congr 1
  funext i
  rw [BitArithmetic.sub_correct, (input_words δ x).1, (input_words δ x).2]

@[simp] lemma dataPart_append {p b : ℕ} (d : Basis p) (z : Basis b) :
    dataPart (Fin.append d z) = d := by funext i; simp [dataPart]
@[simp] lemma phasePart_append {p b : ℕ} (d : Basis p) (z : Basis b) :
    phasePart (Fin.append d z) = z := by funext i; simp [phasePart]

lemma untranslate_translate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) :
    untranslate δ (translate δ x) = x := by
  simp only [untranslate, translate, dataPart_append, phasePart_append, bitsValue_bits,
    BitVec.add_sub_cancel, bitsValue_bit]
  exact Fin.append_castAdd_natAdd

lemma translate_untranslate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) :
    translate δ (untranslate δ x) = x := by
  simp only [untranslate, translate, dataPart_append, phasePart_append, bitsValue_bits,
    BitVec.sub_add_cancel, bitsValue_bit]
  exact Fin.append_castAdd_natAdd

lemma forward_backward {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (backward δ).eval ((forward δ).eval x) = x := by
  rw [backward_correct, forward_correct, untranslate_translate]

lemma forward_count {p b : ℕ} (δ : BooleanNetwork p b) :
    (forward δ).net.count ≤ δ.net.count+86*b+6 := by
  simp only [forward, addInput, count_pair, count_comp, count_select, Nat.zero_add]
  have := BitArithmetic.add_count b
  omega

lemma backward_count {p b : ℕ} (δ : BooleanNetwork p b) :
    (backward δ).net.count ≤ δ.net.count+158*b+6 := by
  simp only [backward, addInput, count_pair, count_comp, count_select, Nat.zero_add]
  have := BitArithmetic.sub_count b
  omega

end ControlledTranslation
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RowNetwork.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

def rowIndex {b : ℕ} (j e : Fin b) : Fin b :=
  ⟨(b-1+j.val-e.val)%b, Nat.mod_lt _ (by have := j.isLt; omega)⟩

lemma rowIndex_val {b : ℕ} (j e : Fin b) (h : j.val ≤ e.val) :
    (rowIndex j e).val = b-1+j.val-e.val := by
  apply Nat.mod_eq_of_lt
  have := j.isLt
  omega

/-- Combining one triangular row is just a bit permutation and masked ANDs;
no arbitrary phase or exponentially large truth table is present. -/
def rowNetwork {b : ℕ} (j : Fin b) : BooleanNetwork b b :=
  vector (fun e => if j.val ≤ e.val ∧ e.val < b-1 then
    (bit (rowIndex j e)).band (bit j)
    else constant false)

lemma rowNetwork_count {b : ℕ} (j : Fin b) : (rowNetwork j).net.count = b := by
  rw [rowNetwork, count_vector]
  have h : ∀ e : Fin b, (if j.val ≤ e.val ∧ e.val < b-1 then
      (bit (rowIndex j e)).band (bit j)
      else constant false).net.count = 1 := by
    intro e
    by_cases he : j.val ≤ e.val ∧ e.val < b-1
    · rw [ite_eq_left he]; simp
    · rw [ite_eq_right he]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma rowNetwork_bit {b : ℕ} (j e : Fin b) (z : Bits b) :
    (rowNetwork j).eval z e = if j.val ≤ e.val ∧ e.val < b-1 then
      z (rowIndex j e) && z j else false := by
  rw [rowNetwork, eval_vector]
  split_ifs <;> simp_all

lemma rowNetwork_number {b : ℕ} (j : Fin b) (z : Bits b) :
    (bitsValue ((rowNetwork j).eval z)).toNat = rowShift j z := by
  classical
  rw [bitsValue_toNat]
  unfold rowShift
  simp_rw [rowNetwork_bit]
  have hand (a c : Bool) : (a && c).toNat = a.toNat*c.toNat := by
    cases a <;> cases c <;> rfl
  simp only [apply_ite Bool.toNat, Bool.toNat_false, mul_ite, mul_zero, hand, ← mul_assoc]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => rowIndex j e)
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rowIndex_val j e h.1]
    omega
  · intro e he f hf hef
    have h₁ := (Finset.mem_filter.mp he).2
    have h₂ := (Finset.mem_filter.mp hf).2
    have hv := congrArg Fin.val hef
    rw [rowIndex_val j e h₁.1, rowIndex_val j f h₂.1] at hv
    exact Fin.ext (by omega)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    let e : Fin b := ⟨b-1-i.val+j.val,by have := i.isLt; omega⟩
    have he : j.val ≤ e.val ∧ e.val < b-1 := by dsimp [e]; have := i.isLt; omega
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩, ?_⟩
    apply Fin.ext
    rw [rowIndex_val j e he.1]
    dsimp [e]
    have := i.isLt
    omega
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    rw [rowIndex_val j e h.1]
    have hw : b-1-(b-1+j.val-e.val)+j.val = e.val := by
      have := e.isLt
      omega
    rw [hw]

end ExactQuantumFactoring.Triangular


end

end OAI


