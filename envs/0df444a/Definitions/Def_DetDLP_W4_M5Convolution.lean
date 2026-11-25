-- Prove2me | Definitions.Def_DetDLP_W4_M5Convolution
-- name    : DetDLP_W4_M5Convolution
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:30:57.245736+00:00
-- url     : https://prove2.me/theorems/04ac6773-c0e4-4529-ae4e-9574f99d56a9
-- title:
--   Digit convolution and carry-chain uniqueness
-- statement:
--   Relates ordinary digit convolution to integer multiplication; characterizes the canonical residue words and uniquely determined carries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP
namespace w4_ConvolutionArithmetic

/-- The `i`-th base-`B` digit, in little-endian order. -/
def limb (B w i : ℕ) : ℕ := w / B ^ i % B

/-- The ordinary (noncyclic) convolution of two finite digit vectors. -/
def coefficient (B L a b u : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    if i + j = u then limb B a i * limb B b j else 0

/-- Reassemble the canonical residues of the convolution coefficients. -/
def value (B Q L a b : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (2 * L), (coefficient B L a b u % Q) * B ^ u

/-- A bounded natural number is the value of its first `L` base-`B` digits. -/
theorem digit_expansion {B L w : ℕ} (hw : w < B ^ L) :
    (∑ i ∈ Finset.range L, limb B w i * B ^ i) = w := by
  have h := congrArg Fin.val
    ((finFunctionFinEquiv (m := B) (n := L)).apply_symm_apply ⟨w, hw⟩)
  change (∑ i : Fin L, (w / B ^ i.val % B) * B ^ i.val) = w at h
  rw [← Fin.sum_univ_eq_sum_range (fun i => limb B w i * B ^ i)]
  exact h

/-- The crude double-sum bound already fits below the chosen Fermat modulus. -/
theorem coefficient_le_fourth_power {B L a b u : ℕ}
    (hB : 0 < B) (hL : L ≤ B) :
    coefficient B L a b u ≤ B ^ 4 := by
  calc
    coefficient B L a b u ≤
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, B * B := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · exact Nat.mul_le_mul (Nat.le_of_lt (Nat.mod_lt _ hB))
          (Nat.le_of_lt (Nat.mod_lt _ hB))
      · exact Nat.zero_le _
    _ = L * (L * (B * B)) := by simp
    _ ≤ B * (B * (B * B)) :=
      Nat.mul_le_mul hL (Nat.mul_le_mul_right (B * B) hL)
    _ = B ^ 4 := by ring

/-- Collecting the ordinary convolution by its output index preserves its value. -/
theorem weighted_convolution (B L a b : ℕ) :
    (∑ u ∈ Finset.range (2 * L), coefficient B L a b u * B ^ u) =
      (∑ i ∈ Finset.range L, limb B a i * B ^ i) *
      (∑ j ∈ Finset.range L, limb B b j * B ^ j) := by
  rw [Finset.sum_mul_sum]
  simp_rw [coefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i + j ∈ Finset.range (2 * L) := by
    simp only [Finset.mem_range] at hi hj ⊢
    omega
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [hij, if_true, pow_add]
  ring

/-- The complete weighted convolution is the product whenever both digit expansions fit. -/
theorem weighted_convolution_eq_product {B L a b : ℕ}
    (ha : a < B ^ L) (hb : b < B ^ L) :
    (∑ u ∈ Finset.range (2 * L), coefficient B L a b u * B ^ u) = a * b := by
  rw [weighted_convolution, digit_expansion ha, digit_expansion hb]

/-- Every coefficient is strictly below `2^(4*k)+1`, so reduction loses no information. -/
theorem coefficient_lt_fermat {k L a b u : ℕ} (hL : L ≤ 2 ^ k) :
    coefficient (2 ^ k) L a b u < 2 ^ (4 * k) + 1 := by
  have h := coefficient_le_fourth_power (a := a) (b := b) (u := u)
    (pow_pos (by norm_num : 0 < (2 : ℕ)) k) hL
  have hp : (2 ^ k) ^ 4 = 2 ^ (4 * k) := by rw [← pow_mul, Nat.mul_comm k 4]
  rw [hp] at h
  omega

/-- Arbitrary valid limb parameters recover the integer product exactly. -/
theorem fermat_value_eq_product {d k L a b : ℕ}
    (hd : d ≤ k * L) (hL : L ≤ 2 ^ k)
    (ha : a < 2 ^ d) (hb : b < 2 ^ d) :
    value (2 ^ k) (2 ^ (4 * k) + 1) L a b = a * b := by
  have hpow : 2 ^ d ≤ (2 ^ k) ^ L := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hd
  unfold value
  have hc : ∀ u : ℕ,
      coefficient (2 ^ k) L a b u % (2 ^ (4 * k) + 1) =
        coefficient (2 ^ k) L a b u :=
    fun _ => Nat.mod_eq_of_lt (coefficient_lt_fermat hL)
  simp_rw [hc]
  exact weighted_convolution_eq_product (ha.trans_le hpow) (hb.trans_le hpow)

/-- The unsigned value of a bit vector fits its declared width. -/
theorem bitsToNat_lt_pow {d : ℕ} (v : Fin d → Bool) : bitsToNat v < 2 ^ d := by
  let f : Fin d → Fin 2 := fun i => ⟨if v i then 1 else 0, by split <;> norm_num⟩
  have h := (finFunctionFinEquiv f).is_lt
  change (∑ i : Fin d, (if v i then 1 else 0) * 2 ^ i.val) < 2 ^ d at h
  exact h

/-- The exact arithmetic expression in `fermat_convolution_gadget` equals multiplication.
The identity holds for every valid limb width and count, not just a particular choice. -/
theorem fermat_convolution_eq_product {d k L a b : ℕ}
    (hd : d ≤ k * L) (hL : L ≤ 2 ^ k)
    (ha : a < 2 ^ d) (hb : b < 2 ^ d) :
    let B := 2 ^ k
    let Q := 2 ^ (4 * k) + 1
    let limb (w i : ℕ) := w / B ^ i % B
    let c (u : ℕ) := ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      if i + j = u then limb a i * limb b j else 0
    (∑ u ∈ Finset.range (2 * L), (c u % Q) * B ^ u) = a * b :=
  fermat_value_eq_product hd hL ha hb

/-- Evaluate the convolution on two arbitrary `d`-bit inputs. -/
theorem fermat_bits_value_eq_product {d k L : ℕ}
    (hd : d ≤ k * L) (hL : L ≤ 2 ^ k) (a b : Fin d → Bool) :
    value (2 ^ k) (2 ^ (4 * k) + 1) L (bitsToNat a) (bitsToNat b) =
      bitsToNat a * bitsToNat b :=
  fermat_value_eq_product hd hL (bitsToNat_lt_pow a) (bitsToNat_lt_pow b)

/-- The leaf gadget's external relation is exactly the multiplication relation. -/
theorem fermat_relation_iff_multiplication {d k L : ℕ}
    (hd : d ≤ k * L) (hL : L ≤ 2 ^ k) (x : Fin (4 * d) → Bool) :
    (let a := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩)
     let b := bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)
     let cout := bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)
     let B := 2 ^ k
     let Q := 2 ^ (4 * k) + 1
     let limb (w i : ℕ) := w / B ^ i % B
     let c (u : ℕ) := ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
       if i + j = u then limb a i * limb b j else 0
     (∑ u ∈ Finset.range (2 * L), (c u % Q) * B ^ u) = cout) ↔
    (bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
      bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
      bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)) := by
  change value (2 ^ k) (2 ^ (4 * k) + 1) L
      (bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩))
      (bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)) = _ ↔ _
  rw [fermat_bits_value_eq_product hd hL]

/-- Transfer parsimony along an equivalence of external relations. -/
theorem parsimonious_congr {G : BipartiteMultigraph}
    {T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool}
    {m : ℕ} {ext : Fin m → Fin G.nE} {R S : (Fin m → Bool) → Prop}
    (h : ∀ x, R x ↔ S x) : IsParsimonious G T ext R ↔ IsParsimonious G T ext S := by
  have heq : R = S := funext fun x => propext (h x)
  rw [heq]

/-- A parsimonious Fermat-convolution gadget is a parsimonious multiplier on the same graph. -/
theorem parsimonious_fermat_iff_mult {d k L : ℕ}
    (hd : d ≤ k * L) (hL : L ≤ 2 ^ k)
    (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (ext : Fin (4 * d) → Fin G.nE) :
    IsParsimonious G T ext (fun x =>
      let a := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩)
      let b := bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)
      let cout := bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)
      let B := 2 ^ k
      let Q := 2 ^ (4 * k) + 1
      let limb (w i : ℕ) := w / B ^ i % B
      let c (u : ℕ) := ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        if i + j = u then limb a i * limb b j else 0
      (∑ u ∈ Finset.range (2 * L), (c u % Q) * B ^ u) = cout) ↔
    IsParsimonious G T ext (fun x =>
      bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
      bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
      bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)) := by
  exact parsimonious_congr (fermat_relation_iff_multiplication hd hL)

/-- The canonical fixed-width, little-endian binary word of a natural number. -/
def canonicalBits (d w : ℕ) : Fin d → Bool :=
  fun i => decide (w / 2 ^ i.val % 2 = 1)

/-- A fixed-width bit vector is determined by its unsigned value. -/
theorem bitsToNat_injective (d : ℕ) : Function.Injective (@bitsToNat d) := by
  intro a b hab
  let fa : Fin d → Fin 2 := fun i => ⟨if a i then 1 else 0, by split <;> norm_num⟩
  let fb : Fin d → Fin 2 := fun i => ⟨if b i then 1 else 0, by split <;> norm_num⟩
  have hf : finFunctionFinEquiv fa = finFunctionFinEquiv fb := Fin.ext hab
  have heq : fa = fb := finFunctionFinEquiv.injective hf
  funext i
  have hi := congrArg (fun f : Fin d → Fin 2 => (f i).val) heq
  cases ha : a i <;> cases hb : b i <;> simp [fa, fb, ha, hb] at hi ⊢

/-- Decode the canonical word of any value that fits the chosen width. -/
theorem bitsToNat_canonicalBits {d w : ℕ} (hw : w < 2 ^ d) :
    bitsToNat (canonicalBits d w) = w := by
  have hdigit : ∀ i : Fin d,
      (if canonicalBits d w i then 1 else 0) = w / 2 ^ i.val % 2 := by
    intro i
    have hm : w / 2 ^ i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    simp only [canonicalBits, decide_eq_true_eq]
    split <;> omega
  unfold bitsToNat
  simp_rw [hdigit]
  calc
    (∑ i : Fin d, (w / 2 ^ i.val % 2) * 2 ^ i.val) =
        ∑ i ∈ Finset.range d, (w / 2 ^ i % 2) * 2 ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (w / 2 ^ i % 2) * 2 ^ i) d
    _ = w := digit_expansion hw

/-- Canonical encoding recovers every fixed-width bit vector, including leading zeroes. -/
theorem canonicalBits_bitsToNat {d : ℕ} (v : Fin d → Bool) :
    canonicalBits d (bitsToNat v) = v := by
  apply bitsToNat_injective d
  exact bitsToNat_canonicalBits (bitsToNat_lt_pow v)

/-- Exactly one fixed-width binary word represents each value in range. -/
theorem exists_unique_bits {d w : ℕ} (hw : w < 2 ^ d) :
    ∃! v : Fin d → Bool, bitsToNat v = w := by
  refine ⟨canonicalBits d w, bitsToNat_canonicalBits hw, ?_⟩
  intro v hv
  exact bitsToNat_injective d (hv.trans (bitsToNat_canonicalBits hw).symm)

/-- A bounded canonical residue has a unique binary witness even when only congruence
and the canonical-range test are imposed locally. -/
theorem canonical_residue_bits_unique {d Q r : ℕ}
    (hQ : Q ≤ 2 ^ d) (hr : r < Q) :
    ∃! v : Fin d → Bool, bitsToNat v < Q ∧ bitsToNat v % Q = r := by
  refine ⟨canonicalBits d r, ?_, ?_⟩
  · dsimp only
    rw [bitsToNat_canonicalBits (hr.trans_le hQ)]
    exact ⟨hr, Nat.mod_eq_of_lt hr⟩
  · intro v hv
    have hv' : bitsToNat v = r := by
      have h := hv.2
      rwa [Nat.mod_eq_of_lt hv.1] at h
    apply bitsToNat_injective d
    rw [bitsToNat_canonicalBits (hr.trans_le hQ)]
    exact hv'

/-- Canonical words for an entire indexed family have a unique joint assignment.
This is the pointwise witness used for intermediate wire bundles in a parsimonious graph. -/
theorem canonical_residue_array_unique {I : Type*} {d Q : ℕ}
    (hQ : Q ≤ 2 ^ d) (r : I → ℕ) (hr : ∀ i, r i < Q) :
    ∃! words : I → Fin d → Bool,
      ∀ i, bitsToNat (words i) < Q ∧ bitsToNat (words i) % Q = r i := by
  refine ⟨fun i => canonicalBits d (r i), ?_, ?_⟩
  · intro i
    rw [bitsToNat_canonicalBits ((hr i).trans_le hQ)]
    exact ⟨hr i, Nat.mod_eq_of_lt (hr i)⟩
  · intro words hwords
    funext i
    apply bitsToNat_injective d
    rw [bitsToNat_canonicalBits ((hr i).trans_le hQ)]
    have h := (hwords i).2
    rwa [Nat.mod_eq_of_lt (hwords i).1] at h

/-- The canonical carry recurrence is defined independently of any proposed witness. -/
def carry (B : ℕ) (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (c i + carry B c i) / B

/-- The output digits determined by the canonical carry recurrence. -/
def carriedDigit (B : ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  (c i + carry B c i) % B

/-- The canonical recurrence supplies a valid chain for every coefficient vector. -/
theorem canonical_carry_chain {B : ℕ} (hB : 0 < B) (c : ℕ → ℕ) :
    carry B c 0 = 0 ∧
    ∀ i, c i + carry B c i = carriedDigit B c i + B * carry B c (i + 1) ∧
      carriedDigit B c i < B := by
  refine ⟨rfl, fun i => ?_⟩
  exact ⟨(Nat.mod_add_div _ _).symm, Nat.mod_lt _ hB⟩

/-- Local carry equations force the entire finite trace to be canonical.
The local quotient/remainder calculation is the same one appearing in the accepted
`DetDLP.schonhage_strassen_fermat_dft_and_carry`; this lemma supplies the global
recurrence comparison needed to identify all intermediate witnesses. -/
theorem carry_chain_is_canonical {B m : ℕ} (c z κ : ℕ → ℕ)
    (hB : 0 < B) (hzero : κ 0 = 0)
    (hstep : ∀ i < m, c i + κ i = z i + B * κ (i + 1) ∧ z i < B) :
    (∀ i ≤ m, κ i = carry B c i) ∧
    (∀ i < m, z i = carriedDigit B c i) := by
  have hκ : ∀ i ≤ m, κ i = carry B c i := by
    intro i hi
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have him : i < m := by omega
      have heq := (hstep i him).1
      have hz := (hstep i him).2
      have hdiv : (c i + κ i) / B = κ (i + 1) := by
        rw [heq, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hz, zero_add]
      rw [← hdiv, ih (by omega)]
      rfl
  refine ⟨hκ, ?_⟩
  intro i hi
  have heq := (hstep i hi).1
  have hz := (hstep i hi).2
  unfold carriedDigit
  rw [← hκ i (by omega), heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz]

/-- Any two locally valid carry traces agree at every position used by the finite network. -/
theorem carry_chain_unique {B m : ℕ} (c z κ z' κ' : ℕ → ℕ)
    (hB : 0 < B) (hzero : κ 0 = 0) (hzero' : κ' 0 = 0)
    (hstep : ∀ i < m, c i + κ i = z i + B * κ (i + 1) ∧ z i < B)
    (hstep' : ∀ i < m, c i + κ' i = z' i + B * κ' (i + 1) ∧ z' i < B) :
    (∀ i ≤ m, κ i = κ' i) ∧ (∀ i < m, z i = z' i) := by
  have h := carry_chain_is_canonical c z κ hB hzero hstep
  have h' := carry_chain_is_canonical c z' κ' hB hzero' hstep'
  exact ⟨fun i hi => (h.1 i hi).trans (h'.1 i hi).symm,
    fun i hi => (h.2 i hi).trans (h'.2 i hi).symm⟩


end w4_ConvolutionArithmetic
end DetDLP


