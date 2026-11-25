-- Prove2me | Definitions.Def_DetDLP_W4_M5Transcript
-- name    : DetDLP_W4_M5Transcript
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:33:46.859164+00:00
-- url     : https://prove2.me/theorems/2d475f05-ffd4-4bbe-bec3-4f7c7c69de6b
-- title:
--   Local transform checks and unique multiplication transcripts
-- statement:
--   Defines all transform and carry checks. A correct external product admits one transcript satisfying all checks, and an incorrect product admits none.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5DFT
import Definitions.Def_DetDLP_W4_M5Parameters

set_option autoImplicit false

namespace DetDLP.w4_M5TranscriptBridge

open w4_ConvolutionArithmetic Finset

/-- A packed input or output word with zero padding beyond its external bit width. -/
def bitWindow {s : ℕ} (x : Fin s → Bool) (k j : ℕ) : Fin k → Bool :=
  fun b => if h : k*j + b.val < s then x ⟨k*j + b.val, h⟩ else false

theorem bitWindow_value {s : ℕ} (x : Fin s → Bool) (k j : ℕ) :
    bitsToNat (bitWindow x k j) = limb (2^k) (bitsToNat x) j := by
  have hb : limb (2^k) (bitsToNat x) j < 2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hw : bitWindow x k j = canonicalBits k (limb (2^k) (bitsToNat x) j) := by
    funext b
    unfold canonicalBits limb
    rw [← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_mod_two_pow,
      decide_eq_true b.isLt, Bool.true_and, ← pow_mul, Nat.testBit_div_two_pow, Nat.add_comm]
    by_cases h : k*j + b.val < s
    · have hh := congrFun (canonicalBits_bitsToNat x) ⟨_, h⟩
      simpa only [bitWindow, dif_pos h, canonicalBits, ← Nat.testBit_eq_decide_div_mod_eq] using hh.symm
    · rw [bitWindow, dif_neg h, Nat.testBit_lt_two_pow]
      exact (bitsToNat_lt_pow x).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [hw, bitsToNat_canonicalBits hb]

/-- Two bounded digit strings with the same integer value agree digit by digit. -/
theorem digits_ext {B m : ℕ} (u v : ℕ → ℕ) (hu : ∀ j < m, u j < B)
    (hv : ∀ j < m, v j < B)
    (he : (∑ j ∈ range m, u j * B^j) = ∑ j ∈ range m, v j * B^j) :
    ∀ j < m, u j = v j := by
  let U : Fin m → Fin B := fun i => ⟨u i.val, hu _ i.isLt⟩
  let V : Fin m → Fin B := fun i => ⟨v i.val, hv _ i.isLt⟩
  have he' : finFunctionFinEquiv U = finFunctionFinEquiv V := by
    apply Fin.ext
    change (∑ i : Fin m, u i.val * B^i.val) = ∑ i : Fin m, v i.val * B^i.val
    rwa [Fin.sum_univ_eq_sum_range (fun j => u j * B^j),
      Fin.sum_univ_eq_sum_range (fun j => v j * B^j)]
  have hUV := finFunctionFinEquiv.injective he'
  intro j hj
  exact congrArg Fin.val (congrFun hUV ⟨j, hj⟩)

/-- A finite, zero-ended carry chain enforces exactly the external integer value. -/
theorem carry_spec {B m y : ℕ} (hB : 0 < B) (hy : y < B^m) (c : ℕ → ℕ) :
    ((∑ i ∈ range m, c i * B ^ i) = y) ↔
      carry B c m = 0 ∧ ∀ i < m, carriedDigit B c i = limb B y i := by
  obtain ⟨_, hstep⟩ := canonical_carry_chain hB c
  have hp := DetDLP.schonhage_strassen_fermat_dft_and_carry.2.2 B m c
    (carriedDigit B c) (carry B c) hB rfl (fun i _ => hstep i)
  constructor
  · intro h
    have hm := hp.2.2 (h.trans_lt hy)
    refine ⟨hm.1, digits_ext _ _ (fun i _ => (hstep i).2)
      (fun i _ => Nat.mod_lt _ hB) ?_⟩
    exact hm.2.trans (h.trans (digit_expansion hy).symm)
  · rintro ⟨hk, hd⟩
    rw [hp.2.1, hk, zero_mul, add_zero, ← digit_expansion hy]
    apply sum_congr rfl
    intro i hi
    rw [hd i (mem_range.mp hi)]

/-- The mixed-radix indexing used by the first and second FFT layers. -/
theorem sum_grid {R : Type*} [AddCommMonoid R] (L1 L2 : ℕ) (f : ℕ → R) :
    (∑ i ∈ range (L1*L2), f i) =
      ∑ j1 ∈ range L1, ∑ j2 ∈ range L2, f (L2*j1 + j2) := by
  induction L1 with
  | zero => simp
  | succ L1 ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, Nat.mul_comm L2 L1]

/-- Compute the two forward checks in the Fermat ring. Here the block index is
`j₂` for the first layer and `t₁` for the second; their common index is `(t₁,j₂)`. -/
def fwd1 {R : Type*} [CommRing R] (L1 L2 : ℕ) (w : R) (x : ℕ → R)
    (t1 j2 : ℕ) : R :=
  w^(j2*t1) * ∑ j1 ∈ range L1, w^(L2*j1*t1) * x (L2*j1+j2)

def fwd2 {R : Type*} [CommRing R] (L1 L2 : ℕ) (w : R) (x : ℕ → ℕ → R)
    (t1 t2 : ℕ) : R :=
  ∑ j2 ∈ range L2, w^(L1*j2*t2) * x t1 j2

theorem forward_blocks {R : Type*} [CommRing R] {L1 L2 : ℕ} {w : R}
    (hp : w^(L1*L2) = 1) (x : ℕ → R) (t1 t2 : ℕ) :
    fwd2 L1 L2 w (fwd1 L1 L2 w x) t1 t2 =
      w4_FermatDFT.forward (L1*L2) w x (t1+L1*t2) := by
  unfold w4_FermatDFT.forward
  rw [sum_grid]
  exact (w4_FermatDFT.two_layer_forward L1 L2 w hp x t1 t2).symm

def inv1 {R : Type*} [CommRing R] (L1 L2 : ℕ) (r : R) (y : ℕ → ℕ → R)
    (t1 j2 : ℕ) : R := ∑ t2 ∈ range L2, r^(L1*j2*t2) * y t1 t2

def inv2 {R : Type*} [CommRing R] (L1 L2 : ℕ) (r a : R) (y : ℕ → ℕ → R)
    (j1 j2 : ℕ) : R := a * ∑ t1 ∈ range L1, r^((L2*j1+j2)*t1) * y t1 j2

private theorem reverse_base {R : Type*} [CommRing R] {L : ℕ} {w : R}
    (hP : w^L = 1) {u : ℕ} (hu : u < L) :
    (w^(L-1))^u = w^(L-u) := by
  rw [← pow_mul]
  apply pow_eq_pow_of_modEq _ hP
  apply Nat.ModEq.add_right_cancel' u
  have hL : L - 1 + 1 = L := by omega
  rw [show (L-1)*u + u = L*u by
    calc _ = (L - 1 + 1)*u := by ring
         _ = _ := by rw [hL], Nat.sub_add_cancel hu.le]
  simp [Nat.ModEq]

theorem inverse_blocks {R : Type*} [CommRing R] {L1 L2 : ℕ} {w : R}
    (hP : w^(L1*L2) = 1) (invL : R) (y : ℕ → R) (j1 j2 : ℕ)
    (hu : L2*j1+j2 < L1*L2) :
    inv2 L1 L2 (w^(L1*L2-1)) invL
      (inv1 L1 L2 (w^(L1*L2-1)) (fun t1 t2 => y (t1+L1*t2))) j1 j2 =
      w4_FermatDFT.inverse (L1*L2) w invL y (L2*j1+j2) := by
  let r := w^(L1*L2-1)
  have hr : r^(L1*L2) = 1 := by
    dsimp [r]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hP, one_pow]
  have hneg (t : ℕ) : w^((L1*L2-(L2*j1+j2))*t) = r^((L2*j1+j2)*t) := by
    rw [pow_mul, pow_mul, ← reverse_base hP hu]
  unfold inv2 inv1 w4_FermatDFT.inverse
  congr 1
  conv_rhs =>
    rw [Nat.mul_comm L1 L2, sum_grid L2 L1]
  rw [sum_comm]
  -- Compare the two double sums with the indices in the same order.
  simp_rw [Finset.mul_sum]
  apply sum_congr rfl
  intro t1 _
  apply sum_congr rfl
  intro t2 _
  rw [Nat.mul_comm L2 L1, hneg]
  have he := w4_FermatDFT.two_layer_summand L1 L2 r hr (fun _ => (1 : R)) j1 j2 t1 t2
  simp only [one_mul, mul_one] at he
  rw [Nat.add_comm (L1*t2) t1, he]
  dsimp [r] at *
  rw [← pow_add _ (j2*t1), show j2*t1 + L2*j1*t1 = (L2*j1+j2)*t1 by ring]
  ring

open w4_MulParams

abbrev base (d : ℕ) := 2 ^ k d
abbrev ncoef (d : ℕ) := 2 * n0 d
abbrev modulus (d : ℕ) := 2 ^ J d + 1
abbrev Word (d : ℕ) := Fin (J d + 1) → Bool
abbrev Grid (d : ℕ) (α : Type) := Fin (L1 d) → Fin (L2 d) → α

/-- Split the precise external interface into two inputs and one claimed output. -/
def operand {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) : Fin d → Bool :=
  fun i => if a then x ⟨d+i.val, by omega⟩ else x ⟨i.val, by omega⟩

def output {d : ℕ} (x : Fin (4*d) → Bool) : Fin (2*d) → Bool :=
  fun i => x ⟨2*d+i.val, by omega⟩

def IsProduct {d : ℕ} (x : Fin (4*d) → Bool) : Prop :=
  bitsToNat (operand x false) * bitsToNat (operand x true) = bitsToNat (output x)

def inputDigit {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) (j : ℕ) : ℕ :=
  bitsToNat (bitWindow (operand x a) (k d) j)

def outputDigit {d : ℕ} (x : Fin (4*d) → Bool) (j : ℕ) : ℕ :=
  bitsToNat (bitWindow (output x) (k d) j)

def padDigit {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) : ℕ → FermatRing d :=
  w4_FermatDFT.padded (J d) (n0 d) (inputDigit x a)

/-- The numerical value computed by each concrete FFT block. -/
def first {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) :=
  fwd1 (L1 d) (L2 d) (w4_MulParams.omega d) (padDigit x a)

def second {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) :=
  fwd2 (L1 d) (L2 d) (w4_MulParams.omega d) (first x a)

def point {d : ℕ} (x : Fin (4*d) → Bool) (i j : ℕ) :=
  second x false i j * second x true i j

def wInv (d : ℕ) := (w4_MulParams.omega d) ^ (L1 d * L2 d - 1)

def third {d : ℕ} (x : Fin (4*d) → Bool) := inv1 (L1 d) (L2 d) (wInv d) (point x)

def fourth {d : ℕ} (x : Fin (4*d) → Bool) := inv2 (L1 d) (L2 d) (wInv d) (inverseL d) (third x)

def coeff {d : ℕ} (x : Fin (4*d) → Bool) : ℕ → ℕ :=
  coefficient (base d) (n0 d) (bitsToNat (operand x false)) (bitsToNat (operand x true))

theorem coeff_bounded {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) (u : ℕ) :
    coeff x u < modulus d := by
  unfold modulus
  rw [← four_mul_k hd]
  exact coefficient_lt_fermat (n0_lt_two_pow_k hd).le

private theorem weighted_coeff {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) :
    (∑ i ∈ range (ncoef d), coeff x i * base d ^ i) =
      bitsToNat (operand x false) * bitsToNat (operand x true) := by
  have hbound : 2 ^ d ≤ base d ^ n0 d := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (n0_covers hd)
  exact weighted_convolution_eq_product ((bitsToNat_lt_pow _).trans_le hbound)
    ((bitsToNat_lt_pow _).trans_le hbound)

/-- The last physical block reads exactly the ordinary unsigned coefficient,
including all zero high coefficients. This is equality in `ℕ`, after taking
canonical representatives, not only equality modulo the Fermat modulus. -/
theorem fourth_value {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool)
    (j1 j2 : ℕ) (hu : L2 d * j1 + j2 < L d) :
    (fourth x j1 j2).val = coeff x (L2 d * j1 + j2) := by
  have hP : (w4_MulParams.omega d) ^ (L1 d * L2 d) = 1 := by
    rw [L1_mul_L2, omega_full hd]
  have hS (b : Bool) (a t : ℕ) : second x b a t =
      w4_FermatDFT.forward (L d) (w4_MulParams.omega d) (padDigit x b) (a+L1 d*t) := by
    simpa only [second, first, L1_mul_L2] using forward_blocks hP (padDigit x b) a t
  let F : ℕ → FermatRing d := fun t =>
    w4_FermatDFT.forward (L d) (w4_MulParams.omega d) (padDigit x false) t *
    w4_FermatDFT.forward (L d) (w4_MulParams.omega d) (padDigit x true) t
  have hpoint : point x = fun a t => F (a+L1 d*t) := by
    funext a t
    simp only [point, hS, F]
  have hi : fourth x j1 j2 = w4_FermatDFT.inverse (L d) (w4_MulParams.omega d) (inverseL d) F
      (L2 d * j1 + j2) := by
    unfold fourth third wInv
    rw [hpoint, inverse_blocks hP _ _ j1 j2 (by rwa [L1_mul_L2]), L1_mul_L2]
  obtain ⟨hμ, _, hJ, hL⟩ := root_parameters hd
  have hn : μ d - 1 + 1 = μ d := Nat.sub_add_cancel hμ
  have hp := w4_FermatDFT.fermat_productPipeline_eq_natCoefficient (m := μ d - 1)
    (by rw [hn]; exact mu_le_J hd) hJ (hL ▸ L_lower hd) (inputDigit x false)
    (inputDigit x true) (hL ▸ hu)
  have his : inverseL d = w4_FermatDFT.lengthInverse (J d) (μ d - 1) := by
    simp only [inverseL, w4_FermatDFT.lengthInverse, hn]
  rw [w4_FermatDFT.productPipeline, ← hL, ← his] at hp
  rw [hi, show w4_FermatDFT.inverse (L d) (w4_MulParams.omega d) (inverseL d) F
      (L2 d*j1+j2) = _ from hp]
  have heq : w4_FermatDFT.natCoefficient (n0 d) (inputDigit x false) (inputDigit x true)
      (L2 d*j1+j2) = coeff x (L2 d*j1+j2) := by
    simp only [w4_FermatDFT.natCoefficient, inputDigit, bitWindow_value, coeff, coefficient]
  rw [heq, ZMod.val_natCast_of_lt (coeff_bounded hd x _)]

def coeffStage {d : ℕ} (x : Fin (4*d) → Bool) (u : ℕ) : FermatRing d :=
  fourth x (u / L2 d) (u % L2 d)

theorem coeffStage_value {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) {u : ℕ}
    (hu : u < L d) : (coeffStage x u).val = coeff x u := by
  unfold coeffStage
  simpa only [Nat.div_add_mod] using fourth_value hd x (u / L2 d) (u % L2 d)
    (by simpa only [Nat.div_add_mod] using hu)

/-- Read one canonical-width residue word. Each gate checks its *output word*,
not just equality after taking its residue, so noncanonical words cannot survive. -/
def decode {d : ℕ} (w : Word d) : FermatRing d := (bitsToNat w : FermatRing d)

def encode (d : ℕ) (r : FermatRing d) : Word d := w4_FermatDFT.canonicalWord (J d) r

theorem decode_encode (d : ℕ) (r : FermatRing d) : decode (d := d) (encode d r) = r := by
  change ((bitsToNat (canonicalBits (J d + 1) r.val) : ℕ) : FermatRing d) = r
  rw [bitsToNat_canonicalBits ((ZMod.val_lt r).trans_le (w4_FermatDFT.fermat_modulus_le_wordspace _)),
    ZMod.natCast_zmod_val]

theorem bits_encode (d : ℕ) (r : FermatRing d) : bitsToNat (encode d r) = r.val :=
  bitsToNat_canonicalBits ((ZMod.val_lt r).trans_le (w4_FermatDFT.fermat_modulus_le_wordspace _))

def packedGate {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) (i : Fin (n0 d)) : Word d :=
  encode d (inputDigit x a i.val : FermatRing d)

def readPacked {d : ℕ} (w : Fin (n0 d) → Word d) (n : ℕ) : FermatRing d :=
  if h : n < n0 d then decode (d := d) (w ⟨n, h⟩) else 0

def readGrid {d : ℕ} (g : Grid d (Word d)) (i j : ℕ) : FermatRing d :=
  if hi : i < L1 d then if hj : j < L2 d then decode (d := d) (g ⟨i,hi⟩ ⟨j,hj⟩) else 0 else 0

def firstGate {d : ℕ} (w : Fin (n0 d) → Word d) (i : Fin (L1 d)) (b : Fin (L2 d)) : Word d :=
  encode d (fwd1 (L1 d) (L2 d) (w4_MulParams.omega d) (readPacked (d := d) w) i.val b.val)

def secondGate {d : ℕ} (w : Grid d (Word d)) (i : Fin (L1 d)) (t : Fin (L2 d)) : Word d :=
  encode d (fwd2 (L1 d) (L2 d) (w4_MulParams.omega d) (readGrid (d := d) w) i.val t.val)

def pointGate {d : ℕ} (p q : Grid d (Word d)) (i : Fin (L1 d)) (t : Fin (L2 d)) : Word d :=
  encode d (decode (d := d) (p i t) * decode (d := d) (q i t))

def thirdGate {d : ℕ} (w : Grid d (Word d)) (i : Fin (L1 d)) (b : Fin (L2 d)) : Word d :=
  encode d (inv1 (L1 d) (L2 d) (wInv d) (readGrid (d := d) w) i.val b.val)

def coeffGate {d : ℕ} (w : Grid d (Word d)) (u : Fin (ncoef d)) : Word d :=
  encode d (inv2 (L1 d) (L2 d) (wInv d) (inverseL d) (readGrid (d := d) w)
    (u.val / L2 d) (u.val % L2 d))

@[simp] theorem readPacked_packedGate {d : ℕ} (x : Fin (4*d) → Bool) (a : Bool) :
    readPacked (d := d) (packedGate x a) = padDigit x a := by
  funext n
  by_cases hn : n < n0 d <;>
    simp only [readPacked, padDigit, w4_FermatDFT.padded, packedGate, hn, dif_pos, dif_neg,
      if_pos, if_neg, decode_encode, not_false_eq_true]

theorem blocks_first (d : ℕ) (x : Fin (4*d) → Bool) (a : Bool) (i : Fin (L1 d)) (b : Fin (L2 d)) :
    firstGate (d := d) (packedGate x a) i b = encode d (first x a i.val b.val) := by
  simp only [firstGate, readPacked_packedGate, first]

private theorem readGrid_encode {d : ℕ} (f : ℕ → ℕ → FermatRing d) (i j : ℕ)
    (hi : i < L1 d) (hj : j < L2 d) :
    readGrid (d := d) (fun a b => encode d (f a.val b.val)) i j = f i j := by
  rw [readGrid, dif_pos hi, dif_pos hj, decode_encode]

theorem blocks_second (d : ℕ) (x : Fin (4*d) → Bool) (a : Bool) (i : Fin (L1 d)) (t : Fin (L2 d)) :
    secondGate (d := d) (fun j b => encode d (first x a j.val b.val)) i t =
      encode d (second x a i.val t.val) := by
  unfold secondGate second fwd2
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [readGrid_encode (first x a) _ _ i.isLt (mem_range.mp hj)]

theorem blocks_point (d : ℕ) (x : Fin (4*d) → Bool) (i : Fin (L1 d)) (t : Fin (L2 d)) :
    pointGate (d := d) (fun j b => encode d (second x false j.val b.val))
      (fun j b => encode d (second x true j.val b.val)) i t =
      encode d (point x i.val t.val) := by simp only [pointGate, point, decode_encode]

theorem blocks_third (d : ℕ) (x : Fin (4*d) → Bool) (i : Fin (L1 d)) (b : Fin (L2 d)) :
    thirdGate (d := d) (fun j t => encode d (point x j.val t.val)) i b =
      encode d (third x i.val b.val) := by
  unfold thirdGate third inv1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [readGrid_encode (point x) _ _ i.isLt (mem_range.mp hj)]

theorem blocks_coeff (d : ℕ) (x : Fin (4*d) → Bool) (u : Fin (ncoef d)) :
    coeffGate (d := d) (fun j b => encode d (third x j.val b.val)) u =
      encode d (coeffStage x u.val) := by
  unfold coeffGate coeffStage fourth inv2
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [readGrid_encode (third x) _ _ (mem_range.mp hj) (Nat.mod_lt _ (L2_pos d))]

/-- One word per internal edge of the two-layer graph, including a separate
word on each side of a carry equality vertex; no phantom padding wires. -/
@[ext] structure Transcript (d : ℕ) where
  packed : Bool → Fin (n0 d) → Word d
  forwardMiddle : Bool → Grid d (Word d)
  forwardPoint : Bool → Grid d (Word d)
  pointInverse : Grid d (Word d)
  inverseMiddle : Grid d (Word d)
  coefficient : Fin (ncoef d) → Word d
  carryLeft : Fin (ncoef d - 1) → Word d
  carryRight : Fin (ncoef d - 1) → Word d

def canonical {d : ℕ} (x : Fin (4*d) → Bool) : Transcript d where
  packed := packedGate x
  forwardMiddle := fun a i b => encode d (first x a i.val b.val)
  forwardPoint := fun a i b => encode d (second x a i.val b.val)
  pointInverse := fun i b => encode d (point x i.val b.val)
  inverseMiddle := fun i b => encode d (third x i.val b.val)
  coefficient := fun u => encode d (coeffStage x u.val)
  carryLeft := fun i => canonicalBits (J d+1) (carry (base d) (coeff x) (i.val+1))
  carryRight := fun i => canonicalBits (J d+1) (carry (base d) (coeff x) (i.val+1))

structure TransformChecks {d : ℕ} (x : Fin (4*d) → Bool) (t : Transcript d) : Prop where
  pack : ∀ a i, t.packed a i = packedGate x a i
  first : ∀ a i b, t.forwardMiddle a i b = firstGate (d := d) (t.packed a) i b
  second : ∀ a i b, t.forwardPoint a i b = secondGate (d := d) (t.forwardMiddle a) i b
  point : ∀ i b, t.pointInverse i b = pointGate (d := d) (t.forwardPoint false) (t.forwardPoint true) i b
  third : ∀ i b, t.inverseMiddle i b = thirdGate (d := d) t.pointInverse i b
  coeff : ∀ u, t.coefficient u = coeffGate (d := d) t.inverseMiddle u

theorem canonical_transform {d : ℕ} (x : Fin (4*d) → Bool) : TransformChecks x (canonical x) :=
  ⟨fun _ _ => rfl, fun a i b => (blocks_first d x a i b).symm,
    fun a i t => (blocks_second d x a i t).symm, fun i t => (blocks_point d x i t).symm,
    fun i b => (blocks_third d x i b).symm, fun u => (blocks_coeff d x u).symm⟩

/-- Induction over actual local equations forces every noncarry wire to its canonical word. -/
theorem transform_eq {d : ℕ} {x : Fin (4*d) → Bool} {p q : Transcript d}
    (hp : TransformChecks x p) (hq : TransformChecks x q) :
    p.packed = q.packed ∧ p.forwardMiddle = q.forwardMiddle ∧
      p.forwardPoint = q.forwardPoint ∧ p.pointInverse = q.pointInverse ∧
      p.inverseMiddle = q.inverseMiddle ∧ p.coefficient = q.coefficient := by
  have h0 : p.packed = q.packed := by funext a i; rw [hp.pack, hq.pack]
  have h1 : p.forwardMiddle = q.forwardMiddle := by funext a i b; rw [hp.first, hq.first, h0]
  have h2 : p.forwardPoint = q.forwardPoint := by funext a i b; rw [hp.second, hq.second, h1]
  have h3 : p.pointInverse = q.pointInverse := by funext i b; rw [hp.point, hq.point, h2]
  have h4 : p.inverseMiddle = q.inverseMiddle := by funext i b; rw [hp.third, hq.third, h3]
  have h5 : p.coefficient = q.coefficient := by funext i; rw [hp.coeff, hq.coeff, h4]
  exact ⟨h0, h1, h2, h3, h4, h5⟩

private theorem base_ge_two {d : ℕ} (hd : 1 ≤ d) : 2 ≤ base d :=
  Nat.one_lt_two_pow (by have := k_ge_four hd; omega)

/-- A carry never needs more bits than a residue word. -/
theorem carry_fits {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) (j : ℕ) :
    carry (base d) (coeff x) j < 2 ^ (J d + 1) := by
  have hb (u : ℕ) : coeff x u ≤ 2^J d := Nat.le_of_lt_succ (coeff_bounded hd x u)
  have hK (u : ℕ) : carry (base d) (coeff x) u ≤ 2^J d := by
    induction u with
    | zero => exact Nat.zero_le _
    | succ u ih =>
      apply Nat.div_le_of_le_mul
      have hh := Nat.mul_le_mul_right (2 ^ J d) (base_ge_two hd)
      have := hb u
      omega
  have := hK j
  rw [pow_succ]
  have := Nat.two_pow_pos (J d)
  omega

private theorem out_fits {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) :
    bitsToNat (output x) < base d ^ ncoef d := by
  apply (bitsToNat_lt_pow _).trans_le
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  dsimp only [ncoef]
  nlinarith only [n0_covers hd]

/-- Read out a carry word with constants at both ends of the finite chain. -/
def atLink {d : ℕ} (s : Fin (ncoef d-1) → Word d) (j : ℕ) : ℕ :=
  if hj : 0 < j ∧ j < ncoef d then bitsToNat (s ⟨j-1, by omega⟩) else 0

@[simp] theorem atLink_zero {d : ℕ} (s : Fin (ncoef d-1) → Word d) : atLink (d := d) s 0 = 0 := by
  simp [atLink]

@[simp] theorem atLink_last {d : ℕ} (s : Fin (ncoef d-1) → Word d) : atLink (d := d) s (ncoef d) = 0 := by
  simp [atLink]

@[simp] theorem atLink_internal {d : ℕ} (s : Fin (ncoef d-1) → Word d) (i : Fin (ncoef d-1)) :
    atLink (d := d) s (i.val+1) = bitsToNat (s i) := by
  have h : 0 < i.val+1 ∧ i.val+1 < ncoef d := by omega
  simp only [atLink, dif_pos h, Nat.add_sub_cancel]

structure CarryChecks {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) : Prop where
  spacer : ∀ i, p.carryLeft i = p.carryRight i
  gate : ∀ u : Fin (ncoef d), bitsToNat (p.coefficient u) + atLink (d := d) p.carryRight u.val =
    outputDigit x u.val + base d * atLink (d := d) p.carryLeft (u.val+1)

def Valid {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) : Prop :=
  TransformChecks x p ∧ CarryChecks x p

private theorem gate_word_correct {d : ℕ} (hd : 1 ≤ d) {x : Fin (4*d) → Bool} {p : Transcript d}
    (hp : TransformChecks x p) (u : Fin (ncoef d)) : bitsToNat (p.coefficient u) = coeff x u.val := by
  have h := (transform_eq hp (canonical_transform x)).2.2.2.2.2
  rw [h]
  change bitsToNat (encode d (coeffStage x u.val)) = _
  rw [bits_encode, coeffStage_value hd x (u.isLt.trans_le (L_lower hd))]

/-- The local word-level tests force the unique canonical carries and external multiplication. -/
theorem valid_forces {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) (p : Transcript d)
    (hp : Valid x p) : IsProduct x ∧ p = canonical x := by
  obtain ⟨htr, hc⟩ := hp
  have hsp : p.carryLeft = p.carryRight := funext hc.spacer
  have hch := carry_chain_is_canonical (coeff x) (outputDigit x) (atLink (d := d) p.carryRight)
    (Nat.two_pow_pos (k d)) (atLink_zero (d := d) p.carryRight) (m := ncoef d) (by
      intro u hu
      have h := hc.gate ⟨u, hu⟩
      rw [hsp, gate_word_correct hd htr] at h
      exact ⟨h, bitsToNat_lt_pow _⟩)
  have hoff := (hch.1 (ncoef d) le_rfl).symm.trans (atLink_last (d := d) p.carryRight)
  have hdigits (i : ℕ) (hi : i < ncoef d) : carriedDigit (base d) (coeff x) i =
      limb (base d) (bitsToNat (output x)) i :=
    (hch.2 i hi).symm.trans (bitWindow_value (output x) (k d) i)
  have hm := (carry_spec (Nat.two_pow_pos (k d)) (out_fits hd x) (coeff x)).2 ⟨hoff,hdigits⟩
  have hout : IsProduct x := (weighted_coeff hd x).symm.trans hm
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := transform_eq htr (canonical_transform x)
  have h7 : p.carryRight = (canonical x).carryRight := by
    funext i
    apply bitsToNat_injective
    have h := hch.1 (i.val+1) (by omega)
    rw [atLink_internal] at h
    exact h.trans (bitsToNat_canonicalBits (carry_fits hd x (i.val+1))).symm
  exact ⟨hout, Transcript.ext h0 h1 h2 h3 h4 h5 (hsp.trans h7) h7⟩

private theorem atLink_canonical {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool)
    (hL : carry (base d) (coeff x) (ncoef d) = 0) {i : ℕ} (hi : i ≤ ncoef d) :
    atLink (d := d) (canonical x).carryRight i = carry (base d) (coeff x) i := by
  by_cases hi0 : i = 0
  · subst i
    rfl
  by_cases him : i = ncoef d
  · subst i
    rw [atLink_last, hL]
  have hi' : 0 < i ∧ i < ncoef d := by omega
  rw [atLink, dif_pos hi']
  change bitsToNat (canonicalBits (J d+1) (carry (base d) (coeff x) (i-1+1))) = _
  rw [Nat.sub_add_cancel (by omega), bitsToNat_canonicalBits (carry_fits hd x i)]

/-- Conversely every true product has a canonical satisfying transcript on every wire. -/
theorem canonical_valid {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) (hx : IsProduct x) :
    Valid x (canonical x) := by
  refine ⟨canonical_transform x, ⟨fun _ => rfl, ?_⟩⟩
  have h := (carry_spec (Nat.two_pow_pos (k d)) (out_fits hd x) (coeff x)).1
    ((weighted_coeff hd x).trans hx)
  intro i
  rw [gate_word_correct hd (canonical_transform x), atLink_canonical hd x h.1 i.isLt.le]
  change coeff x i.val + carry (base d) (coeff x) i.val =
    outputDigit x i.val + base d * atLink (d := d) (canonical x).carryRight (i.val + 1)
  rw [atLink_canonical hd x h.1 i.isLt, outputDigit, bitWindow_value, ← h.2 i.val i.isLt]
  exact ((canonical_carry_chain (Nat.two_pow_pos _) (coeff x)).2 i.val).1

/-- Exact arithmetic parsimony: every bit-word witness of all the local tests is
canonical, and a witness exists precisely for the exact external multiplication relation. -/
theorem transcript_parsimony {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) :
    (IsProduct x → ∃! p : Transcript d, Valid x p) ∧
      (¬ IsProduct x → ¬ ∃ p : Transcript d, Valid x p) := by
  constructor
  · intro h
    exact ⟨canonical x, canonical_valid hd x h, fun p hp => (valid_forces hd x p hp).2⟩
  · rintro h ⟨p,hp⟩
    exact h (valid_forces hd x p hp).1

/- The checks below are grouped by *physical vertex*, not just by equation.
In particular an inverse-2 vertex with label `b` owns precisely `u % L2 = b`.
Input and output bit leaves impose no additional test. -/
def packCheck {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) (a : Bool) (u : Fin (n0 d)) : Bool :=
  decide (p.packed a u = packedGate x a u)

def forward1Check {d : ℕ} (p : Transcript d) (a : Bool) (b : Fin (L2 d)) : Bool :=
  decide (∀ i, p.forwardMiddle a i b = firstGate (d := d) (p.packed a) i b)

def forward2Check {d : ℕ} (p : Transcript d) (a : Bool) (i : Fin (L1 d)) : Bool :=
  decide (∀ t, p.forwardPoint a i t = secondGate (d := d) (p.forwardMiddle a) i t)

def pointCheck {d : ℕ} (p : Transcript d) (i : Fin (L1 d)) (t : Fin (L2 d)) : Bool :=
  decide (p.pointInverse i t = pointGate (d := d) (p.forwardPoint false) (p.forwardPoint true) i t)

def inverse1Check {d : ℕ} (p : Transcript d) (i : Fin (L1 d)) : Bool :=
  decide (∀ b, p.inverseMiddle i b = thirdGate (d := d) p.pointInverse i b)

def inverse2Check {d : ℕ} (p : Transcript d) (b : Fin (L2 d)) : Bool :=
  decide (∀ u : Fin (ncoef d), u.val % L2 d = b.val → p.coefficient u = coeffGate (d := d) p.inverseMiddle u)

def spacerCheck {d : ℕ} (p : Transcript d) (i : Fin (ncoef d-1)) : Bool :=
  decide (p.carryLeft i = p.carryRight i)

def carryCheck {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) (u : Fin (ncoef d)) : Bool :=
  decide (bitsToNat (p.coefficient u) + atLink (d := d) p.carryRight u.val =
    outputDigit x u.val + base d * atLink (d := d) p.carryLeft (u.val+1))

def AllChecks {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) : Prop :=
  (∀ a u, packCheck x p a u = true) ∧ (∀ a b, forward1Check p a b = true) ∧
  (∀ a i, forward2Check p a i = true) ∧ (∀ i t, pointCheck p i t = true) ∧
  (∀ i, inverse1Check p i = true) ∧ (∀ b, inverse2Check p b = true) ∧
  (∀ j, spacerCheck p j = true) ∧ (∀ u, carryCheck x p u = true)

theorem allChecks_iff {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) :
    AllChecks x p ↔ Valid x p := by
  simp only [AllChecks, packCheck, forward1Check, forward2Check, pointCheck,
    inverse1Check, inverse2Check, spacerCheck, carryCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨pa, f1, f2, pm, i1, i2, sp, ca⟩
    exact ⟨⟨pa, fun a i b => f1 a b i, f2, pm, i1,
      fun u => i2 ⟨u.val % L2 d, Nat.mod_lt _ (L2_pos d)⟩ u rfl⟩, ⟨sp, ca⟩⟩
  · rintro ⟨tr, c⟩
    exact ⟨tr.pack, fun a b i => tr.first a i b, tr.second, tr.point, tr.third,
      fun _ u _ => tr.coeff u, c.spacer, c.gate⟩

/-- The original external `Fin (4*d)` relation, with all Boolean gate checks and no hypotheses
on the transform, the canonical witnesses or their range. -/
theorem allChecks_parsimony {d : ℕ} (hd : 1 ≤ d) (x : Fin (4*d) → Bool) :
    let isMult := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
      bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
      bitsToNat (fun i : Fin (2*d) => x ⟨2*d + i.val, by omega⟩)
    (isMult → ∃! p : Transcript d, AllChecks x p) ∧
      (¬ isMult → ¬ ∃ p : Transcript d, AllChecks x p) := by
  simp only [allChecks_iff]
  exact transcript_parsimony hd x

/-- A bit packer reads only the input indices whose quotient is its limb index. -/
theorem bitWindow_congr {s k j : ℕ} (x y : Fin s → Bool)
    (h : ∀ i : Fin s, i.val / k = j → x i = y i) : bitWindow x k j = bitWindow y k j := by
  funext b
  by_cases hb : k*j+b.val < s
  · simp only [bitWindow, dif_pos hb]
    apply h
    change (k*j+b.val)/k = j
    rw [Nat.mul_add_div ((Nat.zero_le b.val).trans_lt b.isLt), Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  · simp only [bitWindow, dif_neg hb]

theorem packCheck_congr {d : ℕ} (x y : Fin (4*d) → Bool) (p q : Transcript d)
    (a : Bool) (u : Fin (n0 d)) (hout : p.packed a u = q.packed a u)
    (hin : ∀ i : Fin d, i.val / k d = u.val → operand x a i = operand y a i) :
    packCheck x p a u = packCheck y q a u := by
  simp only [packCheck, packedGate, inputDigit, hout, bitWindow_congr _ _ hin]
  rfl

private theorem firstGate_congr {d : ℕ} (p q : Fin (n0 d) → Word d) (b : Fin (L2 d))
    (h : ∀ u : Fin (n0 d), u.val % L2 d = b.val → p u = q u) (i : Fin (L1 d)) :
    firstGate (d := d) p i b = firstGate (d := d) q i b := by
  have hr (j : ℕ) : readPacked (d := d) p (L2 d*j+b.val) = readPacked (d := d) q (L2 d*j+b.val) := by
    by_cases hj : L2 d*j+b.val < n0 d
    · simp only [readPacked, dif_pos hj]
      rw [h ⟨_,hj⟩ (by change (L2 d*j+b.val) % L2 d = b.val; simp [Nat.mod_eq_of_lt b.isLt])]
    · simp only [readPacked, dif_neg hj]
  simp only [firstGate, fwd1, hr]

theorem forward1Check_congr {d : ℕ} (p q : Transcript d) (a : Bool) (b : Fin (L2 d))
    (hin : ∀ u : Fin (n0 d), u.val % L2 d = b.val → p.packed a u = q.packed a u)
    (hout : ∀ i, p.forwardMiddle a i b = q.forwardMiddle a i b) :
    forward1Check p a b = forward1Check q a b := by
  unfold forward1Check
  apply decide_eq_decide.mpr
  simp only [hout, firstGate_congr _ _ b hin]

private theorem readGrid_row {d : ℕ} (p q : Grid d (Word d)) (i : Fin (L1 d))
    (h : ∀ t, p i t = q i t) (j : ℕ) : readGrid (d := d) p i.val j = readGrid (d := d) q i.val j := by
  by_cases hj : j < L2 d <;> simp only [readGrid, dif_pos i.isLt, hj, dif_pos, dif_neg, h, not_false_eq_true]

private theorem readGrid_column {d : ℕ} (p q : Grid d (Word d)) (b : Fin (L2 d))
    (h : ∀ i, p i b = q i b) (j : ℕ) : readGrid (d := d) p j b.val = readGrid (d := d) q j b.val := by
  by_cases hj : j < L1 d <;> simp only [readGrid, dif_pos b.isLt, hj, dif_pos, dif_neg, h, not_false_eq_true]

theorem forward2Check_congr {d : ℕ} (p q : Transcript d) (a : Bool) (i : Fin (L1 d))
    (hin : ∀ b, p.forwardMiddle a i b = q.forwardMiddle a i b)
    (hout : ∀ t, p.forwardPoint a i t = q.forwardPoint a i t) :
    forward2Check p a i = forward2Check q a i := by
  simp only [forward2Check, secondGate, fwd2, hout, readGrid_row _ _ i hin]
  rfl

theorem pointCheck_congr {d : ℕ} (p q : Transcript d) (i : Fin (L1 d)) (t : Fin (L2 d))
    (hin : ∀ a, p.forwardPoint a i t = q.forwardPoint a i t)
    (hout : p.pointInverse i t = q.pointInverse i t) : pointCheck p i t = pointCheck q i t := by
  simp only [pointCheck, pointGate, hin, hout]
  rfl

theorem inverse1Check_congr {d : ℕ} (p q : Transcript d) (i : Fin (L1 d))
    (hin : ∀ t, p.pointInverse i t = q.pointInverse i t)
    (hout : ∀ b, p.inverseMiddle i b = q.inverseMiddle i b) : inverse1Check p i = inverse1Check q i := by
  simp only [inverse1Check, thirdGate, inv1, hout, readGrid_row _ _ i hin]
  rfl

theorem inverse2Check_congr {d : ℕ} (p q : Transcript d) (b : Fin (L2 d))
    (hin : ∀ i, p.inverseMiddle i b = q.inverseMiddle i b)
    (hout : ∀ u : Fin (ncoef d), u.val % L2 d = b.val → p.coefficient u = q.coefficient u) :
    inverse2Check p b = inverse2Check q b := by
  have hgate (u : Fin (ncoef d)) (hu : u.val % L2 d = b.val) :
      coeffGate (d := d) p.inverseMiddle u = coeffGate (d := d) q.inverseMiddle u := by
    simp only [coeffGate, inv2, hu, readGrid_column _ _ b hin]
  simp only [inverse2Check, decide_eq_decide]
  constructor <;> intro H u hu
  · rw [← hout u hu, ← hgate u hu]; exact H u hu
  · rw [hout u hu, hgate u hu]; exact H u hu

theorem spacerCheck_congr {d : ℕ} (p q : Transcript d) (j : Fin (ncoef d-1))
    (hl : p.carryLeft j = q.carryLeft j) (hr : p.carryRight j = q.carryRight j) :
    spacerCheck p j = spacerCheck q j := by simp only [spacerCheck, hl, hr]

private theorem atLink_congr {d : ℕ} (p q : Fin (ncoef d-1) → Word d) (n : ℕ)
    (h : ∀ j : Fin (ncoef d-1), j.val+1 = n → p j = q j) :
    atLink (d := d) p n = atLink (d := d) q n := by
  by_cases hn : 0 < n ∧ n < ncoef d
  · simp only [atLink, dif_pos hn]
    rw [h ⟨n-1, by omega⟩ (by change n-1+1 = n; omega)]
  · simp only [atLink, dif_neg hn]

theorem carryCheck_congr {d : ℕ} (x y : Fin (4*d) → Bool) (p q : Transcript d) (u : Fin (ncoef d))
    (hc : p.coefficient u = q.coefficient u)
    (hi : ∀ j : Fin (ncoef d-1), j.val+1 = u.val → p.carryRight j = q.carryRight j)
    (ho : ∀ j : Fin (ncoef d-1), j.val = u.val → p.carryLeft j = q.carryLeft j)
    (hz : ∀ j : Fin (2*d), j.val / k d = u.val → output x j = output y j) :
    carryCheck x p u = carryCheck y q u := by
  have hright := atLink_congr (d := d) _ _ _ hi
  have hleft := atLink_congr (d := d) p.carryLeft q.carryLeft (u.val+1)
    (fun j hj => ho j (by omega))
  simp only [carryCheck, hc, hright, hleft, outputDigit, bitWindow_congr _ _ hz]
  rfl

end DetDLP.w4_M5TranscriptBridge


