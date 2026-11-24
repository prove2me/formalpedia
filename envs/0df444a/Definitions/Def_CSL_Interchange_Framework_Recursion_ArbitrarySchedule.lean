-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_ArbitrarySchedule
-- name    : CSL_Interchange_Framework_Recursion_ArbitrarySchedule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:56:40.586169+00:00
-- url     : https://prove2.me/theorems/e04d6f85-b37e-4b39-ac12-3b440341de5e
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / ArbitrarySchedule
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.ArbitrarySchedule` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Cost arithmetic behind the proposed external-memory implementation
--
--   The following results solve numerical recurrences and prove bookkeeping
--   inequalities.  The hypotheses are explicit: these results do not define an I/O
--   machine or prove that the proposed algorithm obeys a particular recurrence.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.ArbitrarySchedule

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_NormalizationComplete
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_CSL_Shared_Memory_Address
import Definitions.Def_CSL_Shared_Memory_Streams
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin

section Recurrence
/-!
# Cost arithmetic behind the proposed external-memory implementation

The following results solve numerical recurrences and prove bookkeeping
inequalities.  The hypotheses are explicit: these results do not define an I/O
machine or prove that the proposed algorithm obeys a particular recurrence.
-/

namespace CSL.Recurrence

/-- Closed form of a recurrence with an arbitrary initial upper bound. -/
theorem affine_recurrence_bound
    (F : ℕ → ℝ) (lambda C A : ℝ)
    (hlambda : 0 ≤ lambda) (hne : lambda ≠ 1)
    (hbase : F 0 ≤ A)
    (hstep : ∀ k, F (k + 1) ≤ lambda * F k + C) :
    ∀ k, F k ≤ lambda ^ k * (A + C / (lambda - 1)) - C / (lambda - 1) := by
  have hden : lambda - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hshift : lambda * (C / (lambda - 1)) - C / (lambda - 1) = C := by
    field_simp [hden]
    try ring
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hlambda
    have hrec := hstep k
    rw [pow_succ]
    nlinarith

/-- The degenerate multiplier-one case has linear rather than geometric cost. -/
theorem unit_recurrence_bound
    (F : ℕ → ℝ) (C A : ℝ)
    (hbase : F 0 ≤ A) (hstep : ∀ k, F (k + 1) ≤ F k + C) :
    ∀ k, F k ≤ A + (k : ℝ) * C := by
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hrec := hstep k
    push_cast
    linarith

/-- A strict gap between the recurrence multiplier and a chosen growth base
absorbs the additive cost of every level.  In the paper the chosen base is
`m^tau`, once its strict separation from `S/W` has been established. -/
theorem power_bound
    (F : ℕ → ℝ) (lambda C K R : ℝ)
    (hlambda : 0 ≤ lambda) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hbase : F 0 ≤ K) (hgap : C ≤ K * (R - lambda))
    (hstep : ∀ k, F (k + 1) ≤ lambda * F k + C) :
    ∀ k, F k ≤ K * R ^ k := by
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hpow : 1 ≤ R ^ k := one_le_pow₀ hR
    have hpow0 : 0 ≤ R ^ k := le_trans (by norm_num) hpow
    have hmul := mul_le_mul_of_nonneg_left ih hlambda
    have hconst := mul_le_mul_of_nonneg_left hpow hC
    have hbudget := mul_le_mul_of_nonneg_right hgap hpow0
    have hrec := hstep k
    rw [pow_succ]
    nlinarith

/-- Explicit construction of a constant for any strictly larger growth base. -/
theorem exists_power_bound
    (F : ℕ → ℝ) (lambda C A R : ℝ)
    (hlambda : 0 ≤ lambda) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hR : 1 ≤ R) (hgap : lambda < R)
    (hbase : F 0 ≤ A)
    (hstep : ∀ k, F (k + 1) ≤ lambda * F k + C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k, F k ≤ K * R ^ k := by
  let K := A + C / (R - lambda)
  have hden : 0 < R - lambda := sub_pos.mpr hgap
  have hdiv : 0 ≤ C / (R - lambda) := div_nonneg hC (le_of_lt hden)
  have hK : 0 ≤ K := add_nonneg hA hdiv
  have hbaseK : F 0 ≤ K := le_trans hbase (le_add_of_nonneg_right hdiv)
  have hbudget : C ≤ K * (R - lambda) := by
    try dsimp [K]
    have hid : (C / (R - lambda)) * (R - lambda) = C :=
      div_mul_cancel₀ C (ne_of_gt hden)
    have hnonneg := mul_nonneg hA (le_of_lt hden)
    nlinarith
  exact ⟨K, hK, power_bound F lambda C K R hlambda hC hR hbaseK hbudget hstep⟩

/-- The total child volume at depth k is the parent's volume times (S/W)^k.
This is arithmetic only: equal-volume child streams must be proved separately. -/
theorem total_child_volume (S W V : ℝ) (k : ℕ) :
    S ^ k * (V / W ^ k) = V * (S / W) ^ k := by
  rw [div_pow]
  ring

/-- Specialization to the paper's explicit parameters.  This checks the
analytic implication from the displayed recurrence; it does not assert that
an external-memory execution satisfies that recurrence. -/
theorem paper_normalized_recurrence_bound
    (F : ℕ → ℝ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : F 0 ≤ A)
    (hstep : ∀ k, F (k + 1) ≤
      ((Parameters.S : ℝ) / (Parameters.W : ℝ)) * F k + C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k, F k ≤
      K * (Parameters.m : ℝ) ^ ((k : ℝ) * (1 - (Parameters.epsilon : ℝ))) := by
  have hlam : 0 ≤ (Parameters.S : ℝ) / (Parameters.W : ℝ) := by positivity
  have hm : (1 : ℝ) ≤ (Parameters.m : ℝ) := by norm_num [Parameters.m_value]
  have heps : (Parameters.epsilon : ℝ) < 1 := by
    exact_mod_cast Parameters.epsilon_lt_one
  have hR : (1 : ℝ) ≤ (Parameters.m : ℝ) ^ (1 - (Parameters.epsilon : ℝ)) :=
    Real.one_le_rpow hm (by linarith)
  obtain ⟨K, hK, hbound⟩ := exists_power_bound F
    ((Parameters.S : ℝ) / (Parameters.W : ℝ)) C A
    ((Parameters.m : ℝ) ^ (1 - (Parameters.epsilon : ℝ)))
    hlam hC hA hR Parameters.strict_exponent_gap hbase hstep
  refine ⟨K, hK, fun k => ?_⟩
  have hid : (Parameters.m : ℝ) ^ ((k : ℝ) * (1 - (Parameters.epsilon : ℝ))) =
      ((Parameters.m : ℝ) ^ (1 - (Parameters.epsilon : ℝ))) ^ k := by
    rw [mul_comm, Real.rpow_mul_natCast (by positivity)]
  rw [hid]
  exact hbound k

/-- Integer form of the per-call start-up absorption argument. -/
theorem child_at_least_one_block
    (V W block : ℕ) (hW : 0 < W) (hlarge : W * block ≤ V) :
    block ≤ V / W := by
  exact (Nat.le_div_iff_mul_le hW).2 (by simpa [Nat.mul_comm] using hlarge)

/-- A constant start-up charge is covered by twice the scan charge whenever
the volume is at least one block. -/
theorem absorb_startup (V block : ℝ) (hblock : 0 < block) (hV : block ≤ V) :
    1 + V / block ≤ 2 * (V / block) := by
  have hratio : 1 ≤ V / block := (le_div_iff₀ hblock).2 (by simpa using hV)
  linarith

/-- Two width-e q-ary coordinates have q^(2e) possible value pairs. -/
theorem pair_buffer_count (q e : ℕ) : (q ^ e) ^ 2 = q ^ (2 * e) := by
  rw [← pow_mul]
  congr 1
  omega

/-- The memory cutoff inequality: e ≤ t and 8t ≤ L imply 8e ≤ L. 
-/
theorem cutoff_exponent (e t L : ℕ) (he : e ≤ t) (ht : 8 * t ≤ L) :
    4 * (2 * e) ≤ L := by omega

/-- Columnsort's concrete shape satisfies its numerical side conditions. -/
theorem columnsort_shape (s : ℕ) (hs : 3 ≤ s) :
    s ∣ s ^ 3 ∧ 2 * s * (s + 1) ≤ s ^ 3 := by
  constructor
  · refine ⟨s ^ 2, ?_⟩
    ring
  · have h : 0 ≤ (s : ℤ) * ((s : ℤ) - 3) * ((s : ℤ) + 1) := by
      have hs' : 3 ≤ (s : ℤ) := by exact_mod_cast hs
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hs' : 3 ≤ (s : ℤ) := by exact_mod_cast hs
    have hz : 2 * (s : ℤ) * ((s : ℤ) + 1) ≤ (s : ℤ) ^ 3 := by
      nlinarith
    exact_mod_cast hz

/-- Number of chunks obtained by cutting n entries into chunks of size c. -/
def chunkCount (n c : ℕ) : ℕ := (n + c - 1) / c

/-- For n at least one chunk, rounding up the chunk count costs at most two
times the original volume. -/
theorem chunk_count_volume (n c : ℕ) (hc : c ≤ n) :
    chunkCount n c * c ≤ 2 * n := by
  unfold chunkCount
  have h := Nat.div_mul_le_self (n + c - 1) c
  omega

/-- The auxiliary table of Section 7 has at most scan-order many entries:
the count of entries times B is at most 2n.  This is an exact integer bound. -/
theorem bucket_metadata_bound
    (n H B K : ℕ) (hn : H ^ 2 ≤ n) (hB : B ≤ H) (hK : K ≤ H) :
    chunkCount n (H ^ 2) * K * B ≤ 2 * n := by
  have hprod : K * B ≤ H ^ 2 := by
    calc
      K * B ≤ H * B := Nat.mul_le_mul_right B hK
      _ ≤ H * H := Nat.mul_le_mul_left H hB
      _ = H ^ 2 := by ring
  have hmul := Nat.mul_le_mul_left (chunkCount n (H ^ 2)) hprod
  have htotal := chunk_count_volume n (H ^ 2) hn
  nlinarith

/-- The two logarithmic inequalities used to simplify the large-input bound. -/
theorem large_input_log_relations
    (N M : ℝ) (hM : 1 ≤ M) (hN : M ^ 2 ≤ N) :
    Real.log M ≤ Real.log (N / M) ∧ Real.log N ≤ 2 * Real.log (N / M) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hMsq : 0 < M ^ 2 := pow_pos hMpos 2
  have hNpos : 0 < N := lt_of_lt_of_le hMsq hN
  have hlog := Real.log_le_log hMsq hN
  rw [Real.log_pow] at hlog
  rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hMpos)]
  norm_num at hlog
  constructor <;> linarith

end CSL.Recurrence
end Recurrence

section ArbitraryShapes
/-! Moving high digits into the prefix and adding padding. This file proves the address identities and data-preservation properties used in Appendix C. Padding may change during intermediate coding operations. The completed transformation preserves prefix segments, allowing the added segments to be removed afterward. 









-/

namespace CSL.ArbitraryShapes

open Address

variable {Prefix High Low Gap Suffix Value : Type*}

abbrev Original := FullAddress Prefix (High × Low) Gap Suffix
abbrev Borrowed := FullAddress (Prefix × High × High) Low Gap Suffix

/-- Before the low-field call, the two high parts become additional prefixes.
The prefix records the original D-high before the original H-high. -/
def borrow (a : Original (Prefix := Prefix) (High := High) (Low := Low)
    (Gap := Gap) (Suffix := Suffix)) :
    Borrowed (Prefix := Prefix) (High := High) (Low := Low) (Gap := Gap) (Suffix := Suffix) :=
  ⟨(a.prefixCoord, a.low.1, a.high.1), a.high.2, a.gap, a.low.2, a.suffix⟩

def unborrow (a : Borrowed (Prefix := Prefix) (High := High) (Low := Low)
    (Gap := Gap) (Suffix := Suffix)) :
    Original (Prefix := Prefix) (High := High) (Low := Low) (Gap := Gap) (Suffix := Suffix) :=
  ⟨a.prefixCoord.1, (a.prefixCoord.2.2, a.high), a.gap,
    (a.prefixCoord.2.1, a.low), a.suffix⟩

def finish (a : Borrowed (Prefix := Prefix) (High := High) (Low := Low)
    (Gap := Gap) (Suffix := Suffix)) :
    Original (Prefix := Prefix) (High := High) (Low := Low) (Gap := Gap) (Suffix := Suffix) :=
  ⟨a.prefixCoord.1, (a.prefixCoord.2.1, a.high), a.gap,
    (a.prefixCoord.2.2, a.low), a.suffix⟩

def borrowEquiv : Original (Prefix := Prefix) (High := High) (Low := Low)
    (Gap := Gap) (Suffix := Suffix) ≃
    Borrowed (Prefix := Prefix) (High := High) (Low := Low) (Gap := Gap) (Suffix := Suffix) where
  toFun := borrow
  invFun := unborrow
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

def finishEquiv : Borrowed (Prefix := Prefix) (High := High) (Low := Low)
    (Gap := Gap) (Suffix := Suffix) ≃
    Original (Prefix := Prefix) (High := High) (Low := Low) (Gap := Gap) (Suffix := Suffix) where
  toFun := finish
  invFun a := ⟨(a.prefixCoord, a.high.1, a.low.1), a.high.2,
    a.gap, a.low.2, a.suffix⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

/-- The three-stage address schedule swaps BOTH high and low parts. -/
theorem borrowing_exchange (a : Original (Prefix := Prefix) (High := High)
    (Low := Low) (Gap := Gap) (Suffix := Suffix)) :
    finish (exchange (borrow a)) = exchange a := by
  cases a
  rfl

theorem borrowing_exchange_equiv :
    (borrowEquiv (Prefix := Prefix) (High := High) (Low := Low)
      (Gap := Gap) (Suffix := Suffix)).trans
        (exchangeEquiv.trans finishEquiv) = exchangeEquiv := by
  ext a
  exact borrowing_exchange a

def move {A B : Type*} (e : A ≃ B) (F : A → Value) : B → Value :=
  fun b => F (e.symm b)

/-- The data, not just addresses, reaches the complete swapped destination. -/
theorem borrowing_preserves_payload
    (F : Original (Prefix := Prefix) (High := High) (Low := Low)
      (Gap := Gap) (Suffix := Suffix) → Value)
    (a : Original (Prefix := Prefix) (High := High) (Low := Low) (Gap := Gap) (Suffix := Suffix)) :
    move finishEquiv (move exchangeEquiv (move borrowEquiv F))
      (exchange a) = F a := by
  cases a
  rfl

/-- The smallest multiple of C at least R, for a positive padding unit C. -/
def paddedCount (R C : ℕ) : ℕ := C * ((R+C-1)/C)

theorem paddedCount_multiple (R C : ℕ) : C ∣ paddedCount R C :=
  ⟨(R+C-1)/C, rfl⟩

theorem paddedCount_ge (R C : ℕ) (hC : 0 < C) : R ≤ paddedCount R C := by
  have h := Nat.mod_lt (R+C-1) hC
  have he := Nat.mod_add_div (R+C-1) C
  unfold paddedCount
  omega

theorem paddedCount_lt_add (R C : ℕ) (hC : 0 < C) :
    paddedCount R C < R+C := by
  have h := Nat.mul_div_le (R+C-1) C
  unfold paddedCount
  omega

theorem paddedCount_lt_twice (R C : ℕ) (hC : 0 < C) (hR : C ≤ R) :
    paddedCount R C < 2*R := by
  have h := paddedCount_lt_add R C hC
  omega

section Padding

variable {R R' : ℕ} {Inner : Type*} [Zero Value]

def padRows (F : Fin R → Inner → Value) : Fin R' → Inner → Value :=
  fun r x => if h : r.val < R then F ⟨r.val,h⟩ x else 0

def restrictRows (h : R ≤ R') (F : Fin R' → Inner → Value) :
    Fin R → Inner → Value := fun r => F (r.castLE h)

theorem restrict_pad (h : R ≤ R') (F : Fin R → Inner → Value) :
    restrictRows h (padRows F) = F := by
  funext r x
  simp [restrictRows, padRows, r.isLt]

def insideRows (e : Inner ≃ Inner) (F : Fin R → Inner → Value) :
    Fin R → Inner → Value := fun r x => F r (e.symm x)

theorem padding_commutes (e : Inner ≃ Inner) (F : Fin R → Inner → Value) :
    insideRows e (padRows (R' := R') F) = padRows (insideRows e F) := rfl

theorem completed_transform_padding_zero (e : Inner ≃ Inner)
    (F : Fin R → Inner → Value) (r : Fin R') (hr : R ≤ r.val) (x : Inner) :
    insideRows e (padRows F) r x = 0 := by
  simp [insideRows, padRows, Nat.not_lt.mpr hr]

/-- Removing padded rows after the WHOLE call recovers the exact result. -/
theorem completed_transform_restrict (h : R ≤ R') (e : Inner ≃ Inner)
    (F : Fin R → Inner → Value) :
    restrictRows h (insideRows e (padRows F)) = insideRows e F := by
  rw [padding_commutes, restrict_pad]

end Padding

end CSL.ArbitraryShapes
end ArbitraryShapes

section ArbitrarySchedule
/-!
# The executable width schedule of Appendix C

`scales` emits the radix expansion as a list of recursive depths.  Every
entry is one actual short-field call.  Its cost is the sum over that list,
not a postulated bound for an arbitrary-width exchange.
-/

namespace CSL.ArbitrarySchedule

open Address ArbitraryShapes
open scoped BigOperators

def scales (m : ℕ) : ℕ → ℕ → List ℕ
  | 0, n => List.replicate n 0
  | k+1, n => List.replicate (n % m) 0 ++ (scales m k (n / m)).map Nat.succ

theorem scales_width (m k n : ℕ) :
    ((scales m k n).map (fun j => m ^ j)).sum = n := by
  induction k generalizing n with
  | zero => simp [scales]
  | succ k ih =>
    simp only [scales, List.map_append, List.sum_append, List.map_replicate,
      pow_zero, List.sum_replicate, smul_eq_mul, Nat.mul_one, List.map_map]
    have h : ((scales m k (n / m)).map (fun j => m ^ (j+1))).sum =
        m * ((scales m k (n / m)).map (fun j => m ^ j)).sum := by
      induction scales m k (n / m) with
      | nil => simp
      | cons j js ih =>
        simp only [List.map_cons, List.sum_cons, Nat.mul_add] at *
        rw [ih, pow_succ, Nat.mul_comm (m^j) m]
    change n % m + ((scales m k (n / m)).map (fun j => m ^ (j+1))).sum = n
    rw [h, ih]
    exact Nat.mod_add_div n m

theorem scales_depth (m k n j : ℕ) (hj : j ∈ scales m k n) : j ≤ k := by
  induction k generalizing n j with
  | zero =>
    have : j = 0 := (List.mem_replicate.mp hj).2
    omega
  | succ k ih =>
    rcases List.mem_append.mp hj with h | h
    · have : j = 0 := (List.mem_replicate.mp h).2
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      have := ih _ _ hi
      omega

def scaleWeight (b : ℝ) (js : List ℕ) : ℝ := (js.map (fun j => b ^ j)).sum

def geometric (b : ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => 1 + b * geometric b k

theorem scaleWeight_step (m k n : ℕ) (b : ℝ) :
    scaleWeight b (scales m (k+1) n) =
      (n % m : ℕ) + b * scaleWeight b (scales m k (n / m)) := by
  simp only [scaleWeight, scales, List.map_append, List.sum_append,
    List.map_replicate, pow_zero, List.sum_replicate, nsmul_eq_mul, mul_one,
    List.map_map]
  change (n % m : ℝ) + ((scales m k (n / m)).map (fun j => b^(j+1))).sum = _
  congr 1
  induction (scales m k (n / m)) with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons, List.sum_cons, mul_add] at *
    rw [ih, pow_succ]
    ring

theorem scaleWeight_bound (m k n : ℕ) (hm : 1 < m)
    (hn : n < m ^ (k+1)) (b : ℝ) (hb : 0 ≤ b) :
    scaleWeight b (scales m k n) ≤ (m-1 : ℕ) * geometric b k := by
  induction k generalizing n with
  | zero =>
    have hn' : n ≤ m-1 := by simpa using (Nat.le_sub_one_of_lt (by simpa using hn))
    simpa [scaleWeight, scales, geometric] using (show (n : ℝ) ≤ (m-1 : ℕ) by exact_mod_cast hn')
  | succ k ih =>
    have hr : n % m ≤ m-1 := Nat.le_sub_one_of_lt (Nat.mod_lt n (by omega))
    have hq : n / m < m ^ (k+1) := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      simpa [pow_succ, Nat.mul_comm] using hn
    have hrec := mul_le_mul_of_nonneg_left (ih _ hq) hb
    have hr' : (n % m : ℕ) ≤ (m-1 : ℕ) := hr
    have hrR : (n % m : ℕ) ≤ (m-1 : ℕ) := hr'
    have hrReal : ((n % m : ℕ) : ℝ) ≤ ((m-1 : ℕ) : ℝ) := by exact_mod_cast hrR
    rw [scaleWeight_step, geometric]
    nlinarith

theorem geometric_nonneg (b : ℝ) (hb : 0 ≤ b) (k : ℕ) : 0 ≤ geometric b k := by
  induction k with
  | zero => norm_num [geometric]
  | succ k ih => simpa [geometric] using add_nonneg (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg hb ih)

theorem depth_le_geometric (b : ℝ) (hb : 1 ≤ b) (k : ℕ) :
    (k+1 : ℕ) ≤ geometric b k := by
  induction k with
  | zero => simp [geometric]
  | succ k ih =>
    have hg := geometric_nonneg b (by linarith) k
    have := mul_le_mul_of_nonneg_right hb hg
    simp only [geometric, Nat.cast_add, Nat.cast_one] at *
    linarith

theorem geometric_power_bound (b : ℝ) (hb : 1 < b) (k : ℕ) :
    geometric b k ≤ b / (b-1) * b ^ k := by
  have hden : 0 < b-1 := by linarith
  have hid : geometric b k * (b-1) = b^(k+1)-1 := by
    induction k with
    | zero => simp [geometric]
    | succ k ih => rw [geometric, pow_succ]; nlinarith
  calc
    geometric b k ≤ (b^(k+1))/(b-1) := by
      apply (le_div_iff₀ hden).2
      linarith
    _ = b / (b-1) * b^k := by
      field_simp
      ring

/-- Each emitted depth j stands for one width `t₀*m^j`; a single remainder
field is emitted last, including an empty remainder when the width divides. -/
def widths (m t₀ k e : ℕ) : List ℕ :=
  (scales m k (e / t₀)).map (fun j => t₀ * m^j) ++ [e % t₀]

theorem widths_sum (m t₀ k e : ℕ) : (widths m t₀ k e).sum = e := by
  unfold widths
  rw [List.sum_append, List.sum_singleton]
  have h : ((scales m k (e/t₀)).map (fun j => t₀*m^j)).sum =
      t₀ * ((scales m k (e/t₀)).map (fun j => m^j)).sum := by
    induction scales m k (e/t₀) with
    | nil => simp
    | cons j js ih => simp [ih, Nat.mul_add]
  rw [h, scales_width]
  exact Nat.div_add_mod e t₀

def depth (m t₀ e : ℕ) : ℕ := Nat.log m (e / t₀)

theorem quotient_depth_bound (m t₀ e : ℕ) (hm : 1 < m) :
    e / t₀ < m ^ (depth m t₀ e + 1) := Nat.lt_pow_succ_log_self hm _

def borrowConstant (q W : ℕ) : ℕ := Nat.clog (q^2) W
def borrowedWidth (q W k : ℕ) : ℕ := borrowConstant q W * (k+1)

theorem borrowed_rows_enough (q W k : ℕ) (hq : 1 < q) :
    W^(k+1) ≤ q^(2 * borrowedWidth q W k) := by
  have hq2 : 1 < q^2 := by nlinarith
  have hw := Nat.le_pow_clog hq2 W
  have hp := Nat.pow_le_pow_left hw (k+1)
  simpa only [borrowedWidth, borrowConstant, ← pow_mul, Nat.mul_assoc] using hp

theorem all_depths_divide_padding (q W k j : ℕ) (hW : 0 < W) (hj : j ≤ k) :
    W^j ∣ paddedCount (q^(2*borrowedWidth q W k)) (W^(k+1)) := by
  exact dvd_trans (pow_dvd_pow W (by omega)) (paddedCount_multiple _ _)

theorem borrowing_padding_lt_twice (q W k : ℕ) (hq : 1 < q) (hW : 0 < W) :
    paddedCount (q^(2*borrowedWidth q W k)) (W^(k+1)) <
      2 * q^(2*borrowedWidth q W k) :=
  paddedCount_lt_twice _ _ (pow_pos hW _) (borrowed_rows_enough q W k hq)

section ChunkExecution

variable {ι : Type*} [DecidableEq ι] {Digit : ι → Type*}
variable {Prefix Gap Suffix : Type*}

/-- One corresponding pair of chunks is exchanged. Every other chunk and
all prefix/gap/suffix coordinates stay in place. -/
def swapChunk (i : ι)
    (a : FullAddress Prefix (∀ j, Digit j) Gap Suffix) :
    FullAddress Prefix (∀ j, Digit j) Gap Suffix :=
  ⟨a.prefixCoord, (fun j => if j=i then a.low j else a.high j), a.gap,
    (fun j => if j=i then a.high j else a.low j), a.suffix⟩

def runChunks : List ι → FullAddress Prefix (∀ j, Digit j) Gap Suffix →
    FullAddress Prefix (∀ j, Digit j) Gap Suffix
  | [], a => a
  | i::is, a => runChunks is (swapChunk i a)

theorem runChunks_spec (is : List ι) (hn : is.Nodup)
    (a : FullAddress Prefix (∀ j, Digit j) Gap Suffix) :
    runChunks is a =
      ⟨a.prefixCoord, (fun j => if j∈is then a.low j else a.high j), a.gap,
        (fun j => if j∈is then a.high j else a.low j), a.suffix⟩ := by
  induction is generalizing a with
  | nil => simp [runChunks]
  | cons i is ih =>
    obtain ⟨hi, hn⟩ := List.nodup_cons.mp hn
    rw [runChunks, ih hn]
    simp only [swapChunk]
    congr 1 <;> funext j <;> by_cases hji : j=i <;> simp [hji, hi, List.mem_cons]

theorem runChunks_correct [Fintype ι]
    (a : FullAddress Prefix (∀ j, Digit j) Gap Suffix) :
    runChunks (Finset.univ : Finset ι).toList a = exchange a := by
  rw [runChunks_spec _ (Finset.nodup_toList _)]
  simp [exchange]

noncomputable def chunkExchange [Fintype ι] : Equiv.Perm (FullAddress Prefix (∀ j, Digit j) Gap Suffix) where
  toFun := runChunks Finset.univ.toList
  invFun := runChunks Finset.univ.toList
  left_inv a := by simp only [runChunks_correct]; cases a; rfl
  right_inv a := by simp only [runChunks_correct]; cases a; rfl

theorem chunkExchange_eq [Fintype ι] :
    (chunkExchange : Equiv.Perm (FullAddress Prefix (∀ j, Digit j) Gap Suffix)) =
      exchangeEquiv := by
  ext a
  exact runChunks_correct a

/-- The complete chunk program, followed by high-digit restoration, swaps
the original long fields. It is an execution of all emitted chunks. -/
theorem borrowed_chunk_execution [Fintype ι] {High : Type*}
    (a : Original (Prefix := Prefix) (High := High) (Low := ∀ j, Digit j)
      (Gap := Gap) (Suffix := Suffix)) :
    finish (runChunks (Finset.univ : Finset ι).toList (borrow a)) = exchange a := by
  rw [runChunks_correct]
  exact borrowing_exchange a

end ChunkExecution

/-- The j-th emitted chunk contains exactly the digits of that list entry.
The ordered sigma equivalence below locates them consecutively. -/
abbrev ChunkDigits (ws : List ℕ) (Digit : Type*) :=
  (i : Fin ws.length) → Fin (ws.get i) → Digit

def chunkPosition (ws : List ℕ) :
    ((i : Fin ws.length) × Fin (ws.get i)) ≃
      Fin (∑ i : Fin ws.length, ws.get i) := finSigmaFinEquiv

theorem chunkPosition_order (ws : List ℕ)
    (x : (i : Fin ws.length) × Fin (ws.get i)) :
    (chunkPosition ws x : ℕ) =
      (∑ i : Fin x.1, ws.get (Fin.castLE x.1.2.le i)) + x.2 :=
  finSigmaFinEquiv_apply x

theorem chunkPosition_size (ws : List ℕ) :
    (∑ i : Fin ws.length, ws.get i) = ws.sum := by
  simpa using List.sum_ofFn (fun i : Fin ws.length => ws.get i)

theorem scheduled_position_size (m t₀ k e : ℕ) :
    (∑ i : Fin (widths m t₀ k e).length, (widths m t₀ k e).get i) = e := by
  rw [chunkPosition_size, widths_sum]

def chunkFieldEquiv (ws : List ℕ) (Digit : Type*) :
    ChunkDigits ws Digit ≃ (Fin (∑ i : Fin ws.length, ws.get i) → Digit) where
  toFun f p := f ((chunkPosition ws).symm p).1 ((chunkPosition ws).symm p).2
  invFun f i j := f (chunkPosition ws ⟨i,j⟩)
  left_inv f := by
    funext i j
    change f ((chunkPosition ws).symm ((chunkPosition ws) ⟨i,j⟩)).1
      ((chunkPosition ws).symm ((chunkPosition ws) ⟨i,j⟩)).2 = f i j
    rw [Equiv.symm_apply_apply]
  right_inv f := by
    funext p
    change f ((chunkPosition ws) ((chunkPosition ws).symm p)) = f p
    rw [Equiv.apply_symm_apply]

theorem chunkField_card (ws : List ℕ) (q : ℕ) :
    Fintype.card (ChunkDigits ws (Fin q)) = q ^ ws.sum := by
  rw [Fintype.card_congr (chunkFieldEquiv ws (Fin q)), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, chunkPosition_size]

/-- Padding wraps the actual list of chunk operations. Padding rows may
be arbitrary during a recursive subroutine; it is only after the completed
program that the following theorem removes them. -/
noncomputable def paddedChunkProgram {Rows Rows' : ℕ} {ws : List ℕ}
    {Digit Prefix Gap Suffix Value : Type*} [Zero Value]
    (hrows : Rows ≤ Rows')
    (F : Fin Rows → FullAddress Prefix (ChunkDigits ws Digit) Gap Suffix → Value) :
    Fin Rows → FullAddress Prefix (ChunkDigits ws Digit) Gap Suffix → Value :=
  restrictRows hrows (insideRows chunkExchange (padRows F))

theorem paddedChunkProgram_correct {Rows Rows' : ℕ} {ws : List ℕ}
    {Digit Prefix Gap Suffix Value : Type*} [Zero Value]
    (hrows : Rows ≤ Rows')
    (F : Fin Rows → FullAddress Prefix (ChunkDigits ws Digit) Gap Suffix → Value) :
    paddedChunkProgram hrows F = insideRows exchangeEquiv F := by
  unfold paddedChunkProgram
  rw [chunkExchange_eq]
  exact completed_transform_restrict hrows exchangeEquiv F

theorem padded_volume_lt_twice (q W k inner : ℕ)
    (hq : 1 < q) (hW : 0 < W) (hinner : 0 < inner) :
    paddedCount (q^(2*borrowedWidth q W k)) (W^(k+1)) * inner <
      2 * (q^(2*borrowedWidth q W k) * inner) := by
  have := Nat.mul_lt_mul_of_pos_right (borrowing_padding_lt_twice q W k hq hW) hinner
  simpa [Nat.mul_assoc] using this

theorem padded_scan_bound (original padded block : ℝ) (hblock : 0 < block)
    (hvolume : padded ≤ 2*original) :
    1 + padded/block ≤ 2*(1+original/block) := by
  have := div_le_div_of_nonneg_right hvolume (le_of_lt hblock)
  rw [mul_div_assoc] at this
  linarith

inductive Instruction where
  | moveDigit
  | pad
  | recursiveCall (depth : ℕ)
  | baseCall (width : ℕ)
  | removePadding
  deriving DecidableEq

/-- Move both high fields to the prefix, pad, execute the radix list and
remainder, discard padding, and restore both high fields. -/
def borrowedPlan (m t₀ k ρ e : ℕ) : List Instruction :=
  List.replicate (2*ρ) .moveDigit ++ [.pad] ++
    (scales m k ((e-ρ)/t₀)).map Instruction.recursiveCall ++
    [.baseCall ((e-ρ)%t₀), .removePadding] ++
    List.replicate (2*ρ) .moveDigit

def basePlan (t₀ e : ℕ) : List Instruction :=
  List.replicate (e/t₀) (.baseCall t₀) ++ [.baseCall (e%t₀)]

def plan (m t₀ q W e : ℕ) : List Instruction :=
  let k := depth m t₀ e
  let ρ := borrowedWidth q W k
  if ρ < e then borrowedPlan m t₀ k ρ e else basePlan t₀ e

theorem plan_recursive_depth (m t₀ q W e j : ℕ)
    (hj : Instruction.recursiveCall j ∈ plan m t₀ q W e) :
    j ≤ depth m t₀ e := by
  try dsimp only [plan] at hj
  split_ifs at hj with h
  · have hmem : j ∈ scales m (depth m t₀ e)
        ((e-borrowedWidth q W (depth m t₀ e))/t₀) := by
      simpa [borrowedPlan] using hj
    exact scales_depth _ _ _ _ hmem
  · simp [basePlan] at hj

theorem plan_base_width (m t₀ q W e w : ℕ) (ht : 0<t₀)
    (hw : Instruction.baseCall w ∈ plan m t₀ q W e) : w ≤ t₀ := by
  try dsimp only [plan] at hw
  split_ifs at hw with h
  · have heq : (e-borrowedWidth q W (depth m t₀ e))%t₀ = w := by
      simpa [borrowedPlan, eq_comm] using hw
    rw [← heq]
    exact le_of_lt (Nat.mod_lt _ ht)
  · have hcases : (e/t₀ ≠ 0 ∧ t₀=w) ∨ e%t₀=w := by
      simpa [basePlan, eq_comm] using hw
    rcases hcases with ⟨_,rfl⟩ | rfl
    · rfl
    · exact le_of_lt (Nat.mod_lt _ ht)

theorem plan_calls_fit_padding (m t₀ q W e j : ℕ) (hW : 0<W)
    (hj : Instruction.recursiveCall j ∈ plan m t₀ q W e) :
    W^j ∣ paddedCount (q^(2*borrowedWidth q W (depth m t₀ e)))
      (W^(depth m t₀ e+1)) :=
  all_depths_divide_padding q W _ j hW (plan_recursive_depth m t₀ q W e j hj)

def traceCost (charge : Instruction → ℝ) (trace : List Instruction) : ℝ :=
  (trace.map charge).sum

theorem traceCost_append (charge : Instruction → ℝ) (xs ys : List Instruction) :
    traceCost charge (xs++ys) = traceCost charge xs + traceCost charge ys := by
  simp [traceCost]

theorem traceCost_mono (f g : Instruction → ℝ) (xs : List Instruction)
    (h : ∀ i ∈ xs, f i ≤ g i) : traceCost f xs ≤ traceCost g xs := by
  unfold traceCost
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- A local envelope: scan operations get one scan unit, and a scale-j
recursive call gets its established `A*b^j` bound. -/
def envelope (scan A b : ℝ) : Instruction → ℝ
  | .recursiveCall j => scan*A*b^j
  | .baseCall _ => scan*A
  | _ => scan

theorem borrowedPlan_cost (m t₀ k ρ e : ℕ) (scan A b : ℝ) :
    traceCost (envelope scan A b) (borrowedPlan m t₀ k ρ e) =
      scan*(4*ρ+2) + scan*A*(scaleWeight b (scales m k ((e-ρ)/t₀))+1) := by
  simp only [borrowedPlan, traceCost, List.map_append, List.sum_append,
    List.map_replicate, List.sum_replicate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, envelope, nsmul_eq_mul, List.map_map]
  have hs : ((scales m k ((e-ρ)/t₀)).map (fun j => scan*A*b^j)).sum =
      scan*A*scaleWeight b (scales m k ((e-ρ)/t₀)) := by
    unfold scaleWeight
    rw [List.sum_map_mul_left]
  change _ + _ + ((scales m k ((e-ρ)/t₀)).map (fun j => scan*A*b^j)).sum + _ + _ = _
  rw [hs]
  push_cast
  ring

theorem basePlan_cost (t₀ e : ℕ) (scan A b : ℝ) :
    traceCost (envelope scan A b) (basePlan t₀ e) =
      scan*A*((e/t₀ : ℕ)+1) := by
  simp [basePlan, traceCost, envelope, nsmul_eq_mul]
  ring

def scheduleConstant (m q W : ℕ) (A : ℝ) : ℝ :=
  4*borrowConstant q W+2 + A*(m+borrowConstant q W+1)

/-- The bound is obtained by summing the emitted calls. In particular the
case where there are too few digits to borrow is handled by its actual
base-call list; no global arbitrary-width cost premise occurs here. -/
theorem plan_envelope_bound (m t₀ q W e : ℕ) (hm : 1 < m) (ht : 0 < t₀)
    (scan A b : ℝ) (hscan : 0 ≤ scan) (hA : 0 ≤ A) (hb : 1 ≤ b) :
    traceCost (envelope scan A b) (plan m t₀ q W e) ≤
      scan * scheduleConstant m q W A * geometric b (depth m t₀ e) := by
  let k := depth m t₀ e
  let c := borrowConstant q W
  let ρ := borrowedWidth q W k
  have hg := geometric_nonneg b (by linarith) k
  have hk := depth_le_geometric b hb k
  have h1 : (1:ℝ) ≤ geometric b k := by
    have : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (by omega : 1 ≤ k+1)
    linarith
  have hρ : (ρ:ℝ) ≤ c * geometric b k := by
    have hc : (0:ℝ) ≤ c := by positivity
    have hmul := mul_le_mul_of_nonneg_left hk hc
    simpa [ρ, borrowedWidth, c] using hmul
  have hcm : (0:ℝ) ≤ m+c+1 := by positivity
  unfold plan
  change traceCost _ (if ρ < e then borrowedPlan m t₀ k ρ e else basePlan t₀ e) ≤ _
  split_ifs with hborrow
  · rw [borrowedPlan_cost]
    have hn : (e-ρ)/t₀ < m^(k+1) :=
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le e ρ)) (quotient_depth_bound m t₀ e hm)
    have hs := scaleWeight_bound m k ((e-ρ)/t₀) hm hn b (by linarith)
    have hmcast : ((m-1:ℕ):ℝ) = m-1 := by push_cast [Nat.cast_sub (by omega : 1≤m)]; rfl
    rw [hmcast] at hs
    have hc0 : (0:ℝ) ≤ c := by positivity
    have hcost := mul_le_mul_of_nonneg_left (show
        4*(ρ:ℝ)+2 + A*(scaleWeight b (scales m k ((e-ρ)/t₀))+1) ≤
          (4*c+2+A*(m+c+1))*geometric b k by nlinarith) hscan
    try dsimp [scheduleConstant]
    try dsimp [k,c] at hcost
    nlinarith
  · rw [basePlan_cost]
    have he : e ≤ ρ := by omega
    have hn : e/t₀ ≤ ρ := (Nat.div_le_self _ _).trans he
    have hnR : ((e/t₀:ℕ):ℝ) ≤ ρ := by exact_mod_cast hn
    have hc0 : (0:ℝ) ≤ c := by positivity
    have hm0 : (0:ℝ) ≤ m := by positivity
    have hh : ((e/t₀:ℕ):ℝ)+1 ≤ (c+1)*geometric b k := by nlinarith
    have hc : A*(c+1) ≤ 4*c+2+A*(m+c+1) := by nlinarith
    have hh' : A*(((e/t₀:ℕ):ℝ)+1) ≤
        (4*c+2+A*(m+c+1))*geometric b k := by
      have hleft := mul_le_mul_of_nonneg_left hh hA
      have hright := mul_le_mul_of_nonneg_right hc hg
      nlinarith
    have hcost := mul_le_mul_of_nonneg_left hh' hscan
    try dsimp [scheduleConstant]
    try dsimp [k,c] at hcost
    nlinarith

theorem plan_cost_power_bound (m t₀ q W e : ℕ) (hm : 1 < m) (ht : 0 < t₀)
    (scan A b : ℝ) (hscan : 0 ≤ scan) (hA : 0 ≤ A) (hb : 1 < b)
    (charge : Instruction → ℝ)
    (hprimitive : ∀ op ∈ plan m t₀ q W e, charge op ≤ envelope scan A b op) :
    traceCost charge (plan m t₀ q W e) ≤
      scan * (scheduleConstant m q W A * (b/(b-1))) * b^(depth m t₀ e) := by
  have hC : 0 ≤ scheduleConstant m q W A := by unfold scheduleConstant; positivity
  have hfirst := (traceCost_mono charge _ _ hprimitive).trans
    (plan_envelope_bound m t₀ q W e hm ht scan A b hscan hA (le_of_lt hb))
  have hsecond := mul_le_mul_of_nonneg_left (geometric_power_bound b hb (depth m t₀ e))
    (mul_nonneg hscan hC)
  nlinarith

/-- Passing from the integer scale to the actual width ratio introduces no
logarithmic factor. The `1+` also covers a width below the base threshold. -/
theorem depth_power_width_bound (m t₀ e : ℕ) (ht : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ((m:ℝ)^τ) ^ depth m t₀ e ≤ 1 + ((e:ℝ)/t₀)^τ := by
  by_cases hn : e/t₀ = 0
  · simp only [depth, hn, Nat.log_zero_right, pow_zero]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  · have hpow := Nat.pow_log_le_self m hn
    have he : ((e/t₀:ℕ):ℝ) ≤ (e:ℝ)/t₀ := by
      apply (le_div_iff₀ (by exact_mod_cast ht : (0:ℝ)<t₀)).2
      exact_mod_cast Nat.div_mul_le_self e t₀
    have hpR : ((m:ℝ) ^ depth m t₀ e) ≤ (e:ℝ)/t₀ := by
      have hpn : ((m:ℝ) ^ depth m t₀ e) ≤ ((e/t₀:ℕ):ℝ) := by exact_mod_cast hpow
      exact hpn.trans he
    have hr := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(m:ℝ)^depth m t₀ e) hpR hτ
    rw [← Real.rpow_pow_comm (by positivity : (0:ℝ)≤(m:ℝ))] at hr
    linarith

/-- Appendix C's scan multiplier, derived from the generated schedule and
local per-operation bounds. `scan` may be taken as the padded volume scan;
`padded_scan_bound` transfers it to at most twice the original-volume scan. -/
theorem arbitrary_width_cost (m t₀ q W e : ℕ) (hm : 1 < m) (ht : 0 < t₀)
    (scan A τ : ℝ) (hscan : 0 ≤ scan) (hA : 0 ≤ A) (hτ : 0 < τ)
    (charge : Instruction → ℝ)
    (hprimitive : ∀ op ∈ plan m t₀ q W e,
      charge op ≤ envelope scan A ((m:ℝ)^τ) op) :
    traceCost charge (plan m t₀ q W e) ≤
      scan * (scheduleConstant m q W A *
        (((m:ℝ)^τ)/((m:ℝ)^τ-1))) * (1+((e:ℝ)/t₀)^τ) := by
  have hb : 1 < (m:ℝ)^τ := Real.one_lt_rpow (by exact_mod_cast hm) hτ
  have hC : 0 ≤ scheduleConstant m q W A := by unfold scheduleConstant; positivity
  have hfactor : 0 ≤ scan * (scheduleConstant m q W A *
      (((m:ℝ)^τ)/((m:ℝ)^τ-1))) := by
    apply mul_nonneg hscan
    apply mul_nonneg hC
    exact div_nonneg (by positivity) (by linarith)
  exact (plan_cost_power_bound m t₀ q W e hm ht scan A _ hscan hA hb charge hprimitive).trans
    (mul_le_mul_of_nonneg_left (depth_power_width_bound m t₀ e ht τ (le_of_lt hτ)) hfactor)

end CSL.ArbitrarySchedule
end ArbitrarySchedule


