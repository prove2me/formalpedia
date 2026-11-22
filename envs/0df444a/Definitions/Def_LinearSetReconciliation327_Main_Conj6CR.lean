-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Conj6CR
-- name    : LinearSetReconciliation327_Main_Conj6CR
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T15:31:04.374952+00:00
-- url     : https://prove2.me/theorems/00930cc7-86a2-498b-be88-f44986799034
-- title:
--   Theorem 6.5, conjunct 6: the composite toggle assembly, with the CR block discharged
-- statement:
--   **One import for Theorem 6.5's conjunct 6.**  This bundle contains, in a single module, everything the toggle conjunct needs besides Theorem 5.1's per-block export.
--
--   * First, Proposition 2.3's toggle block **relocated to a deterministic-table base**: `cr23UpStmtAt` is `progUp` with $r_1 := \delta$ and $r_0 \mathrel{+}= \delta$ before the prologue and $r_5 \mathrel{+}= \delta$ right after the record base has been read out of the table (which shifts the pointer registers $r_7,r_{10},r_{11}$ the body uses as table indices).  Its run contract `CrSemAtW` is the published `CrSemAt` with the *payload-word fit* $\beta + \mathrm{wordsOf}\ W\ M \le 2^W$ added --- without it the contract is false, because `iTbl` reduces a table entry modulo $2^W$ --- and with the block width pinned.  The theorem `cr23UpStmtAt_crSemAtW` proves it: the block toggles column $i$ of the CR sketch into the payload at $\beta$ in at most $65536\lg^2(N+2)$ steps and leaves the caller's memory outside the payload window untouched.
--
--   * Second, the **assembly** `conj6_assembly_CR`: from the single per-block hypothesis $\mathit{hUp} : \mathrm{UpChildSemC}\ \mathit{Sup}\ E\ T_u\ 2^{W_d}\ f\ H_s$ (Theorem 5.1's obligation, `Bw` pinned, payload-word fit present) the composite programme `progUpOfProB Sup cr23UpStmtAt` reaches, in $7 + (8\ell + \ell T_u) + 2 + 3 + 65536\lg^2(N+2)$ steps from the initial state, a state whose payload is $y + \mathrm{compH}(\ldots)(\mathrm{cr23Sketch}\ N\ t\ C)(\mathrm{Pi.single}\ i\ 1)$.  The CR premise `hCr` of the earlier assembly is **not a hypothesis any more**: it is discharged by the theorem above.  This module therefore leaves *only* Theorem 5.1's obligation as a per-block assumption.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §6.1, Theorem 6.5, conjunct 6; Proposition 2.3 for the CR block; Theorem 5.1 for the per-block contract that remains a hypothesis.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_CR23
import Definitions.Def_LinearSetReconciliation327_Main_Top65Up
/-!
# Theorem 6.5, conjunct 6: the composite toggle assembly, with the `CR` block discharged

This module is the single import a downstream proof of Theorem 6.5's conjunct 6 needs.  It is the
verbatim concatenation of two green bundles:

* `Def_..._CR23UpAtB` --- the published `CR23UpAt` (Proposition 2.3's toggle relocated to a `det`
  base, with the run contract `CrSemAtW`) minus the 39 word-RAM lemmas it re-declares from
  `DecoderLemmas`.  It proves `cr23UpStmtAt_crSemAtW`, so the `CR` block of the composite needs no
  hypothesis at all.
* `Def_..._Conj6AsmW` --- the conjunct-6 assembly at the repaired per-block contract
  `UpChildSemC` (`Bw` pinned, payload-word fit present), with `hCr` discharged from the theorem
  above.  Its headline is `conj6_assembly_CR`.

Consequently the only per-block assumption of `conj6_assembly_CR` is
`hUp : UpChildSemC Sup E Tu (2 ^ Wd) f Hs`, i.e. Theorem 5.1's obligation in the exact shape its
export has to supply.

Why one module instead of two: `CR23UpAtB` deliberately re-uses the declaration names of the
published `CR23UpAt` (it *is* that file minus 39 duplicate lemmas), so a downstream file that
imports both `Def_..._CR23UpAt` and this development would see clashing names.  Declaring the
relocated block exactly once, here, keeps the import surface of conjunct 6 to this one module; the
overlap with `CR23UpAt` itself is harmless and of the same kind as the overlap that already exists
between the published `CR23UpAt` and `DecoderLemmas`.

Nothing in either span is edited; each edit that `Conj6AsmW` makes to the published
`Conj6Asm` proof is marked `-- !contract` there.
-/

set_option autoImplicit false
set_option linter.all false

namespace LinearSetReconciliation327.Main

open Finset

@[simp] theorem execInstr_halt (E : RAMEnv) (s : RAMState) : execInstr .halt E s = s := rfl
@[simp] theorem execInstr_imm (E : RAMEnv) (s : RAMState) (d : Fin 16) (v : ℕ) :
    execInstr (.imm d v) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_add (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.add d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_sub (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.sub d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + 2 ^ E.W - (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ||| (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bxor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bxor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ^^^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_load (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.load d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((s.mem (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_store (E : RAMEnv) (s : RAMState) (a v : Fin 16) :
    execInstr (.store a v) E s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.regs a) (s.regs v) } := rfl
@[simp] theorem execInstr_qDet (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.qDet d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.det (s.regs a)) % 2 ^ E.W) } := rfl
/-- The machine does not move at a `halt`. -/
theorem step_halt (P : Program) (E : RAMEnv) (s : RAMState)
    (h : P[s.pc]? = some .halt) : step P E s = s := by
  rw [step_eq_execInstr P E s .halt h, execInstr_halt]
/-- Unfolding of `Halted`. -/
theorem halted_iff (P : Program) (s : RAMState) : Halted P s ↔ P[s.pc]? = some .halt := by
  unfold Halted
  cases h : P[s.pc]? with
  | none => simp
  | some i => cases i <;> simp
/-- Only `store` touches memory. -/
theorem execInstr_mem (i : Instr) (E : RAMEnv) (s : RAMState)
    (h : ∀ a v, i ≠ .store a v) : (execInstr i E s).mem = s.mem := by
  cases i <;> simp_all [execInstr]
/-- Which register an instruction overwrites, if any. -/
def Instr.dest? : Instr → Option (Fin 16)
  | .imm d _ => some d
  | .add d _ _ => some d
  | .sub d _ _ => some d
  | .mul d _ _ => some d
  | .div d _ _ => some d
  | .mod d _ _ => some d
  | .band d _ _ => some d
  | .bor d _ _ => some d
  | .bxor d _ _ => some d
  | .shl d _ _ => some d
  | .shr d _ _ => some d
  | .lt d _ _ => some d
  | .load d _ => some d
  | .store _ _ => none
  | .jz _ _ => none
  | .jmp _ => none
  | .qDet d _ => some d
  | .qPerm d _ _ => some d
  | .qPermInv d _ _ => some d
  | .qCoeff d _ _ => some d
  | .halt => none
/-- Only the destination register of an instruction changes. -/
theorem execInstr_regs (i : Instr) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (h : i.dest? ≠ some d) : (execInstr i E s).regs d = s.regs d := by
  cases i <;>
    simp only [execInstr, Instr.dest?] at h ⊢ <;>
    first
      | rfl
      | (rw [Function.update_of_ne (fun he => h (by rw [he]))])
/-- A block that never writes register `d` leaves register `d` alone. -/
theorem runBlock_regs_frame (code : List Instr) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (h : ∀ i ∈ code, i.dest? ≠ some d) : (runBlock code E s).regs d = s.regs d := by
  induction code generalizing s with
  | nil => rfl
  | cons i tl ih =>
      rw [runBlock_cons, ih (s := execInstr i E s) (fun j hj => h j (by
        simp only [List.mem_cons]; exact Or.inr hj))]
      exact execInstr_regs i E s d (h i (by simp))
/-- A block with no `store` leaves memory alone. -/
theorem runBlock_mem_frame (code : List Instr) (E : RAMEnv) (s : RAMState)
    (h : ∀ i ∈ code, ∀ a v, i ≠ .store a v) : (runBlock code E s).mem = s.mem := by
  induction code generalizing s with
  | nil => rfl
  | cons i tl ih =>
      rw [runBlock_cons, ih (s := execInstr i E s) (fun j hj => h j (by
        simp only [List.mem_cons]; exact Or.inr hj))]
      exact execInstr_mem i E s (h i (by simp))
/-- A `Sem` run that lands on a `halt` is a `HaltsWithin` run; the `halt` itself costs one more
step.  `Post` is the caller's reading of the final state. -/
theorem halts_of_run (P : Program) (E : RAMEnv) (a e : ℕ) (s : RAMState) (B : ℝ)
    (Q : ℕ → RAMState → Prop) (Post : RAMState → Prop)
    (hAt : P[e]? = some .halt) (h : Sem P E a e s Q)
    (hQ : ∀ t s', Q t s' → (t : ℝ) + 1 ≤ B ∧ Post s') :
    ∃ s' : RAMState, HaltsWithin P E B s s' ∧ Post s' := by
  obtain ⟨-, k, s', hstep, hpe, hQ'⟩ := h
  obtain ⟨hB, hPost⟩ := hQ k s' hQ'
  refine ⟨s', ⟨k + 1, ?_, ?_, ?_⟩, hPost⟩
  · push_cast at hB ⊢
    linarith
  · rw [show k + 1 = 1 + k from by omega, Function.iterate_add_apply, Function.iterate_one, hstep,
      step_halt P E s' (by rw [hpe]; exact hAt)]
  · rw [halted_iff, hpe]
    exact hAt
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
/-- Column `v` of the sketch is what an update XORs in. -/
theorem cr23Sketch_single (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (v : Fin N) :
    cr23Sketch N t C (Pi.single v 1) = fun p => cr23Matrix N t C p v := by
  funext p
  simp [cr23Sketch]
/-- `clog 2 m ≤ logb 2 m + 1` (copied from the old block, renamed). -/
theorem cr23_clog_le_logb_add_one (m : ℕ) (hm : 1 < m) :
    (Nat.clog 2 m : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hm)
  have hlt : (2 : ℕ) ^ (Nat.clog 2 m - 1) < m :=
    Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hm
  have hltR : (2 : ℝ) ^ ((Nat.clog 2 m - 1 : ℕ) : ℝ) < (m : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hlt
  have hlog : ((Nat.clog 2 m - 1 : ℕ) : ℝ) < Real.logb 2 (m : ℝ) :=
    (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) hmR).2 hltR
  have hc1 : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num : 1 < 2) hm
  have hsub : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
    rw [Nat.cast_sub hc1]
    norm_num
  linarith
/-- `1 ≤ lg(N+2)` for `N ≥ 1` (copied from the old block, renamed). -/
theorem cr23_one_le_lg (N : ℕ) (hN : 1 ≤ N) : (1 : ℝ) ≤ lg ((N : ℝ) + 2) := by
  show (1 : ℝ) ≤ Real.logb 2 ((N : ℝ) + 2)
  have hpos : (0 : ℝ) < (N : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos, Real.rpow_one]
  have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith
/-- `N ≤ 2^(log N)`. -/
theorem cr23_le_pow_lb (N : ℕ) : N ≤ 2 ^ cr23Lb N := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) (N + 1)
  simp only [cr23Lb]
  omega
/-- `lg` is `Real.logb 2`, definitionally; the bridge lets `linarith` see through the definition. -/
theorem cr23_lg_eq (x : ℝ) : lg x = Real.logb 2 x := rfl
/-- `log N ≤ lg(N+2) + 1`. -/
theorem cr23_lb_le (N : ℕ) (hN : 1 ≤ N) : (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := by
  have hmono : cr23Lb N ≤ Nat.clog 2 (N + 2) := by
    have h2 : Nat.clog 2 (N + 1) ≤ Nat.clog 2 (N + 2) := by
      rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
      exact le_trans (by omega : N + 1 ≤ N + 2)
        (Nat.le_pow_clog (by norm_num : 1 < 2) (N + 2))
    simpa only [cr23Lb] using h2
  have hcast : (cr23Lb N : ℝ) ≤ (Nat.clog 2 (N + 2) : ℝ) := by exact_mod_cast hmono
  have h := cr23_clog_le_logb_add_one (N + 2) (by omega : 1 < N + 2)
  push_cast at h
  rw [cr23_lg_eq]
  linarith
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
noncomputable section
theorem cr23Word_pos (N : ℕ) : 0 < cr23Word N := by simp only [cr23Word]; omega
/-- The number whose `b`-th bit (for `b < W`) is `f b`. -/
def ofBits (W : ℕ) (f : ℕ → Bool) : ℕ := ∑ b ∈ Finset.range W, if f b then 2 ^ b else 0
theorem geom_two (W : ℕ) : (∑ b ∈ Finset.range W, 2 ^ b) = 2 ^ W - 1 := by
  induction W with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
theorem ofBits_lt (W : ℕ) (f : ℕ → Bool) : ofBits W f < 2 ^ W := by
  have h : ofBits W f ≤ ∑ b ∈ Finset.range W, 2 ^ b := by
    refine Finset.sum_le_sum ?_
    intro b _
    split_ifs with hb
    · exact le_rfl
    · exact Nat.zero_le _
  rw [geom_two] at h
  have h2 : 0 < 2 ^ W := Nat.two_pow_pos W
  omega
theorem ofBits_succ (W : ℕ) (f : ℕ → Bool) :
    ofBits (W + 1) f = (if f 0 then 1 else 0) + 2 * ofBits W (fun b => f (b + 1)) := by
  rw [ofBits, ofBits, Finset.sum_range_succ']
  have h2 : (∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ (k + 1) else 0))
      = 2 * ∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ k else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    split_ifs with hk
    · rw [pow_succ]
      ring
    · rfl
  rw [h2]
  by_cases h : f 0 = true
  · simp [h, Nat.add_comm]
  · simp [h, Nat.add_comm]
theorem ofBits_testBit (W : ℕ) (f : ℕ → Bool) (b : ℕ) (hb : b < W) :
    (ofBits W f).testBit b = f b := by
  induction W generalizing b f with
  | zero => omega
  | succ n ih =>
      rw [ofBits_succ]
      cases b with
      | zero =>
          rw [Nat.testBit_zero, Nat.add_mul_mod_self_left]
          by_cases h : f 0 = true <;> simp [h]
      | succ b =>
          rw [Nat.testBit_succ]
          have hdiv : ((if f 0 then 1 else 0) + 2 * ofBits n (fun b => f (b + 1))) / 2
              = ofBits n (fun b => f (b + 1)) := by
            rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
            by_cases h : f 0 = true <;> simp [h]
          rw [hdiv]
          exact ih (fun b => f (b + 1)) b (by omega)
/-- `packMem` is the bit string of the rows `a·W + b < M` that are set. -/
theorem packMem_eq_ofBits (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a = ofBits W (fun b => decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1)) := by
  rw [packMem, ofBits]
  have hR : (∑ b ∈ Finset.range W,
        (if decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) then 2 ^ b else 0))
      = ∑ b ∈ (Finset.range W).filter
          (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1), 2 ^ b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b _
    by_cases h : ∃ p : Fin M, p.val = a * W + b ∧ y p = 1 <;> simp [h]
  rw [hR]
  have hL : (∑ p : Fin M, (if p.val / W = a ∧ y p = 1 then 2 ^ (p.val % W) else 0))
      = ∑ b ∈ (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
          (fun p => p.val % W), 2 ^ b := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
    · intro p hp p' hp' heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp hp'
      have heq' : p.val % W = p'.val % W := heq
      refine Fin.ext ?_
      rw [← Nat.div_add_mod p.val W, hp.1, ← Nat.div_add_mod p'.val W, hp'.1, heq']
  rw [hL]
  have himg : (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
        (fun p => p.val % W)
      = (Finset.range W).filter (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range, true_and,
      exists_prop]
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨Nat.mod_lt _ hW, p, ?_, hp2⟩
      rw [← hp1, Nat.mul_comm]
      exact (Nat.div_add_mod p.val W).symm
    · rintro ⟨hb, p, hp, hp2⟩
      refine ⟨p, ⟨?_, hp2⟩, ?_⟩
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [himg]
theorem testBit_packMem (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a b : ℕ)
    (hb : b < W) :
    (packMem W y a).testBit b = decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_testBit W _ b hb
theorem packMem_lt (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a < 2 ^ W := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_lt W _
/-- In `ZMod 2`, `a + b = 1` is the exclusive or of `a = 1` and `b = 1`. -/
theorem decide_zmod2_add (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
/-- The `b`-th bit of a sum of two payloads packed into the same word. -/
theorem decide_row_add {M : ℕ} (q : ℕ) (u z : Fin M → ZMod 2) :
    decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1)
      = (decide (∃ p : Fin M, p.val = q ∧ u p = 1)
          ^^ decide (∃ p : Fin M, p.val = q ∧ z p = 1)) := by
  have hrow : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) → ∀ p' : Fin M,
      p'.val = q → y p' = 1 := by
    intro y hy p' hp'
    obtain ⟨p, hp, hpy⟩ := hy
    have : p' = p := Fin.ext (by rw [hp', hp])
    rwa [this]
  by_cases hex : ∃ p : Fin M, p.val = q
  · obtain ⟨p₀, hp₀⟩ := hex
    have e : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) ↔ y p₀ = 1 := by
      intro y
      exact ⟨fun hy => hrow y hy p₀ hp₀, fun hy => ⟨p₀, hp₀, hy⟩⟩
    have e1 : decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1) = decide ((u + z) p₀ = 1) := by
      by_cases h : (u + z) p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e (u + z)).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e (u + z)).mp hc))]
    have e2 : decide (∃ p : Fin M, p.val = q ∧ u p = 1) = decide (u p₀ = 1) := by
      by_cases h : u p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e u).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e u).mp hc))]
    have e3 : decide (∃ p : Fin M, p.val = q ∧ z p = 1) = decide (z p₀ = 1) := by
      by_cases h : z p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e z).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e z).mp hc))]
    rw [e1, e2, e3]
    show decide (u p₀ + z p₀ = 1) = (decide (u p₀ = 1) ^^ decide (z p₀ = 1))
    exact decide_zmod2_add _ _
  · have h1 : ¬ ∃ p : Fin M, p.val = q ∧ (u + z) p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h2 : ¬ ∃ p : Fin M, p.val = q ∧ u p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h3 : ¬ ∃ p : Fin M, p.val = q ∧ z p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
    rfl
/-- **The packed payload is additive.** Toggling the bits of `z` in a stored payload `y` is the
XOR of the packed words. -/
theorem packMem_add (W : ℕ) (hW : 0 < W) {M : ℕ} (u z : Fin M → ZMod 2) (a : ℕ) :
    packMem W (u + z) a = packMem W u a ^^^ packMem W z a := by
  refine Nat.eq_of_testBit_eq ?_
  intro b
  by_cases hb : b < W
  · rw [testBit_packMem W hW _ a b hb, Nat.testBit_xor, testBit_packMem W hW _ a b hb,
      testBit_packMem W hW _ a b hb, decide_row_add]
  · have hbW : W ≤ b := by omega
    have h1 : packMem W (u + z) a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h2 : packMem W u a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h3 : packMem W z a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_xor, Nat.testBit_lt_two_pow h2,
      Nat.testBit_lt_two_pow h3]
    rfl
/-- The part of column `v` contributed by the seeds `0, …, j-1`. -/
def cr23Delta (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (j : ℕ) (v : Fin N) :
    Fin (cr23R N t) → ZMod 2 :=
  fun p => ∑ s ∈ Finset.range j, cr23Lvl N t C v s p
theorem cr23Lvl_apply (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ)
    (hs : s < cr23D N) (p : Fin (cr23R N t)) :
    cr23Lvl N t C v s p
      = if p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) then
          cr23Sketch N t C (Pi.single v 1) p else 0 := by
  simp only [cr23Lvl, dif_pos hs]
theorem cr23Lb_succ_pos (N : ℕ) : 0 < cr23Lb N + 1 := by omega
theorem cr23_one_le_lb (N : ℕ) (hN : 1 ≤ N) : 1 ≤ cr23Lb N :=
  Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < N + 1)
theorem cr23D_pos (N : ℕ) (hN : 1 ≤ N) : 0 < cr23D N := by
  have h := cr23_one_le_lb N hN
  simp only [cr23D]
  omega
/-- A row of the sketch forces `M > 0` (`R = 0` when `t = 0`). -/
theorem cr23M_pos (N t : ℕ) (p : Fin (cr23R N t)) : 0 < cr23M t := by
  rcases Nat.eq_zero_or_pos (cr23M t) with h | h
  · exfalso
    have h0 : cr23R N t = 0 := by simp [cr23R, h]
    have := p.isLt
    omega
  · exact h
/-- The check index of row `p` is below `D·M`. -/
theorem cr23_check_lt (N t : ℕ) (p : Fin (cr23R N t)) :
    p.val / (cr23Lb N + 1) < cr23D N * cr23M t := by
  rw [Nat.div_lt_iff_lt_mul (cr23Lb_succ_pos N)]
  simpa only [cr23R] using p.isLt
theorem cr23RowSeedComp_lt (N t : ℕ) (p : Fin (cr23R N t)) :
    p.val / (cr23Lb N + 1) / cr23M t < cr23D N :=
  (Nat.div_lt_iff_lt_mul (cr23M_pos N t p)).mpr (cr23_check_lt N t p)
theorem cr23RowBktComp_lt (N t : ℕ) (p : Fin (cr23R N t)) :
    p.val / (cr23Lb N + 1) % cr23M t < cr23M t :=
  Nat.mod_lt _ (cr23M_pos N t p)
/-- The seed of row `p`: the check of `p` is `(seed, bucket)`. -/
def cr23RowSeed (N t : ℕ) (p : Fin (cr23R N t)) : Fin (cr23D N) :=
  ⟨p.val / (cr23Lb N + 1) / cr23M t, cr23RowSeedComp_lt N t p⟩
/-- The bucket of row `p`. -/
def cr23RowBkt (N t : ℕ) (p : Fin (cr23R N t)) : Fin (cr23M t) :=
  ⟨p.val / (cr23Lb N + 1) % cr23M t, cr23RowBktComp_lt N t p⟩
/-- The label bit of row `p`. -/
def cr23RowBit (N t : ℕ) (p : Fin (cr23R N t)) : Fin (cr23Lb N + 1) :=
  ⟨p.val % (cr23Lb N + 1), Nat.mod_lt _ (cr23Lb_succ_pos N)⟩
/-- The value of the row-triple equivalence, in terms of the check index. -/
theorem cr23RowEquiv_val (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t))
    (k : Fin (cr23Lb N + 1)) :
    (cr23RowEquiv N t ((s, y), k)).val
      = k.val + (cr23Lb N + 1) * cr23Check N t s y := rfl
/-- Every row is the row of its own check, at its own label bit. -/
theorem cr23Row_mk (N t : ℕ) (p : Fin (cr23R N t)) :
    cr23RowEquiv N t ((cr23RowSeed N t p, cr23RowBkt N t p), cr23RowBit N t p) = p := by
  refine Fin.ext ?_
  have hsplit : p.val / (cr23Lb N + 1) % cr23M t
        + cr23M t * (p.val / (cr23Lb N + 1) / cr23M t) = p.val / (cr23Lb N + 1) := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod _ _
  simp only [cr23RowEquiv_val, cr23Check, cr23RowSeed, cr23RowBkt, cr23RowBit, Fin.val_mk]
  rw [hsplit, Nat.mod_add_div]
/-- The sketch value at a row is the entry of the row's own check, bucket and bit. -/
theorem cr23Sketch_entry (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N)
    (p : Fin (cr23R N t)) :
    cr23Sketch N t C (Pi.single v 1) p
      = cr23Entry N t C ((cr23RowSeed N t p, cr23RowBkt N t p), cr23RowBit N t p) v := by
  have hsymm : (cr23RowEquiv N t).symm p
      = ((cr23RowSeed N t p, cr23RowBkt N t p), cr23RowBit N t p) := by
    rw [Equiv.symm_apply_eq]
    exact (cr23Row_mk N t p).symm
  rw [cr23Sketch_single]
  show cr23Matrix N t C p v = _
  rw [show cr23Matrix N t C p v = cr23Entry N t C ((cr23RowEquiv N t).symm p) v from rfl, hsymm]
theorem cr23Lvl_word (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ)
    (hs : s < cr23D N) (p : Fin (cr23R N t)) (h : cr23Lvl N t C v s p = 1) :
    p.val / cr23Word N = cr23Addr N t C ⟨s, hs⟩ v := by
  have hn : 0 < cr23Lb N + 1 := cr23Lb_succ_pos N
  rw [cr23Lvl_apply N t C v s hs] at h
  by_cases hc : p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩)
  · have hp : p.val = p.val % (cr23Lb N + 1)
        + (cr23Lb N + 1) * cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) := by
      rw [← hc, Nat.mod_add_div]
    set cheq := cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) with hcheq
    have hk : p.val % (cr23Lb N + 1) < cr23Lb N + 1 := Nat.mod_lt _ hn
    have hr : cheq % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
    have hq : cheq = 1024 * (cheq / 1024) + cheq % 1024 := (Nat.div_add_mod cheq 1024).symm
    have hsmall : p.val % (cr23Lb N + 1) + (cr23Lb N + 1) * (cheq % 1024)
        < 1024 * (cr23Lb N + 1) := by
      have h1 : (cr23Lb N + 1) * (cheq % 1024) ≤ (cr23Lb N + 1) * 1023 :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 := Nat.add_lt_add_of_lt_of_le hk h1
      calc p.val % (cr23Lb N + 1) + (cr23Lb N + 1) * (cheq % 1024)
          < (cr23Lb N + 1) + (cr23Lb N + 1) * 1023 := h2
        _ = 1024 * (cr23Lb N + 1) := by ring
    have hsplit : p.val = (p.val % (cr23Lb N + 1) + (cr23Lb N + 1) * (cheq % 1024))
        + (1024 * (cr23Lb N + 1)) * (cheq / 1024) := by
      conv_lhs => rw [hp]
      conv_lhs => rw [hq]
      ring
    rw [cr23Addr, cr23Word, hsplit,
      Nat.add_mul_div_left _ _ (by positivity : 0 < 1024 * (cr23Lb N + 1)),
      Nat.div_eq_of_lt hsmall, Nat.zero_add]
  · rw [if_neg hc] at h
    exact absurd h (by norm_num)
theorem packMem_cr23Lvl (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ)
    (hs : s < cr23D N) (a : ℕ) :
    packMem (cr23Word N) (cr23Lvl N t C v s) a
      = if a = cr23Addr N t C ⟨s, hs⟩ v then cr23Mask N t C ⟨s, hs⟩ v else 0 := by
  have hW : 0 < cr23Word N := cr23Word_pos N
  by_cases ha : a = cr23Addr N t C ⟨s, hs⟩ v
  · rw [if_pos ha, ha]
    rfl
  · rw [if_neg ha, packMem]
    refine Finset.sum_eq_zero ?_
    intro p _
    by_cases hp : p.val / cr23Word N = a
    · have h0 : cr23Lvl N t C v s p ≠ 1 := by
        rintro h1
        exact ha (by rw [← hp]; exact cr23Lvl_word N t C v s hs p h1)
      rw [if_neg (by rintro ⟨-, hc⟩; exact h0 hc)]
    · rw [if_neg (by rintro ⟨hc, -⟩; exact hp hc)]
theorem cr23Mask_lt (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : Fin (cr23D N))
    (v : Fin N) : cr23Mask N t C s v < 2 ^ cr23Word N :=
  packMem_lt (cr23Word N) (cr23Word_pos N) _ _
theorem cr23Delta_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23Delta N t C 0 v = 0 := by
  funext p
  simp only [cr23Delta, Finset.range_zero, Finset.sum_empty, Pi.zero_apply]
theorem cr23Delta_succ (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (j : ℕ)
    (v : Fin N) :
    cr23Delta N t C (j + 1) v = cr23Delta N t C j v + cr23Lvl N t C v j := by
  funext p
  simp only [cr23Delta, Finset.sum_range_succ, Pi.add_apply]
/-- **The column of `v` is the sum of its seed parts.** -/
theorem cr23Delta_full (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23Delta N t C (cr23D N) v = cr23Sketch N t C (Pi.single v 1) := by
  funext p
  have hM : 0 < cr23M t := cr23M_pos N t p
  have hval := cr23Sketch_entry N t C v p
  have hcheq : p.val / (cr23Lb N + 1)
      = (cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val := by
    have key : p.val / (cr23Lb N + 1) % cr23M t
        + cr23M t * (p.val / (cr23Lb N + 1) / cr23M t) = p.val / (cr23Lb N + 1) := by
      rw [Nat.add_comm]
      exact Nat.div_add_mod _ _
    simp only [cr23RowSeed, cr23RowBkt]
    exact key.symm
  -- any seed whose check matches row `p` is `p`'s own seed, with `p`'s own bucket
  have hkey : ∀ (s : ℕ) (hs : s < cr23D N),
      p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) →
      s = (cr23RowSeed N t p).val ∧ C v ⟨s, hs⟩ = cr23RowBkt N t p := by
    intro s hs hc
    have h1 : (C v ⟨s, hs⟩).val + cr23M t * s
        = (cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val :=
      hc.symm.trans hcheq
    have e1 : ((C v ⟨s, hs⟩).val + cr23M t * s) % cr23M t = (C v ⟨s, hs⟩).val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (C v ⟨s, hs⟩).isLt]
    have e2 : ((cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val) % cr23M t
        = (cr23RowBkt N t p).val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (cr23RowBkt N t p).isLt]
    rw [h1] at e1
    rw [e2] at e1
    have hbkt : C v ⟨s, hs⟩ = cr23RowBkt N t p := Fin.ext e1.symm
    refine ⟨?_, hbkt⟩
    have e3 : ((C v ⟨s, hs⟩).val + cr23M t * s) / cr23M t = s := by
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (C v ⟨s, hs⟩).isLt, Nat.zero_add]
    have e4 : ((cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val) / cr23M t
        = (cr23RowSeed N t p).val := by
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (cr23RowBkt N t p).isLt, Nat.zero_add]
    rw [← h1] at e4
    rw [← e3]
    exact e4
  by_cases hcy : C v (cr23RowSeed N t p) = cr23RowBkt N t p
  · have hcond : p.val / (cr23Lb N + 1)
        = cr23Check N t (cr23RowSeed N t p) (C v (cr23RowSeed N t p)) := by
      rw [cr23Check, hcy]
      exact hcheq
    have hterm : cr23Lvl N t C v (cr23RowSeed N t p).val p
        = cr23Sketch N t C (Pi.single v 1) p := by
      rw [cr23Lvl_apply N t C v _ (cr23RowSeed N t p).isLt p, if_pos hcond]
    rw [cr23Delta,
      Finset.sum_eq_single (cr23RowSeed N t p).val, hterm]
    · intro s hsS hne
      have hsD : s < cr23D N := Finset.mem_range.mp hsS
      rw [cr23Lvl_apply N t C v s hsD p, if_neg]
      intro hc
      exact hne (hkey s hsD hc).1
    · intro hmem
      exact absurd (Finset.mem_range.mpr (cr23RowSeed N t p).isLt) hmem
  · have hzero : ∀ s ∈ Finset.range (cr23D N), cr23Lvl N t C v s p = 0 := by
      intro s hsS
      have hsD : s < cr23D N := Finset.mem_range.mp hsS
      rw [cr23Lvl_apply N t C v s hsD p, if_neg]
      intro hc
      obtain ⟨hse, hbk⟩ := hkey s hsD hc
      refine hcy ?_
      have hseed : (⟨s, hsD⟩ : Fin (cr23D N)) = cr23RowSeed N t p := Fin.ext hse
      rw [hseed] at hbk
      exact hbk
    rw [cr23Delta, Finset.sum_eq_zero hzero, hval]
    simp only [cr23Entry, Prod.fst, Prod.snd, if_neg hcy]
theorem cr23UpDet_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) :
    cr23UpDet N t C 0 = cr23D N := by
  rw [cr23UpDet, dif_pos rfl]
theorem cr23UpDet_base (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23UpDet N t C (1 + v.val) = upBase N v.val := by
  have h0 : ¬ (1 + v.val = 0) := by omega
  have hb : 1 + v.val ≤ N := by omega
  rw [cr23UpDet, dif_neg h0, dif_pos hb, show 1 + v.val - 1 = v.val from by omega]
/-- `(b + c·a) % c = b` for `b < c`. -/
theorem cr23_mod_mul_add (a b c : ℕ) (hb : b < c) : (b + c * a) % c = b := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
/-- `(b + c·a) / c = a` for `b < c`. -/
theorem cr23_div_mul_add (a b c : ℕ) (hc : 0 < c) (hb : b < c) : (b + c * a) / c = a := by
  rw [Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hb, Nat.zero_add]
theorem cr23UpDet_addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N)
    (s : Fin (cr23D N)) :
    cr23UpDet N t C (upBase N v.val + 2 * s.val) = cr23Addr N t C s v := by
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hD0 : 0 < cr23D N := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  set q := upBase N v.val + 2 * s.val with hqdef
  have hq : q = 1 + N + (2 * (cr23D N * v.val) + 2 * s.val) := by
    rw [hqdef]; simp only [upBase]; ring
  have h0 : ¬ (q = 0) := by omega
  have hb : ¬ q ≤ N := by omega
  have hpair : q < cr23PairEnd N := by
    have hv : v.val + 1 ≤ N := by omega
    have h1 : 2 * (cr23D N * v.val) + 2 * cr23D N = 2 * (cr23D N * (v.val + 1)) := by ring
    have h2 : 2 * (cr23D N * (v.val + 1)) ≤ 2 * (cr23D N * N) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)
    have hsum : 2 * (cr23D N * v.val) + 2 * s.val < 2 * (cr23D N * N) := by
      calc 2 * (cr23D N * v.val) + 2 * s.val < 2 * (cr23D N * v.val) + 2 * cr23D N := by omega
        _ = 2 * (cr23D N * (v.val + 1)) := h1
        _ ≤ 2 * (cr23D N * N) := h2
    simp only [cr23PairEnd]
    omega
  have hr : q - (1 + N) = 2 * (cr23D N * v.val) + 2 * s.val := by omega
  have hpar : (q - (1 + N)) % 2 = 0 := by rw [hr]; omega
  have hhalf : (q - (1 + N)) / 2 = s.val + cr23D N * v.val := by rw [hr]; omega
  have hval1 : (q - (1 + N)) / 2 % cr23D N = s.val := by
    rw [hhalf, cr23_mod_mul_add v.val s.val (cr23D N) s.isLt]
  have hval2 : (q - (1 + N)) / 2 / cr23D N % N = v.val := by
    rw [hhalf, cr23_div_mul_add v.val s.val (cr23D N) hD0 s.isLt, Nat.mod_eq_of_lt v.isLt]
  have hs1 : (⟨(q - (1 + N)) / 2 % cr23D N, Nat.mod_lt _ hD0⟩ : Fin (cr23D N)) = s :=
    Fin.ext hval1
  have hv1 : (⟨(q - (1 + N)) / 2 / cr23D N % N, Nat.mod_lt _ hN0⟩ : Fin N) = v :=
    Fin.ext hval2
  rw [cr23UpDet, dif_neg h0, dif_neg hb, dif_pos (show 0 < N ∧ 0 < cr23D N from ⟨hN0, hD0⟩),
    dif_pos hpair, if_pos hpar, hs1, hv1]
theorem cr23UpDet_mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N)
    (s : Fin (cr23D N)) :
    cr23UpDet N t C (upBase N v.val + 2 * s.val + 1) = cr23Mask N t C s v := by
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hD0 : 0 < cr23D N := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  set q := upBase N v.val + 2 * s.val + 1 with hqdef
  have hq : q = 1 + N + (2 * (cr23D N * v.val) + 2 * s.val) + 1 := by
    rw [hqdef]; simp only [upBase]; ring
  have h0 : ¬ (q = 0) := by omega
  have hb : ¬ q ≤ N := by omega
  have hpair : q < cr23PairEnd N := by
    have hv : v.val + 1 ≤ N := by omega
    have h1 : 2 * (cr23D N * v.val) + 2 * cr23D N = 2 * (cr23D N * (v.val + 1)) := by ring
    have h2 : 2 * (cr23D N * (v.val + 1)) ≤ 2 * (cr23D N * N) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)
    have hsum : 2 * (cr23D N * v.val) + 2 * s.val + 1 < 2 * (cr23D N * N) := by
      calc 2 * (cr23D N * v.val) + 2 * s.val + 1
          < 2 * (cr23D N * v.val) + 2 * cr23D N := by omega
        _ = 2 * (cr23D N * (v.val + 1)) := h1
        _ ≤ 2 * (cr23D N * N) := h2
    simp only [cr23PairEnd]
    omega
  have hr : q - (1 + N) = 2 * (cr23D N * v.val) + 2 * s.val + 1 := by omega
  have hpar : ¬ (q - (1 + N)) % 2 = 0 := by rw [hr]; omega
  have hhalf : (q - (1 + N)) / 2 = s.val + cr23D N * v.val := by rw [hr]; omega
  have hval1 : (q - (1 + N)) / 2 % cr23D N = s.val := by
    rw [hhalf, cr23_mod_mul_add v.val s.val (cr23D N) s.isLt]
  have hval2 : (q - (1 + N)) / 2 / cr23D N % N = v.val := by
    rw [hhalf, cr23_div_mul_add v.val s.val (cr23D N) hD0 s.isLt, Nat.mod_eq_of_lt v.isLt]
  have hs1 : (⟨(q - (1 + N)) / 2 % cr23D N, Nat.mod_lt _ hD0⟩ : Fin (cr23D N)) = s :=
    Fin.ext hval1
  have hv1 : (⟨(q - (1 + N)) / 2 / cr23D N % N, Nat.mod_lt _ hN0⟩ : Fin N) = v :=
    Fin.ext hval2
  rw [cr23UpDet, dif_neg h0, dif_neg hb, dif_pos (show 0 < N ∧ 0 < cr23D N from ⟨hN0, hD0⟩),
    dif_pos hpair, if_neg hpar, hs1, hv1]
theorem cr23_pow_lt_word (N : ℕ) (hN : 1 ≤ N) :
    2 ^ (2 * cr23Lb N + 20) < 2 ^ cr23Word N := by
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
  have h := cr23_one_le_lb N hN
  simp only [cr23Word]
  omega
theorem cr23_lt_word (N : ℕ) (hN : 1 ≤ N) {j : ℕ} (hj : j ≤ 2 ^ (2 * cr23Lb N + 20)) :
    j < 2 ^ cr23Word N := lt_of_le_of_lt hj (cr23_pow_lt_word N hN)
theorem cr23D_lt_word (N : ℕ) (hN : 1 ≤ N) : cr23D N < 2 ^ cr23Word N := by
  apply cr23_lt_word N hN
  calc cr23D N = 2 ^ 10 * cr23Lb N := by
        show 1024 * cr23Lb N = 2 ^ 10 * cr23Lb N
        norm_num
    _ ≤ 2 ^ 10 * 2 ^ cr23Lb N := Nat.mul_le_mul_left _ (le_of_lt Nat.lt_two_pow_self)
    _ = 2 ^ (cr23Lb N + 10) := by
        rw [← pow_add]
        congr 1
        omega
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := by
        apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
        omega
theorem cr23_succ_lt_word (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : v.val + 1 < 2 ^ cr23Word N := by
  apply cr23_lt_word N hN
  calc v.val + 1 ≤ N := by omega
    _ ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := by
        apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
        omega
theorem cr23_one_lt_word (N : ℕ) (hN : 1 ≤ N) : 1 < 2 ^ cr23Word N := by
  have h := cr23D_lt_word N hN
  have h1 : 0 < cr23D N := cr23D_pos N hN
  omega
theorem cr23_two_lt_word (N : ℕ) (hN : 1 ≤ N) : 2 < 2 ^ cr23Word N := by
  have h1 : 2 ≤ 2 ^ (2 * cr23Lb N + 20) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  exact lt_of_le_of_lt h1 (cr23_pow_lt_word N hN)
theorem upBase_le_general (N : ℕ) (hN : 1 ≤ N) (u : ℕ) (hu : u ≤ 2 ^ cr23Lb N) :
    1 + N + 2 * (cr23D N * u) ≤ 2 ^ (2 * cr23Lb N + 13) := by
  have hLle : cr23Lb N ≤ 2 ^ cr23Lb N := le_of_lt Nat.lt_two_pow_self
  have hone : (1 : ℕ) ≤ 2 ^ cr23Lb N := Nat.one_le_two_pow
  have h1 : 1 + N ≤ 2 ^ (cr23Lb N + 1) := by
    calc 1 + N ≤ 2 ^ cr23Lb N + 2 ^ cr23Lb N := Nat.add_le_add hone (cr23_le_pow_lb N)
      _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ]; ring
  have h2 : 2 * (cr23D N * u) ≤ 2 ^ (2 * cr23Lb N + 11) := by
    calc 2 * (cr23D N * u) = 2048 * cr23Lb N * u := by
          show 2 * (1024 * cr23Lb N * u) = 2048 * cr23Lb N * u
          ring
      _ ≤ 2048 * cr23Lb N * 2 ^ cr23Lb N := Nat.mul_le_mul_left _ hu
      _ ≤ 2048 * 2 ^ cr23Lb N * 2 ^ cr23Lb N := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left 2048 hLle
      _ = 2 ^ (2 * cr23Lb N + 11) := by
          rw [show (2048 : ℕ) = 2 ^ 11 by norm_num, ← pow_add, ← pow_add]
          congr 1
          ring
  have h3 : 2 ^ (cr23Lb N + 1) ≤ 2 ^ (2 * cr23Lb N + 12) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have h4 : 2 ^ (2 * cr23Lb N + 11) ≤ 2 ^ (2 * cr23Lb N + 12) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have h5 : 2 ^ (2 * cr23Lb N + 12) + 2 ^ (2 * cr23Lb N + 12) = 2 ^ (2 * cr23Lb N + 13) := by
    rw [show 2 * cr23Lb N + 13 = (2 * cr23Lb N + 12) + 1 from by ring, pow_succ]
    ring
  calc 1 + N + 2 * (cr23D N * u)
      ≤ 2 ^ (cr23Lb N + 1) + 2 ^ (2 * cr23Lb N + 11) := Nat.add_le_add h1 h2
    _ ≤ 2 ^ (2 * cr23Lb N + 12) + 2 ^ (2 * cr23Lb N + 12) := Nat.add_le_add h3 h4
    _ = 2 ^ (2 * cr23Lb N + 13) := h5
theorem upBase_lt_general (N : ℕ) (hN : 1 ≤ N) (u : ℕ) (hu : u ≤ 2 ^ cr23Lb N) :
    1 + N + 2 * (cr23D N * u) < 2 ^ cr23Word N := by
  have h1 := upBase_le_general N hN u hu
  have h2 : 2 ^ (2 * cr23Lb N + 13) ≤ 2 ^ (2 * cr23Lb N + 20) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  exact lt_of_le_of_lt h1 (lt_of_le_of_lt h2 (cr23_pow_lt_word N hN))
theorem upBase_succ_lt_general (N : ℕ) (hN : 1 ≤ N) (u : ℕ)
    (hu : u ≤ 2 ^ cr23Lb N) : 2 + N + 2 * (cr23D N * u) < 2 ^ cr23Word N := by
  have h1 := upBase_le_general N hN u hu
  have h2 : 2 + N + 2 * (cr23D N * u) ≤ 2 * (1 + N + 2 * (cr23D N * u)) := by omega
  have h3 : 2 * 2 ^ (2 * cr23Lb N + 13) = 2 ^ (2 * cr23Lb N + 14) := by
    rw [show 2 * cr23Lb N + 14 = (2 * cr23Lb N + 13) + 1 from by ring, pow_succ]
    ring
  have h4 : 2 ^ (2 * cr23Lb N + 14) ≤ 2 ^ (2 * cr23Lb N + 20) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  calc 2 + N + 2 * (cr23D N * u) ≤ 2 * (1 + N + 2 * (cr23D N * u)) := h2
    _ ≤ 2 * 2 ^ (2 * cr23Lb N + 13) := Nat.mul_le_mul_left 2 h1
    _ = 2 ^ (2 * cr23Lb N + 14) := h3
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := h4
    _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
theorem upBase_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : upBase N v.val < 2 ^ cr23Word N :=
  upBase_lt_general N hN v.val (le_trans (le_of_lt v.isLt) (cr23_le_pow_lb N))
theorem upBase_add_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : upBase N v.val + cr23D N < 2 ^ cr23Word N := by
  have h := upBase_lt_general N hN (v.val + 1) (le_trans (by omega) (cr23_le_pow_lb N))
  have e1 : 2 * (cr23D N * (v.val + 1)) = 2 * (cr23D N * v.val) + 2 * cr23D N := by ring
  have e : upBase N v.val + cr23D N ≤ 1 + N + 2 * (cr23D N * (v.val + 1)) := by
    simp only [upBase]
    rw [e1]
    omega
  exact lt_of_le_of_lt e h
theorem upBase_end_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) :
    upBase N v.val + 2 * cr23D N < 2 ^ cr23Word N := by
  have e : upBase N v.val + 2 * cr23D N = 1 + N + 2 * (cr23D N * (v.val + 1)) := by
    simp only [upBase]; ring
  rw [e]
  exact upBase_lt_general N hN (v.val + 1) (le_trans (by omega) (cr23_le_pow_lb N))
theorem upBase_end_succ_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) :
    upBase N v.val + 1 + 2 * cr23D N < 2 ^ cr23Word N := by
  have h := upBase_succ_lt_general N hN (v.val + 1) (le_trans (by omega) (cr23_le_pow_lb N))
  have e : upBase N v.val + 1 + 2 * cr23D N = 2 + N + 2 * (cr23D N * (v.val + 1)) := by
    simp only [upBase]; ring
  rw [e]
  exact h
theorem cr23Check_lt (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t)) :
    cr23Check N t s y < cr23M t * cr23D N := by
  have h1 : cr23M t * s.val + y.val < cr23M t * s.val + cr23M t := Nat.add_lt_add_left y.isLt _
  have h2 : cr23M t * s.val + cr23M t = cr23M t * (s.val + 1) := by ring
  have h3 : cr23M t * (s.val + 1) ≤ cr23M t * cr23D N := Nat.mul_le_mul_left _ (by omega)
  calc cr23Check N t s y = y.val + cr23M t * s.val := rfl
    _ = cr23M t * s.val + y.val := by ring
    _ < cr23M t * s.val + cr23M t := h1
    _ = cr23M t * (s.val + 1) := h2
    _ ≤ cr23M t * cr23D N := h3
theorem progUp_at_pre : At progUp 0 progUpPre := by
  intro r hr
  have hr10 : r < 10 := by simpa [progUpPre] using hr
  interval_cases r <;>
    simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
      progUpBody]
theorem progUp_at_body : At progUp 11 progUpBody := by
  intro r hr
  have hr8 : r < 8 := by simpa [progUpBody] using hr
  interval_cases r <;>
    simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
      progUpBody]
theorem progUp_at_jmp : progUp[19]? = some (iJmp 10) := by
  simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
    progUpBody]
theorem progUp_at_halt : progUp[20]? = some iHalt := by
  simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
    progUpBody]
theorem progUp_at_loop :
    At progUp 10 (Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) 10) := by
  show At progUp 10 ([iJz r6 20] ++ progUpBody ++ [iJmp 10])
  intro r hr
  have hr10 : r < 10 := by simpa [progUpBody] using hr
  interval_cases r <;>
    simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
      progUpBody]
theorem Sem.loopCountUp (P : Program) (E : RAMEnv) (a : ℕ) (r : Fin 16) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop (Cond.neqz r) b) a)) (hW : 1 < 2 ^ E.W)
    (n : ℕ) (R : ℕ → RAMState → Prop) (C : ℕ)
    (hirr : ∀ (j : ℕ) (s s' : RAMState), s.regs = s'.regs → s.mem = s'.mem → R j s → R j s')
    (hstop : ∀ s, R 0 s → s.regs r = 0)
    (hgo : ∀ j s, R (j + 1) s → s.regs r ≠ 0)
    (hstep : ∀ j s, R (j + 1) s → Sem P E (a + 1) a { s with pc := a + 1 }
      (fun k s' => k ≤ C ∧ R j s' ∧ s'.pc = a)) :
    ∀ s, s.pc = a → R n s → Sem P E a (a + b.len + 2) s
      (fun k s' => k ≤ n * (1 + C) + 1 ∧ R 0 s' ∧ s'.pc = a + b.len + 2) := by
  obtain ⟨-, hjz, -, -⟩ := at_loop hAt
  intro s hpc hR
  induction n generalizing s with
  | zero =>
      have hstop' : ¬ (Cond.neqz r).eval s := by
        simp only [Cond.eval, ne_eq, not_not]
        exact hstop s hR
      refine Sem.mono (Sem.loopExit P E a (Cond.neqz r) b s hAt hW hpc hstop') ?_
      intro k s' h
      obtain ⟨hk, hs⟩ := h
      subst hk
      subst hs
      refine ⟨?_, ?_, rfl⟩
      · simp only [Cond.code, List.length_nil, Nat.zero_add, Nat.zero_mul]
        omega
      · simp only [Cond.code, runBlock_nil]
        exact hirr 0 s _ rfl rfl hR
  | succ n ih =>
      have hgo' : (Cond.neqz r).eval s := hgo n s hR
      have hjzn : Sem P E a (a + 1) s (fun k s' => k = 1 ∧ s' = { s with pc := a + 1 }) :=
        Sem.jz_next P E a (a + b.len + 2) (Cond.neqz r) s
          (by simpa [Cond.code, Cond.test] using hjz) hpc (by simpa [Cond.eval, Cond.test] using hgo')
      have h1 : Sem P E a a s (fun k s' => k ≤ 1 + C ∧ R n s' ∧ s'.pc = a) := by
        refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = 1 ∧ s' = { s with pc := a + 1 })
          (Q₂ := fun k₁ k₂ s' => k₁ = 1 ∧ (k₂ ≤ C ∧ R n s' ∧ s'.pc = a)) hjzn ?_) ?_
        · intro k₁ s₁ hQ₁
          obtain ⟨rfl, rfl⟩ := hQ₁
          exact Sem.mono (hstep n s hR) (fun k s' h => ⟨rfl, h⟩)
        · intro k s' h
          obtain ⟨k₁, k₂, rfl, hk₁, hk₂, hR', hpc'⟩ := h
          exact ⟨by omega, hR', hpc'⟩
      refine Sem.mono (Sem.seq (Q₁ := fun k s' => k ≤ 1 + C ∧ R n s' ∧ s'.pc = a)
        (Q₂ := fun k₁ k₂ s' => k₁ ≤ 1 + C ∧ (k₂ ≤ n * (1 + C) + 1 ∧ R 0 s' ∧
          s'.pc = a + b.len + 2)) h1 ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨hk₁, hR₁, hpc₁⟩ := hQ₁
        exact Sem.mono (ih s₁ hpc₁ hR₁) (fun k s' h => ⟨hk₁, h⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, rfl, hk₁, hk₂, hR0, hpc'⟩ := h
        have harith : (1 + C) + (n * (1 + C) + 1) = (n + 1) * (1 + C) + 1 := by ring
        exact ⟨by omega, hR0, hpc'⟩
/-- The first four body instructions (up to just before the store) as a chunk. -/
def upBodyA : List Instr := [iTbl r8 r7, iTbl r9 r10, iLd r4 r8, iBxor r4 r4 r9]
theorem upBody_split :
    progUpBody =
      (upBodyA ++ [iSt r8 r4] ++ [iAdd r7 r7 r12, iAdd r10 r10 r12, iSub r6 r6 r13]) := rfl
theorem upBodyA_mem (E : RAMEnv) (st : RAMState) :
    (runBlock upBodyA E st).mem = st.mem :=
  runBlock_mem_frame upBodyA E st
    (by
      intro i hi a v
      simp only [upBodyA, List.mem_cons, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | hi
      · simp
      · simp
      · simp
      · simp
      · simp at hi)
theorem upBodyA_r8 (E : RAMEnv) (st : RAMState) :
    (runBlock upBodyA E st).regs r8 = E.det (st.regs r7) % 2 ^ E.W := by
  simp only [upBodyA, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_load, execInstr_bxor,
    Function.update_of_ne, Function.update_self]
  rfl
theorem upBodyA_r4 (E : RAMEnv) (st : RAMState) :
    (runBlock upBodyA E st).regs r4
      = ((st.mem (E.det (st.regs r7) % 2 ^ E.W) % 2 ^ E.W ^^^ (E.det (st.regs r10) % 2 ^ E.W))
          % 2 ^ E.W) := by
  simp only [upBodyA, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_load, execInstr_bxor,
    Function.update_of_ne, Function.update_self]
  rfl
theorem upBodyA_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r8)
    (hd2 : d ≠ r4) (hd3 : d ≠ r9) :
    (runBlock upBodyA E st).regs d = st.regs d :=
  runBlock_regs_frame upBodyA E st d
    (by
      intro i hi
      simp only [upBodyA, List.mem_cons, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | hi
      · exact fun h => hd (by simpa [Instr.dest?] using h.symm)
      · exact fun h => hd3 (by simpa [Instr.dest?] using h.symm)
      · exact fun h => hd2 (by simpa [Instr.dest?] using h.symm)
      · exact fun h => hd2 (by simpa [Instr.dest?] using h.symm)
      · simp at hi)
theorem nat_lor_self (n : ℕ) : n ||| n = n := by simp
/-- The runtime bound `10·D + 11` of the update program is below `65536·lg²(N+2)`. -/
theorem upCost_le (N : ℕ) (hN : 1 ≤ N) :
    10 * (cr23D N : ℝ) + 12 ≤ 65536 * lg ((N : ℝ) + 2) ^ 2 := by
  have hD : (cr23D N : ℝ) = 1024 * (cr23Lb N : ℝ) := by
    simp only [cr23D]
    push_cast
    ring
  have hc : (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := cr23_lb_le N hN
  have hlg : (1 : ℝ) ≤ lg ((N : ℝ) + 2) := cr23_one_le_lg N hN
  have hsq : lg ((N : ℝ) + 2) ≤ lg ((N : ℝ) + 2) ^ 2 := by nlinarith only [hlg]
  rw [hD]
  nlinarith only [hc, hlg, hsq]
end
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
variable {N' t' : ℕ}
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
/-- **Below the graph block the two tables agree**: the decoder's own cells are strictly above. -/
theorem cr23DecDet_agrees (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) {a : ℕ}
    (ha : a < cr23DecBase N) : cr23DecDet N t C a = cr23UpDet N t C a := by
  simp only [cr23DecDet, if_pos ha]
theorem cr23DecBase_pos (N : ℕ) : 0 < cr23DecBase N := by
  simp only [cr23DecBase, cr23Graph0, cr23PairEnd]
  omega
/-- The record base of coordinate `v` lies below the decoder's own cells. -/
theorem cr23_succ_lt_decBase (N : ℕ) (v : Fin N) : 1 + v.val < cr23DecBase N := by
  simp only [cr23DecBase, cr23Graph0, cr23PairEnd]
  omega
/-- The last cell of the last record of coordinate `v` lies below the decoder's own cells. -/
theorem cr23_upBase_lt_decBase (N : ℕ) (v : Fin N) (s : Fin (cr23D N)) :
    upBase N v.val + 2 * s.val + 1 < cr23DecBase N := by
  have h1 : 2 * (cr23D N * v.val) + 2 * s.val + 1 < 2 * (cr23D N * N) := by
    have hs : 2 * s.val + 1 < 2 * cr23D N := by omega
    calc 2 * (cr23D N * v.val) + 2 * s.val + 1
        < 2 * (cr23D N * v.val) + 2 * cr23D N := by omega
      _ = 2 * (cr23D N * (v.val + 1)) := by ring
      _ ≤ 2 * (cr23D N * N) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega))
  simp only [cr23DecBase, cr23Graph0, cr23PairEnd, upBase]
  omega
theorem cr23DecDet_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N) :
    cr23DecDet N t C 0 = cr23D N := by
  rw [cr23DecDet_agrees N t C (cr23DecBase_pos N), cr23UpDet_zero]
theorem cr23DecDet_base (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (v : Fin N) : cr23DecDet N t C (1 + v.val) = upBase N v.val := by
  rw [cr23DecDet_agrees N t C (cr23_succ_lt_decBase N v), cr23UpDet_base]
theorem cr23DecDet_addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDet N t C (upBase N v.val + 2 * s.val) = cr23Addr N t C s v := by
  have h := cr23_upBase_lt_decBase N v s
  rw [cr23DecDet_agrees N t C (by omega), cr23UpDet_addr]
theorem cr23DecDet_mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDet N t C (upBase N v.val + 2 * s.val + 1) = cr23Mask N t C s v := by
  rw [cr23DecDet_agrees N t C (cr23_upBase_lt_decBase N v s), cr23UpDet_mask]
theorem decScanWordLt_aux {V L j : ℕ} (hL : 1 ≤ L) (hj : j < V) :
    j / 1024 < (V * L + 1024 * L - 1) / (1024 * L) := by
  have hLpos : 0 < 1024 * L := Nat.mul_pos (by norm_num) (by omega)
  have hV : j + 1024 ≤ V + 1023 := by omega
  have hX : j / 1024 * 1024 ≤ j := Nat.div_mul_le_self _ _
  have h2 : (j / 1024 + 1) * 1024 ≤ V + 1023 := by
    calc (j / 1024 + 1) * 1024 = j / 1024 * 1024 + 1024 := by ring
      _ ≤ j + 1024 := Nat.add_le_add_right hX 1024
      _ ≤ V + 1023 := hV
  have h6 : (V + 1023) * L = V * L + 1023 * L := by ring
  have h8 : 1024 * L = 1023 * L + L := by ring
  have h7 : 1023 * L ≤ 1024 * L - 1 := by rw [h8]; omega
  have hstep : (j / 1024 + 1) * (1024 * L) ≤ V * L + 1024 * L - 1 := by
    calc (j / 1024 + 1) * (1024 * L) = ((j / 1024 + 1) * 1024) * L := by ring
      _ ≤ (V + 1023) * L := Nat.mul_le_mul_right _ h2
      _ = V * L + 1023 * L := h6
      _ ≤ V * L + (1024 * L - 1) := Nat.add_le_add_left h7 _
      _ = V * L + 1024 * L - 1 := (Nat.add_sub_assoc hLpos (V * L)).symm
  have hq : j / 1024 + 1 ≤ (V * L + 1024 * L - 1) / (1024 * L) := by
    rw [Nat.le_div_iff_mul_le hLpos]
    exact hstep
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hq
/-- The payload word index `j / 1024` of a check is inside the packed payload. -/
theorem decScanWordLt (N t : ℕ) (hN : 1 ≤ N) {j : ℕ} (hj : j < cr23D N * cr23M t) :
    j / 1024 < wordsOf (cr23Word N) (cr23R N t) := by
  have h := decScanWordLt_aux (V := cr23D N * cr23M t) (L := cr23Lb N + 1) (by omega) hj
  rw [wordsOf, cr23Word, cr23R]
  exact h
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecXorPay
/-- **The payload word of a check lies inside the packed payload** — this is the bound the restricted
memory clause needs, and it is `decScanWordLt` (already proved for `j / 1024`) plus
`cr23Addr = cr23Check / 1024 < D·M`. -/
theorem addr_wordsOf (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (s : Fin (cr23D N)) (v : Fin N) :
    cr23Addr N t C s v < wordsOf (cr23Word N) (cr23R N t) := by
  have h := cr23Check_lt N t s (C v s)
  rw [Nat.mul_comm] at h
  exact decScanWordLt N t hN h
end DecXorPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option maxRecDepth 8000
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
/-- One past the record block is exactly `cr23Graph0 N`. -/
theorem cr23RecLo_top (N : ℕ) : cr23RecLo N + 2 * (cr23D N * N) = cr23Graph0 N := by
  simp only [cr23RecLo, cr23Graph0, cr23PairEnd]
/-- **Every address cell is a record cell** `upBase N v + 2·s`. -/
theorem cr23AddrSlot_upBase {N : ℕ} (v : Fin N) (s : Fin (cr23D N)) :
    cr23AddrSlot N (upBase N v.val + 2 * s.val) := by
  have hv : v.val + 1 ≤ N := by omega
  have h1 : 2 * (cr23D N * v.val) + 2 * cr23D N = 2 * (cr23D N * (v.val + 1)) := by ring
  have h2 : 2 * (cr23D N * (v.val + 1)) ≤ 2 * (cr23D N * N) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)
  refine ⟨?_, ?_, ?_⟩
  · simp only [cr23RecLo, upBase]; omega
  · rw [← cr23RecLo_top]
    simp only [upBase, cr23RecLo]
    omega
  · have e : upBase N v.val + 2 * s.val - cr23RecLo N
        = 2 * (cr23D N * v.val) + 2 * s.val := by
      simp only [cr23RecLo, upBase]; omega
    rw [e]; omega
/-- **The mask cell of a record is not an address cell.** -/
theorem cr23AddrSlot_mask_not {N : ℕ} (v : Fin N) (s : Fin (cr23D N)) :
    ¬ cr23AddrSlot N (upBase N v.val + 2 * s.val + 1) := by
  intro h
  obtain ⟨-, -, hpar⟩ := h
  have e : upBase N v.val + 2 * s.val + 1 - cr23RecLo N
      = 2 * (cr23D N * v.val) + 2 * s.val + 1 := by
    simp only [cr23RecLo, upBase]; omega
  rw [e] at hpar
  omega
theorem cr23AddrSlot_zero_not (N : ℕ) : ¬ cr23AddrSlot N 0 := by
  intro h; obtain ⟨h1, -⟩ := h; simp only [cr23RecLo] at h1; omega
theorem cr23AddrSlot_one_add_not {N : ℕ} (v : Fin N) : ¬ cr23AddrSlot N (1 + v.val) := by
  intro h; obtain ⟨h1, -⟩ := h; simp only [cr23RecLo] at h1; omega
/-- **Cells that are not address cells are untouched** — this is the whole content of the
classification: numbers and `det` indices do not move. -/
theorem cr23DecDetAt_agree (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β a : ℕ)
    (h : ¬ cr23AddrSlot N a) : cr23DecDetAt N t C β a = cr23DecDet N t C a := by
  simp only [cr23DecDetAt, if_neg h]
/-- `det 0 = D` — a **number**. -/
theorem cr23DecDetAt_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) : cr23DecDetAt N t C β 0 = cr23D N := by
  rw [cr23DecDetAt_agree N t C β 0 (cr23AddrSlot_zero_not N), cr23DecDet_zero N t C hN]
/-- `det (1+v) = upBase N v` — a **det index**: unchanged. -/
theorem cr23DecDetAt_base (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) (v : Fin N) : cr23DecDetAt N t C β (1 + v.val) = upBase N v.val := by
  rw [cr23DecDetAt_agree N t C β _ (cr23AddrSlot_one_add_not v), cr23DecDet_base N t C hN v]
/-- `det (upBase v + 2s) = cr23Addr` — a **memory address**: shifted by `β`. -/
theorem cr23DecDetAt_addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDetAt N t C β (upBase N v.val + 2 * s.val) = β + cr23Addr N t C s v := by
  rw [cr23DecDetAt, if_pos (cr23AddrSlot_upBase v s), cr23DecDet_addr N t C hN v s]
/-- `det (upBase v + 2s + 1) = cr23Mask` — a **number**: unchanged. -/
theorem cr23DecDetAt_mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDetAt N t C β (upBase N v.val + 2 * s.val + 1) = cr23Mask N t C s v := by
  rw [cr23DecDetAt_agree N t C β _ (cr23AddrSlot_mask_not v s), cr23DecDet_mask N t C hN v s]
/-- Word `a` of the payload, read from base `β`, is word `a` of `y`. -/
theorem payMem_at {W M β : ℕ} (y : Fin M → ZMod 2) {a : ℕ} (ha : a < wordsOf W M) :
    payMem W β y (β + a) = packMem W y a := by
  rw [payMem, if_pos ⟨Nat.le_add_right _ _, by rwa [Nat.add_sub_cancel_left]⟩,
    Nat.add_sub_cancel_left]
/-- **`UpData` with the payload moved to base `β`.**  The nine register clauses are *identical* to
`UpData`'s — that is the content of the classification: no register of `progUp` holds a payload
address across a step.  The only register that ever does, `r8`, is written by `qDet` and consumed by
the following `load`/`store` inside `progUpBody` (`§R.4.1`). -/
def UpDataAt (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ) (s : RAMState) : Prop :=
  s.regs r0 = v.val ∧ s.regs r3 = cr23D N ∧ s.regs r5 = upBase N v.val ∧ s.regs r6 = m ∧
    s.regs r7 = upBase N v.val + 2 * (cr23D N - m) ∧
    s.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - m) ∧
    s.regs r11 = upBase N v.val + 2 * cr23D N ∧ s.regs r12 = 2 ∧ s.regs r13 = 1 ∧
    (∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
      s.mem (β + addr) = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - m) v) addr) ∧
    (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
      s.mem c = payMem (cr23Word N) β y c)
theorem UpDataAt.irrel (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ)
    (s s' : RAMState) (hr : s.regs = s'.regs) (hm : s.mem = s'.mem)
    (h : UpDataAt N t C β y v m s) : UpDataAt N t C β y v m s' := by
  rcases h with ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hmem, hfr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact h0
  · rw [← hr]; exact h3
  · rw [← hr]; exact h5
  · rw [← hr]; exact h6
  · rw [← hr]; exact h7
  · rw [← hr]; exact h10
  · rw [← hr]; exact h11
  · rw [← hr]; exact h12
  · rw [← hr]; exact h13
  · intro addr ha; rw [← hm]; exact hmem addr ha
  · intro c hc; rw [← hm]; exact hfr c hc
/-! # D.  The relocated toggle block: `det` base `δ`

`progUp` (Proposition 2.3's toggle) reads its table at *absolute* indices: `iTbl d a` is
`d := E.det (r a)`.  The composite of Theorem 6.5 places the `CR` block's table at `det` offset
`δ = (l+1)·2^Wd`, so the block has to relocate itself:

* `r1 := δ` and `r0 += δ` before `progUpPre` (the prologue reads `det r1` and `det (r0+1)`);
* `r5 += δ` immediately after `r5` has been read out of the table (`r7`, `r10`, `r11` are computed
  from `r5` and are themselves table indices, so shifting `r5` once shifts all of them).

The resulting statement is `CrSemAt`: `Bw` pinned, the table pinned to 2.3's `cr23DecDetAt`, the
`det` base read from `r14`, a two-sided frame against the *caller's* memory and no register clauses.
This section proves it as the `δ`-generalisation of the `β`-rebased development of §A–§C above.
-/

/-- The two-instruction relocation preamble: `r1 := δ`, `r0 := v + δ`. -/
def cr23UpReloc : List Instr := [iBor r1 r14 r14, iAdd r0 r0 r14]

/-- `progUpPre` relocated: the preamble, then the published prologue with `r5 += δ` inserted
immediately after the table read of `r5`. -/
def cr23UpPreAt : List Instr :=
  [iBor r1 r14 r14, iAdd r0 r0 r14, iImm r13 1, iImm r12 2, iTbl r3 r1, iAdd r4 r0 r13,
   iTbl r5 r4, iAdd r5 r5 r14, iBor r7 r5 r5, iAdd r10 r5 r13, iAdd r11 r5 r3,
   iAdd r11 r11 r3, iBor r6 r3 r3]

@[simp] theorem cr23UpReloc_length : cr23UpReloc.length = 2 := rfl

@[simp] theorem cr23UpPreAt_length : cr23UpPreAt.length = 13 := rfl

/-- The relocated update block: the relocated prologue, then 2.3's countdown loop verbatim. -/
def cr23UpStmtAt : Stmt :=
  Stmt.seq (Stmt.code cr23UpPreAt) (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody))

@[simp] theorem cr23UpStmtAt_len : cr23UpStmtAt.len = 23 := rfl

/-- The compiled block at an arbitrary base: the loop sits at block offset `13` and exits at `23`. -/
theorem cr23UpStmtAt_compile_eq (base : ℕ) :
    cr23UpStmtAt.compile base
      = cr23UpPreAt ++
        Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) (base + 13) := rfl

/-- The compiled block at base `0`, spelled out. -/
theorem cr23UpStmtAt_compile_zero :
    cr23UpStmtAt.compile 0
      = cr23UpPreAt ++ [iJz r6 23] ++ progUpBody ++ [iJmp 13] := rfl

/-- The head piece of an `At` decomposition. -/
theorem At.take {P : Program} {a : ℕ} {A B : List Instr} (h : At P a (A ++ B)) : At P a A := by
  intro r hr
  have h' := h r (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left hr] at h'

/-- The tail piece of an `At` decomposition. -/
theorem At.drop {P : Program} {a : ℕ} {A B : List Instr} (h : At P a (A ++ B)) :
    At P (a + A.length) B := by
  intro r hr
  have h' := h (A.length + r) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega : A.length ≤ A.length + r)] at h'
  rw [show A.length + r - A.length = r from by omega] at h'
  rwa [show a + (A.length + r) = a + A.length + r from by omega] at h'

/-! ## D.1  The record indices of a body read stay below the graph block -/

/-- The record base plus two words per remaining seed is below the graph block, as soon as one
seed has been consumed.  (At `m = 0` it can equal the graph block, but no read happens there.) -/
theorem upBase_add_two_lt_graph0 (N : ℕ) (hN : 1 ≤ N) (v : Fin N) {m : ℕ} (hm : 1 ≤ m) :
    upBase N v.val + 2 * (cr23D N - m) < cr23Graph0 N := by
  have hD : 1 ≤ cr23D N := cr23D_pos N hN
  have hbase2D : upBase N v.val + 2 * cr23D N ≤ cr23Graph0 N := by
    have hv : v.val + 1 ≤ N := by omega
    have e : upBase N v.val + 2 * cr23D N = 1 + N + 2 * (cr23D N * (v.val + 1)) := by
      simp only [upBase]
      ring
    rw [e, cr23Graph0, cr23PairEnd]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)) (1 + N)
  have h2 : upBase N v.val + 2 * (cr23D N - 1) < cr23Graph0 N := by
    have e : upBase N v.val + 2 * (cr23D N - 1) = upBase N v.val + 2 * cr23D N - 2 := by omega
    omega
  have h1 : 2 * (cr23D N - m) ≤ 2 * (cr23D N - 1) := Nat.mul_le_mul_left 2 (by omega)
  omega

/-- The mask record of a body read stays below the graph block. -/
theorem upBase_add_two_succ_lt_graph0 (N : ℕ) (hN : 1 ≤ N) (v : Fin N) {m : ℕ} (hm : 1 ≤ m) :
    upBase N v.val + 1 + 2 * (cr23D N - m) < cr23Graph0 N := by
  have hD : 1 ≤ cr23D N := cr23D_pos N hN
  have hbase2D : upBase N v.val + 2 * cr23D N ≤ cr23Graph0 N := by
    have hv : v.val + 1 ≤ N := by omega
    have e : upBase N v.val + 2 * cr23D N = 1 + N + 2 * (cr23D N * (v.val + 1)) := by
      simp only [upBase]
      ring
    rw [e, cr23Graph0, cr23PairEnd]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)) (1 + N)
  have h2 : upBase N v.val + 1 + 2 * (cr23D N - 1) < cr23Graph0 N := by
    have e : upBase N v.val + 1 + 2 * (cr23D N - 1) = upBase N v.val + 2 * cr23D N - 1 := by
      omega
    omega
  have h1 : 2 * (cr23D N - m) ≤ 2 * (cr23D N - 1) := Nat.mul_le_mul_left 2 (by omega)
  omega

/-- The record base of coordinate `v` is below the graph block. -/
theorem upBase_lt_graph0 (N : ℕ) (hN : 1 ≤ N) (v : Fin N) :
    upBase N v.val < cr23Graph0 N := by
  have hv : v.val + 1 ≤ N := by omega
  have e : upBase N v.val = 1 + N + 2 * (cr23D N * v.val) := rfl
  rw [e, cr23Graph0, cr23PairEnd]
  have hD : 0 < cr23D N := cr23D_pos N hN
  have h2 : 2 * (cr23D N * v.val) < 2 * (cr23D N * N) := by
    have hv' : v.val < N := v.isLt
    exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hv' hD) (by norm_num)
  omega

/-- The two-cell record `1 + v` is below the graph block. -/
theorem succ_lt_graph0 (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : v.val + 1 < cr23Graph0 N := by
  have := upBase_lt_graph0 N hN v
  simp only [upBase] at this
  omega

/-- `0 < cr23Graph0 N`. -/
theorem graph0_pos (N : ℕ) (hN : 1 ≤ N) : 0 < cr23Graph0 N := by
  have := upBase_lt_graph0 N hN ⟨0, hN⟩
  omega

/-- The record base plus one is below the graph block. -/
theorem upBase_succ_lt_graph0 (N : ℕ) (hN : 1 ≤ N) (v : Fin N) :
    upBase N v.val + 1 < cr23Graph0 N := by
  have hD : 1 ≤ cr23D N := cr23D_pos N hN
  have hv : v.val + 1 ≤ N := by omega
  have hle : cr23D N * v.val + cr23D N ≤ cr23D N * N := by
    have h := Nat.mul_le_mul_left (cr23D N) hv
    rwa [Nat.mul_add, Nat.mul_one] at h
  have e : upBase N v.val + 1 = 2 + N + 2 * (cr23D N * v.val) := by
    simp only [upBase]; ring
  rw [e, cr23Graph0, cr23PairEnd]
  omega

/-! ## D.2  The invariant -/

/-- **`UpDataAtD`**: the loop invariant of the relocated block, with the `det` base `δ` added to
`r7`/`r10` (the two table indices the body reads) and the frame stated against the caller's own
memory `m₀`.  The clauses for `r7`/`r10` are guarded by `1 ≤ m` because at `m = 0` the last
pointer bump may wrap modulo `2^W` (when `δ + cr23Graph0 N = 2^W`); no read happens there, and the
final theorem only consumes the payload and frame clauses. -/
def UpDataAtD (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ) (m₀ : ℕ → ℕ) (s : RAMState) : Prop :=
  s.regs r6 = m ∧ s.regs r12 = 2 ∧ s.regs r13 = 1 ∧
    (1 ≤ m → s.regs r7 = δ + upBase N v.val + 2 * (cr23D N - m)) ∧
    (1 ≤ m → s.regs r10 = δ + upBase N v.val + 1 + 2 * (cr23D N - m)) ∧
    (∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
      s.mem (β + addr) = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - m) v) addr) ∧
    (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) → s.mem c = m₀ c)

theorem UpDataAtD.irrel (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ) (m₀ : ℕ → ℕ)
    (s s' : RAMState) (hr : s.regs = s'.regs) (hm : s.mem = s'.mem)
    (h : UpDataAtD N t C β δ y v m m₀ s) : UpDataAtD N t C β δ y v m m₀ s' := by
  rcases h with ⟨h6, h12, h13, h7, h10, hmem, hfr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact h6
  · rw [← hr]; exact h12
  · rw [← hr]; exact h13
  · intro hm1; rw [← hr]; exact h7 hm1
  · intro hm1; rw [← hr]; exact h10 hm1
  · intro addr ha; rw [← hm]; exact hmem addr ha
  · intro c hc; rw [← hm]; exact hfr c hc

theorem UpDataAtD_pc (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m p : ℕ) (m₀ : ℕ → ℕ) (s : RAMState)
    (h : UpDataAtD N t C β δ y v m m₀ s) : UpDataAtD N t C β δ y v m m₀ { s with pc := p } := by
  rcases h with ⟨h6, h12, h13, h7, h10, hmem, hfr⟩
  exact ⟨h6, h12, h13, h7, h10, hmem, hfr⟩

/-! ## D.3  One body step at `det` base `δ` -/

theorem upBody_data_atD (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ Bw : ℕ)
    (hBw : cr23Graph0 N ≤ Bw) (hfit : δ + Bw ≤ 2 ^ E.W)
    (hβfit : β + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W)
    (hdet : ∀ a < Bw, E.det (δ + a) = cr23DecDetAt N t C β a)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (a j : ℕ) (hj : j + 1 ≤ cr23D N)
    (m₀ : ℕ → ℕ) (s : RAMState) (hR : UpDataAtD N t C β δ y v (j + 1) m₀ s) :
    UpDataAtD N t C β δ y v j m₀ (runBlock progUpBody E { s with pc := a + 1 }) := by
  obtain ⟨h6, h12, h13, h7, h10, hm, hfr⟩ := hR
  have hW : 0 < cr23Word N := cr23Word_pos N
  have hD : 0 < cr23D N := cr23D_pos N hN
  have hi : cr23D N - (j + 1) < cr23D N := by omega
  have hsucc : cr23D N - (j + 1) + 1 = cr23D N - j := by omega
  have hjW : j < 2 ^ E.W := by rw [hEW]; exact lt_trans (by omega : j < cr23D N) (cr23D_lt_word N hN)
  have h2j : 2 * (cr23D N - j) ≤ 2 * cr23D N := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hdelta : cr23Delta N t C (cr23D N - j) v
      = cr23Delta N t C (cr23D N - (j + 1)) v + cr23Lvl N t C v (cr23D N - (j + 1)) := by
    rw [← hsucc]
    exact cr23Delta_succ N t C (cr23D N - (j + 1)) v
  have hpack : ∀ addr, packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v) addr
      = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v) addr
        ^^^ packMem (cr23Word N) (cr23Lvl N t C v (cr23D N - (j + 1))) addr := by
    intro addr
    rw [hdelta, ← add_assoc, packMem_add (cr23Word N) hW]
  have hval : packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v)
        (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
      = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v)
          (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
        ^^^ cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hpack, packMem_cr23Lvl N t C v (cr23D N - (j + 1)) hi, if_pos rfl]
  set iA : ℕ := upBase N v.val + 2 * (cr23D N - (j + 1)) with hiA
  set iM : ℕ := upBase N v.val + 1 + 2 * (cr23D N - (j + 1)) with hiM
  have hIdxA : iA < Bw := by
    rw [hiA]
    exact lt_of_lt_of_le (upBase_add_two_lt_graph0 N hN v (m := j + 1) (by omega)) hBw
  have hIdxM : iM < Bw := by
    rw [hiM]
    exact lt_of_lt_of_le (upBase_add_two_succ_lt_graph0 N hN v (m := j + 1) (by omega)) hBw
  have hargA : δ + upBase N v.val + 2 * (cr23D N - (j + 1)) = δ + iA := by rw [hiA]; omega
  have hargM : δ + upBase N v.val + 1 + 2 * (cr23D N - (j + 1)) = δ + iM := by rw [hiM]; omega
  have h7' : s.regs r7 = δ + iA := by rw [← hargA]; exact h7 (by omega)
  have h10' : s.regs r10 = δ + iM := by rw [← hargM]; exact h10 (by omega)
  have hdetA : E.det (δ + iA) = β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hdet iA hIdxA, cr23DecDetAt_addr N t C hN β v ⟨cr23D N - (j + 1), hi⟩]
  have hdetM : E.det (δ + iM) = cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hdet iM hIdxM]
    rw [hiM]
    rw [show upBase N v.val + 1 + 2 * (cr23D N - (j + 1))
        = upBase N v.val + 2 * (cr23D N - (j + 1)) + 1 from by ring]
    exact cr23DecDetAt_mask N t C hN β v ⟨cr23D N - (j + 1), hi⟩
  have hAW : cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
      < wordsOf (cr23Word N) (cr23R N t) := DecXorPay.addr_wordsOf N t hN htN C _ v
  have hbA : β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v < 2 ^ E.W := by
    have hfitW : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N := by
      rwa [hEW] at hβfit
    have hAWW : cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
        < wordsOf (cr23Word N) (cr23R N t) := hAW
    rw [hEW]
    omega
  have hmask_lt : cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v < 2 ^ E.W := by
    rw [hEW]; exact cr23Mask_lt N t C ⟨cr23D N - (j + 1), hi⟩ v
  have hpacklt : packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v)
      (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v) < 2 ^ E.W := by
    rw [hEW]; exact packMem_lt (cr23Word N) hW _ _
  have hxorlt : (packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v)
      (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
      ^^^ cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v) < 2 ^ E.W :=
    Nat.xor_lt_two_pow hpacklt hmask_lt
  have hmA : s.mem (β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
      = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v)
          (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v) := hm _ hAW
  set st1 : RAMState := runBlock upBodyA E { s with pc := a + 1 } with hst1
  have h1mem : st1.mem = s.mem := by
    rw [hst1]
    exact upBodyA_mem _ _
  have h1r8 : st1.regs r8 = β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hst1, upBodyA_r8]
    rw [h7', hdetA, Nat.mod_eq_of_lt hbA]
  have h1r10 : st1.regs r10 = δ + iM := by
    rw [hst1, upBodyA_frame _ _ r10 (by decide) (by decide) (by decide)]
    exact h10'
  have h1r7 : st1.regs r7 = δ + iA := by
    rw [hst1, upBodyA_frame _ _ r7 (by decide) (by decide) (by decide)]
    exact h7'
  have h1r12 : st1.regs r12 = 2 := by
    rw [hst1, upBodyA_frame _ _ r12 (by decide) (by decide) (by decide)]
    exact h12
  have h1r13 : st1.regs r13 = 1 := by
    rw [hst1, upBodyA_frame _ _ r13 (by decide) (by decide) (by decide)]
    exact h13
  have h1r6 : st1.regs r6 = j + 1 := by
    rw [hst1, upBodyA_frame _ _ r6 (by decide) (by decide) (by decide)]
    exact h6
  have h1r4 : st1.regs r4 = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v)
      (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v) := by
    rw [hst1, upBodyA_r4]
    rw [h7', h10', hdetA, Nat.mod_eq_of_lt hbA, hdetM, Nat.mod_eq_of_lt hmask_lt, hmA,
      Nat.mod_eq_of_lt hpacklt, Nat.mod_eq_of_lt hxorlt, hval]
  set st2 : RAMState := execInstr (iSt r8 r4) E st1 with hst2
  have h2mem : st2.mem
      = Function.update s.mem (β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
          (packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v)
            (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)) := by
    rw [hst2, execInstr_store, h1mem, h1r8, h1r4]
  have h2r6 : st2.regs r6 = j + 1 := by
    rw [hst2, execInstr_store]; exact h1r6
  have h2r7 : st2.regs r7 = δ + iA := by
    rw [hst2, execInstr_store]; exact h1r7
  have h2r10 : st2.regs r10 = δ + iM := by
    rw [hst2, execInstr_store]; exact h1r10
  have h2r12 : st2.regs r12 = 2 := by
    rw [hst2, execInstr_store]; exact h1r12
  have h2r13 : st2.regs r13 = 1 := by
    rw [hst2, execInstr_store]; exact h1r13
  set st3 : RAMState := execInstr (iAdd r7 r7 r12) E st2 with hst3
  set st4 : RAMState := execInstr (iAdd r10 r10 r12) E st3 with hst4
  set st5 : RAMState := execInstr (iSub r6 r6 r13) E st4 with hst5
  have h3f : ∀ d : Fin 16, r7 ≠ d → st3.regs d = st2.regs d := by
    intro d hd
    rw [hst3]
    exact execInstr_regs (iAdd r7 r7 r12) _ st2 d (by simpa [Instr.dest?] using hd)
  have h4f : ∀ d : Fin 16, r10 ≠ d → st4.regs d = st3.regs d := by
    intro d hd
    rw [hst4]
    exact execInstr_regs (iAdd r10 r10 r12) _ st3 d (by simpa [Instr.dest?] using hd)
  have h5f : ∀ d : Fin 16, r6 ≠ d → st5.regs d = st4.regs d := by
    intro d hd
    rw [hst5]
    exact execInstr_regs (iSub r6 r6 r13) _ st4 d (by simpa [Instr.dest?] using hd)
  have h3r7 : st3.regs r7 = (st2.regs r7 + 2) % 2 ^ E.W := by
    simp only [hst3, execInstr_add, Function.update_self, h2r12]
  have h4r10 : st4.regs r10 = (st3.regs r10 + 2) % 2 ^ E.W := by
    simp only [hst4, execInstr_add, Function.update_self, h3f r10 (by decide),
      h3f r12 (by decide), h2r12]
  have h5r6 : st5.regs r6 = (st4.regs r6 + 2 ^ E.W - st4.regs r13) % 2 ^ E.W := by
    simp only [hst5, execInstr_sub, Function.update_self]
  have hbody : runBlock progUpBody E { s with pc := a + 1 } = st5 := by
    simp only [upBody_split, runBlock_append, runBlock_cons, runBlock_nil, ← hst1, ← hst2,
      ← hst3, ← hst4, ← hst5]
  rw [hbody]
  have h5m : st5.mem = st2.mem := by
    simp only [hst5, hst4, hst3, execInstr_sub, execInstr_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5r6, h4f r6 (by decide), h3f r6 (by decide), h2r6, h4f r13 (by decide),
      h3f r13 (by decide), h2r13]
    have e : j + 1 + 2 ^ E.W - 1 = j + 2 ^ E.W := by omega
    rw [e, show j + 2 ^ E.W = j + 1 * 2 ^ E.W from by ring,
      Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hjW
  · rw [h5f r12 (by decide), h4f r12 (by decide), h3f r12 (by decide)]
    exact h2r12
  · rw [h5f r13 (by decide), h4f r13 (by decide), h3f r13 (by decide)]
    exact h2r13
  · intro hj1
    rw [h5f r7 (by decide), h4f r7 (by decide), h3r7, h2r7]
    have e : δ + iA + 2 = δ + upBase N v.val + 2 * (cr23D N - j) := by
      rw [hiA]
      rw [show δ + (upBase N v.val + 2 * (cr23D N - (j + 1))) + 2
          = δ + (upBase N v.val + 2 * (cr23D N - (j + 1) + 1)) from by ring, hsucc]
      omega
    rw [e]
    refine Nat.mod_eq_of_lt ?_
    have h := upBase_add_two_lt_graph0 N hN v (m := j) hj1
    omega
  · intro hj1
    rw [h5f r10 (by decide), h4r10, h3f r10 (by decide), h2r10]
    have e : δ + iM + 2 = δ + upBase N v.val + 1 + 2 * (cr23D N - j) := by
      rw [hiM]
      rw [show δ + (upBase N v.val + 1 + 2 * (cr23D N - (j + 1))) + 2
          = δ + (upBase N v.val + 1 + 2 * (cr23D N - (j + 1) + 1)) from by ring, hsucc]
      omega
    rw [e]
    refine Nat.mod_eq_of_lt ?_
    have h := upBase_add_two_succ_lt_graph0 N hN v (m := j) hj1
    omega
  · intro addr haddr
    rw [h5m, h2mem]
    by_cases had : addr = cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
    · subst had
      rw [Function.update_self]
    · rw [Function.update_of_ne (by intro hh; exact had (Nat.add_left_cancel hh)),
        hm addr haddr, hpack addr, packMem_cr23Lvl N t C v (cr23D N - (j + 1)) hi, if_neg had,
        Nat.xor_zero]
  · intro c hc
    rw [h5m, h2mem]
    have hne : c ≠ β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by omega
    rw [Function.update_of_ne hne]
    exact hfr c hc

/-! ## D.4  The loop iteration (at an arbitrary base) -/

theorem upBodyIter_atD (G : Program) (base : ℕ) (hAt : At G base (cr23UpStmtAt.compile base))
    (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ Bw : ℕ)
    (hBw : cr23Graph0 N ≤ Bw) (hfit : δ + Bw ≤ 2 ^ E.W)
    (hβfit : β + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W)
    (hdet : ∀ a < Bw, E.det (δ + a) = cr23DecDetAt N t C β a)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (j : ℕ) (hj : j + 1 ≤ cr23D N)
    (m₀ : ℕ → ℕ) (s : RAMState) (hR : UpDataAtD N t C β δ y v (j + 1) m₀ s) :
    Sem G E (base + 14) (base + 13) { s with pc := base + 14 }
      (fun k s' => k ≤ 9 ∧ UpDataAtD N t C β δ y v j m₀ s' ∧ s'.pc = base + 13) := by
  have hbd := upBody_data_atD N t hN htN E hEW C β δ Bw hBw hfit hβfit hdet y v
    (base + 13) j hj m₀ s hR
  have hno : NoBranch progUpBody := by simp [progUpBody]
  have hAt' : At G base (cr23UpPreAt ++
      Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) (base + 13)) := by
    rwa [cr23UpStmtAt_compile_eq] at hAt
  have hloopAt : At G (base + 13)
      (Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) (base + 13)) :=
    At.drop (A := cr23UpPreAt) hAt'
  obtain ⟨-, -, hbodyAt, hjmp⟩ := at_loop hloopAt
  have hblk : Sem G E (base + 14) (base + 22) { s with pc := base + 14 }
      (fun k s' => k = progUpBody.length ∧
        s' = runBlock progUpBody E { s with pc := base + 14 }) := by
    have h := Sem.block G E (base + 14) progUpBody { s with pc := base + 14 } hbodyAt hno rfl
    simpa [progUpBody] using h
  refine Sem.jmp_append hjmp ?_
  refine Sem.mono hblk ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  have h8 : progUpBody.length = 8 := rfl
  refine ⟨by omega, ?_, rfl⟩
  exact UpDataAtD.irrel N t C β δ y v j m₀ _ _ rfl rfl hbd
/-! ## D.5  The relocated prologue -/

theorem upPre_data_atD (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ Bw : ℕ)
    (hBw : cr23Graph0 N ≤ Bw) (hfit : δ + Bw ≤ 2 ^ E.W)
    (hdet : ∀ a < Bw, E.det (δ + a) = cr23DecDetAt N t C β a)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (s : RAMState)
    (h14 : s.regs 14 = δ) (h0 : s.regs 0 = v.val)
    (hmem : ∀ addr < wordsOf (cr23Word N) (cr23R N t),
      s.mem (β + addr) = packMem (cr23Word N) y addr) :
    UpDataAtD N t C β δ y v (cr23D N) s.mem (runBlock cr23UpPreAt E s) := by
  have hW : 0 < cr23Word N := cr23Word_pos N
  have h1mod : (1 : ℕ) % 2 ^ E.W = 1 := by
    rw [hEW]; exact Nat.mod_eq_of_lt (cr23_one_lt_word N hN)
  have h2mod : (2 : ℕ) % 2 ^ E.W = 2 := by
    rw [hEW]; exact Nat.mod_eq_of_lt (cr23_two_lt_word N hN)
  have hDmod : cr23D N % 2 ^ E.W = cr23D N := by
    rw [hEW]; exact Nat.mod_eq_of_lt (cr23D_lt_word N hN)
  have hgpos : 0 < Bw := lt_of_lt_of_le (graph0_pos N hN) hBw
  have hδlt : δ < 2 ^ E.W := by have := hfit; omega
  have hδmod : δ % 2 ^ E.W = δ := Nat.mod_eq_of_lt hδlt
  have hδD : E.det δ = cr23D N := by
    have h := hdet 0 hgpos
    rwa [Nat.add_zero, cr23DecDetAt_zero N t C hN β] at h
  have hv1Bw : v.val + 1 < Bw := lt_of_lt_of_le (succ_lt_graph0 N hN v) hBw
  have hbaseD : E.det (δ + (v.val + 1)) = upBase N v.val := by
    rw [hdet (v.val + 1) hv1Bw, show v.val + 1 = 1 + v.val from by omega,
      cr23DecDetAt_base N t C hN β v]
  have hvδlt : v.val + δ < 2 ^ E.W := by have := hfit; omega
  have hvδ1lt : v.val + δ + 1 < 2 ^ E.W := by have := hfit; omega
  have hvδmod : (v.val + δ) % 2 ^ E.W = v.val + δ := Nat.mod_eq_of_lt hvδlt
  have hvδ1mod : (v.val + δ + 1) % 2 ^ E.W = v.val + δ + 1 := Nat.mod_eq_of_lt hvδ1lt
  have hbaseDm : E.det (v.val + δ + 1) = upBase N v.val := by
    rw [show v.val + δ + 1 = δ + (v.val + 1) from by omega]; exact hbaseD
  have hbδlt : upBase N v.val + δ < 2 ^ E.W := by
    have h := upBase_lt_graph0 N hN v; have := hfit; omega
  have hbmod : upBase N v.val % 2 ^ E.W = upBase N v.val := by
    rw [hEW]; exact Nat.mod_eq_of_lt (upBase_lt N hN v)
  have hbδmod : (upBase N v.val + δ) % 2 ^ E.W = upBase N v.val + δ :=
    Nat.mod_eq_of_lt hbδlt
  have hb1Bw : upBase N v.val + 1 < Bw :=
    lt_of_lt_of_le (upBase_succ_lt_graph0 N hN v) hBw
  have hbδmod2 : (δ + upBase N v.val) % 2 ^ E.W = δ + upBase N v.val := by
    rw [Nat.add_comm]; exact hbδmod
  have hbδ1mod2 : (δ + upBase N v.val + 1) % 2 ^ E.W = δ + upBase N v.val + 1 := by
    refine Nat.mod_eq_of_lt ?_
    have := hfit
    omega
  have hcomm : upBase N v.val + δ = δ + upBase N v.val := by omega
  have hcomm1 : upBase N v.val + δ + 1 = δ + upBase N v.val + 1 := by omega
  have hmemEq : (runBlock cr23UpPreAt E s).mem = s.mem := by
    simp only [cr23UpPreAt, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor]
  have hcombo : ((E.det (((v.val + δ) % 2 ^ E.W + 1 % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W
      + δ % 2 ^ E.W) % 2 ^ E.W) = upBase N v.val + δ := by
    rw [hvδmod, h1mod, hvδ1mod, hbaseDm, hbmod, hδmod, hbδmod]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cr23UpPreAt, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, h14, h0, hδmod, hδD, hDmod, h1mod, h2mod, hvδmod,
      hvδ1mod, hbaseDm, hcombo, nat_lor_self]
  · simp [cr23UpPreAt, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, h2mod]
  · simp [cr23UpPreAt, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, h1mod]
  · intro _
    simp [cr23UpPreAt, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, h14, h0, hδmod, hδD, hDmod, h1mod, h2mod, hvδmod,
      hvδ1mod, hbaseDm, hcombo, hcomm, hcomm1, hbδmod2, hbδ1mod2, nat_lor_self]
  · intro _
    simp [cr23UpPreAt, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, h14, h0, hδmod, hδD, hDmod, h1mod, h2mod, hvδmod,
      hvδ1mod, hbaseDm, hcombo, hcomm, hcomm1, hbδmod2, hbδ1mod2, nat_lor_self]
  · intro addr haddr
    rw [hmemEq]
    have e : cr23D N - cr23D N = 0 := by omega
    rw [e, cr23Delta_zero]
    simpa using hmem addr haddr
  · intro c hc
    rw [hmemEq]
/-! ## D.6  The loop at `det` base `δ` -/

/-- The runtime bound `10·D + 15` (the relocated block costs two more steps than `progUp`). -/
theorem upCost_le' (N : ℕ) (hN : 1 ≤ N) :
    10 * (cr23D N : ℝ) + 15 ≤ 65536 * lg ((N : ℝ) + 2) ^ 2 := by
  have hD : (cr23D N : ℝ) = 1024 * (cr23Lb N : ℝ) := by
    simp only [cr23D]
    push_cast
    ring
  have hc : (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := cr23_lb_le N hN
  have hlg : (1 : ℝ) ≤ lg ((N : ℝ) + 2) := cr23_one_le_lg N hN
  have hsq : lg ((N : ℝ) + 2) ≤ lg ((N : ℝ) + 2) ^ 2 := by nlinarith only [hlg]
  rw [hD]
  nlinarith only [hc, hlg, hsq]

theorem upLoop_data_atD (G : Program) (base : ℕ) (hAt : At G base (cr23UpStmtAt.compile base))
    (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β δ Bw : ℕ)
    (hBw : cr23Graph0 N ≤ Bw) (hfit : δ + Bw ≤ 2 ^ E.W)
    (hβfit : β + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W)
    (hdet : ∀ a < Bw, E.det (δ + a) = cr23DecDetAt N t C β a)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (s : RAMState) (hpc : s.pc = base + 13)
    (hR : UpDataAtD N t C β δ y v (cr23D N) s.mem s) :
    Sem G E (base + 13) (base + 23) s
      (fun k s' => k ≤ cr23D N * 10 + 1 ∧ UpDataAtD N t C β δ y v 0 s.mem s' ∧
        s'.pc = base + 23) := by
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hAt' : At G base (cr23UpPreAt ++
      Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) (base + 13)) := by
    rwa [cr23UpStmtAt_compile_eq] at hAt
  have hloopAt : At G (base + 13)
      (Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) (base + 13)) :=
    At.drop (A := cr23UpPreAt) hAt'
  have hirr : ∀ (j : ℕ) (s1 s2 : RAMState), s1.regs = s2.regs → s1.mem = s2.mem →
      (UpDataAtD N t C β δ y v j s.mem s1 ∧ j ≤ cr23D N) →
      (UpDataAtD N t C β δ y v j s.mem s2 ∧ j ≤ cr23D N) := by
    intro j s1 s2 hr hm h
    exact ⟨UpDataAtD.irrel N t C β δ y v j s.mem s1 s2 hr hm h.1, h.2⟩
  have hstop : ∀ s', (UpDataAtD N t C β δ y v 0 s.mem s' ∧ 0 ≤ cr23D N) → s'.regs r6 = 0 := by
    intro s' h
    exact h.1.1
  have hgo : ∀ j s', (UpDataAtD N t C β δ y v (j + 1) s.mem s' ∧ j + 1 ≤ cr23D N) →
      s'.regs r6 ≠ 0 := by
    intro j s' h
    rw [h.1.1]
    omega
  have hstep : ∀ j s', (UpDataAtD N t C β δ y v (j + 1) s.mem s' ∧ j + 1 ≤ cr23D N) →
      Sem G E (base + 14) (base + 13) { s' with pc := base + 14 }
        (fun k s'' => k ≤ 9 ∧ (UpDataAtD N t C β δ y v j s.mem s'' ∧ j ≤ cr23D N) ∧
          s''.pc = base + 13) := by
    intro j s' h
    refine Sem.mono
      (upBodyIter_atD G base hAt N t hN htN E hEW C β δ Bw hBw hfit hβfit hdet y v j h.2
        s.mem s' h.1) ?_
    intro k s'' hk
    exact ⟨hk.1, ⟨hk.2.1, by omega⟩, hk.2.2⟩
  have hloop := Sem.loopCountUp G E (base + 13) r6 (Stmt.code progUpBody) hloopAt hW (cr23D N)
    (fun j s' => UpDataAtD N t C β δ y v j s.mem s' ∧ j ≤ cr23D N) 9 hirr hstop hgo hstep s hpc
    ⟨hR, le_rfl⟩
  exact Sem.mono hloop (fun k s' h => ⟨h.1, h.2.1.1, h.2.2⟩)

/-! ## D.7  The contract shape Theorem 6.5's conjunct 6 must consume

The published `CrSemAt`/`UpBlkSemB` omit the *payload-word fit* `β + wordsOf E.W M ≤ 2^E.W`.  It is
not derivable from their premises: `iTbl` reduces the table value modulo `2^E.W`, so a payload base
`β` with `β + wordsOf … > 2^E.W` makes the block address the wrong words, and the payload clause of
the contract is false (the frame and the payload premise are satisfiable for every `β`).  The
shapes below add the fit, and are the ones the assembly must consume. -/

/-- `UpBlkSemB` **plus the payload-word fit**. -/
def UpBlkSemC (Sup : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N : ℕ} (Ms : ℕ)
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ), β + wordsOf E.W Ms ≤ 2 ^ E.W →
  ∀ (dt : ℕ → ℕ) (y : Fin Ms → ZMod 2) (i : Fin N) (s : RAMState),
    At G base (Sup.compile base) → s.pc = base →
    δ + Bw ≤ 2 ^ E.W →
    (∀ a < Bw, E.det (δ + a) = dt a) →
    s.regs 14 = δ → s.regs 15 = β → s.regs 0 = i.val →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sup.len ∧
      (∀ q < wordsOf E.W Ms, out.mem (β + q) = packMem E.W (y + Hs (Pi.single i 1)) q) ∧
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = s.mem a) ∧
      out.regs 0 = s.regs 0 ∧ out.regs 1 = s.regs 1 ∧ out.regs 2 = s.regs 2 ∧
      out.regs 3 = s.regs 3 ∧ out.regs 4 = s.regs 4

/-- One `UpBlkSemC` per child block, at the caller's pinned width. -/
def UpChildSemC {ι : Type} (Sup : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N : ℕ}
    (Ms : ι → ℕ) (Hs : (p : ι) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (Ms p) → ZMod 2)) : Prop :=
  ∀ p : ι, UpBlkSemC Sup E T Bw (Ms p) (Hs p)

/-- The published `CrSemAt` **plus the payload-word fit**: the exact contract the composite's `CR`
block meets, with `Bw` pinned, the table pinned to 2.3's `cr23DecDetAt`, the `det` base and payload
base read from `r14`/`r15`, a two-sided frame against the caller's memory, and no register clauses. -/
def CrSemAtW (Sup : Stmt) (E : RAMEnv) (T : ℝ) (Bw N t : ℕ)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ), β + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W →
  ∀ (y : Fin (cr23R N t) → ZMod 2) (i : Fin N) (s : RAMState),
    At G base (Sup.compile base) → s.pc = base →
    δ + Bw ≤ 2 ^ E.W →
    (∀ a < Bw, E.det (δ + a) = cr23DecDetAt N t C β a) →
    s.regs 14 = δ → s.regs 15 = β → s.regs 0 = i.val →
    (∀ q < wordsOf E.W (cr23R N t), s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sup.len ∧
      (∀ q < wordsOf E.W (cr23R N t),
        out.mem (β + q) = packMem E.W (y + cr23Sketch N t C (Pi.single i 1)) q) ∧
      (∀ a, a < β ∨ β + wordsOf E.W (cr23R N t) ≤ a → out.mem a = s.mem a)

/-- **The `CrSemAt` export for Proposition 2.3's relocated block.**  `cr23UpStmtAt` toggles column
`i` of 2.3's `CR` sketch into the payload at `β`, at `det` base `δ`, in `10·D + 14` steps. -/
theorem cr23UpStmtAt_crSemAtW (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (E : RAMEnv) (hEW : E.W = cr23Word N) (Bw : ℕ) (hBw : cr23Graph0 N ≤ Bw) :
    CrSemAtW cr23UpStmtAt E (65536 * lg ((N : ℝ) + 2) ^ 2) Bw N t C := by
  intro G base δ β hβfit y i s hAt hpc hfit hdet h14 h15 h0 hmem
  have hno : NoBranch cr23UpPreAt := by
    simp [cr23UpPreAt, NoBranch, Instr.NoBranchI]
  have hAt' : At G base (cr23UpPreAt ++
      Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) (base + 13)) := by
    rwa [cr23UpStmtAt_compile_eq] at hAt
  have hpreAt : At G base cr23UpPreAt := At.take hAt'
  have hmem' : ∀ addr < wordsOf (cr23Word N) (cr23R N t),
      s.mem (β + addr) = packMem (cr23Word N) y addr := by
    intro addr h
    have h' : addr < wordsOf E.W (cr23R N t) := by rwa [hEW]
    have := hmem addr h'
    rwa [hEW] at this
  have hUpd : UpDataAtD N t C β δ y i (cr23D N) s.mem (runBlock cr23UpPreAt E s) :=
    upPre_data_atD N t hN htN E hEW C β δ Bw hBw hfit hdet y i s h14 h0 hmem'
  have hpre : Sem G E base (base + 13) s
      (fun k s' => k = 13 ∧ s' = runBlock cr23UpPreAt E s) :=
    Sem.block G E base cr23UpPreAt s hpreAt hno hpc
  have hpcpre : (runBlock cr23UpPreAt E s).pc = base + 13 := by
    rw [runBlock_pc cr23UpPreAt E s hno, hpc, cr23UpPreAt_length]
  have hloop := upLoop_data_atD G base hAt N t hN htN E hEW C β δ Bw hBw hfit hβfit hdet y i
    (runBlock cr23UpPreAt E s) hpcpre hUpd
  have hmain : Sem G E base (base + 23) s
      (fun k s' => k ≤ 13 + (cr23D N * 10 + 1) ∧
        UpDataAtD N t C β δ y i 0 s.mem s' ∧ s'.pc = base + 23) := by
    refine Sem.mono (Sem.seq (Q₂ := fun k1 k2 s' => k1 = 13 ∧
      (k2 ≤ cr23D N * 10 + 1 ∧ UpDataAtD N t C β δ y i 0 s.mem s' ∧
        s'.pc = base + 23)) hpre ?_) ?_
    · intro k1 s1 h1
      obtain ⟨rfl, rfl⟩ := h1
      exact Sem.mono hloop (fun k s' h => ⟨rfl, h⟩)
    · intro k s' h
      obtain ⟨k1, k2, hk, hk1, hlt, hU, hpc23⟩ := h
      subst hk1
      exact ⟨by omega, hU, hpc23⟩
  obtain ⟨-, k, out, hstep, hpcout, hQ⟩ := hmain
  obtain ⟨hk, hU, hpc'⟩ := hQ
  refine ⟨k, out, ?_, hstep, ?_, ?_, ?_⟩
  · have hcost := upCost_le' N hN
    have hkR : (k : ℝ) ≤ ((13 + (cr23D N * 10 + 1) : ℕ) : ℝ) := by exact_mod_cast hk
    have hk' : ((13 + (cr23D N * 10 + 1) : ℕ) : ℝ) = 10 * (cr23D N : ℝ) + 14 := by
      push_cast
      ring
    linarith only [hkR, hk', hcost]
  · rw [hpc', cr23UpStmtAt_len]
  · intro q hq
    obtain ⟨-, -, -, -, -, hp, -⟩ := hU
    have hcol : cr23Delta N t C (cr23D N - 0) i = cr23Sketch N t C (Pi.single i 1) := by
      rw [Nat.sub_zero]
      exact cr23Delta_full N t C i
    rw [hcol] at hp
    rw [hEW] at hq ⊢
    exact hp q hq
  · obtain ⟨-, -, -, -, -, -, hfr⟩ := hU
    rw [hEW]
    exact hfr

end LinearSetReconciliation327.Main

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

noncomputable section

/-! ## 0. The two sources of the per-block and `CR` contracts -/

/-- The `CR` contract of the assembly, restated in exactly the form the assembly consumes:
`CrSemAtW` at `Bw = Rpad`, `δ`-relative, with the payload base already specialised to the
composite's `blkTotal E.W f`.  This is 2.3's export `cr23UpStmtAt_crSemAtW`, nothing else. -/
theorem crSemAtW_cr_block (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (E : RAMEnv) (hEW : E.W = cr23Word N) (Rpad : ℕ) (hBw : cr23Graph0 N ≤ Rpad) :
    CrSemAtW cr23UpStmtAt E (65536 * lg ((N : ℝ) + 2) ^ 2) Rpad N t C :=
  cr23UpStmtAt_crSemAtW N t hN htN C E hEW Rpad hBw

/-- `hCr` is **inhabited**, not assumed: at the concrete environment `⟨cr23Word N, 0, …⟩` the
published export gives the `CR` contract outright. -/
theorem crSemAtW_inhabited (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (Rpad : ℕ) (hBw : cr23Graph0 N ≤ Rpad) :
    CrSemAtW cr23UpStmtAt ⟨cr23Word N, fun _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0⟩ (65536 * lg ((N : ℝ) + 2) ^ 2) Rpad N t C :=
  cr23UpStmtAt_crSemAtW N t hN htN C
    ⟨cr23Word N, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩ rfl Rpad hBw

/-- The only per-block hypothesis the restated assembly keeps, written out: Theorem 5.1's export has
to supply, for each child block `p` and at the caller's **pinned** width `2^Wd`, the block contract
with the payload-word fit `β + wordsOf E.W (f p) ≤ 2^E.W`.  There is no `∀ Bw`. -/
theorem upChildSemC_iff {ι : Type} (Sup : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N : ℕ}
    (Ms : ι → ℕ) (Hs : (p : ι) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (Ms p) → ZMod 2)) :
    UpChildSemC Sup E T Bw Ms Hs ↔ ∀ p : ι, UpBlkSemC Sup E T Bw (Ms p) (Hs p) :=
  Iff.rfl

/-! ## A. The composite `det` with `det 3 = blkTotal` -/

/-- `compUpDet` with one more metadata cell: address `3` holds `bt = blkTotal W f`, the payload word
base of the `CR` block.  Addresses `0,1,2` and every address `≥ 2^Wd` are exactly as in
`compUpDet`. -/
def compUpDetB {l : ℕ} (Wd Rpad : ℕ) (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ)
    (b : Fin l → ℕ) (bt : ℕ) : ℕ → ℕ :=
  fun a =>
    if a < 2 ^ Wd then
      (if a = 0 then l + 1
       else if a = 1 then 2 ^ Wd
       else if a = 2 then compPayBase l Wd Rpad - 1
       else if a = 3 then bt else 0)
    else compDet Wd dt (compCRDet Rpad dcr b) (a - 2 ^ Wd)

/-- The low (metadata) block of `compUpDetB`, away from the four named cells. -/
theorem compUpDetB_meta {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) {a : ℕ} (ha : a < 2 ^ Wd) (h0 : a ≠ 0) (h1 : a ≠ 1) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    compUpDetB Wd Rpad dt dcr b bt a = 0 := by
  unfold compUpDetB
  rw [if_pos ha, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

/-- Metadata cell `0`: the loop bound `l + 1`. -/
theorem compUpDetB_zero {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) (h : 0 < 2 ^ Wd) : compUpDetB Wd Rpad dt dcr b bt 0 = l + 1 := by
  unfold compUpDetB
  rw [if_pos h, if_pos rfl]

/-- Metadata cell `1`: the block width `2^Wd`. -/
theorem compUpDetB_one {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) (h : 1 < 2 ^ Wd) : compUpDetB Wd Rpad dt dcr b bt 1 = 2 ^ Wd := by
  unfold compUpDetB
  rw [if_pos h, if_neg (by norm_num), if_pos rfl]

/-- Metadata cell `2`: the address of `beta_0`, minus one. -/
theorem compUpDetB_two {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) (h : 2 < 2 ^ Wd) : compUpDetB Wd Rpad dt dcr b bt 2 = compPayBase l Wd Rpad - 1 := by
  unfold compUpDetB
  rw [if_pos h, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

/-- Metadata cell `3`: the payload word base `blkTotal W f` of the `CR` block. -/
theorem compUpDetB_three {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) (h : 3 < 2 ^ Wd) : compUpDetB Wd Rpad dt dcr b bt 3 = bt := by
  unfold compUpDetB
  rw [if_pos h, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

/-- Inside child `s`'s block (address `(s+1)*2^Wd + k`) the composite `det` is child `s`'s table. -/
theorem compUpDetB_child {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) (s : Fin l) {k : ℕ} (hk : k < 2 ^ Wd) :
    compUpDetB Wd Rpad dt dcr b bt ((s.val + 1) * 2 ^ Wd + k) = dt s k := by
  have hW : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have hshift : (s.val + 1) * 2 ^ Wd + k - 2 ^ Wd = s.val * 2 ^ Wd + k := by
    rw [Nat.succ_mul]; omega
  have hge : ¬ ((s.val + 1) * 2 ^ Wd + k < 2 ^ Wd) := by
    rw [Nat.succ_mul]; omega
  have hdiv : (s.val * 2 ^ Wd + k) / 2 ^ Wd = s.val := nat_div_mul_add (2 ^ Wd) hW s.val k hk
  have hmod : (s.val * 2 ^ Wd + k) % 2 ^ Wd = k := nat_mod_mul_add (2 ^ Wd) s.val k hk
  unfold compUpDetB
  rw [if_neg hge, hshift,
    compDet_child dt (compCRDet Rpad dcr b) (a := s.val * 2 ^ Wd + k) (by rw [hdiv]; exact s.isLt)]
  rw [hmod]
  exact congrArg (fun t : Fin l => dt t k) (Fin.ext hdiv)

/-- Inside the `CR` block (address `(l+1)*2^Wd + q`, `q < Rpad`) the composite `det` is the `CR`
table. -/
theorem compUpDetB_cr {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) {q : ℕ} (hq : q < Rpad) (hfit : Rpad ≤ 2 ^ Wd) :
    compUpDetB Wd Rpad dt dcr b bt ((l + 1) * 2 ^ Wd + q) = dcr q := by
  have hW : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have hlt : q < 2 ^ Wd := lt_of_lt_of_le hq hfit
  have hshift : (l + 1) * 2 ^ Wd + q - 2 ^ Wd = l * 2 ^ Wd + q := by
    rw [Nat.succ_mul]; omega
  have hge : ¬ ((l + 1) * 2 ^ Wd + q < 2 ^ Wd) := by
    rw [Nat.succ_mul]; omega
  have hdiv : (l * 2 ^ Wd + q) / 2 ^ Wd = l := nat_div_mul_add (2 ^ Wd) hW l q hlt
  have hmod : (l * 2 ^ Wd + q) % 2 ^ Wd = q := nat_mod_mul_add (2 ^ Wd) l q hlt
  unfold compUpDetB
  rw [if_neg hge, hshift,
    compDet_cr dt (compCRDet Rpad dcr b) (a := l * 2 ^ Wd + q) hdiv, hmod]
  unfold compCRDet
  rw [if_pos hq]

/-- **The payload base of block `s` is a `qDet` away.** -/
theorem compUpDetB_pay {l Wd Rpad : ℕ} (dt : Fin l → ℕ → ℕ) (dcr : ℕ → ℕ) (b : Fin l → ℕ)
    (bt : ℕ) (s : Fin l) (hR : 0 < Rpad) (hfit : Rpad + s.val < 2 ^ Wd) :
    compUpDetB Wd Rpad dt dcr b bt (compPayBase l Wd Rpad - 1 + (s.val + 1)) = b s := by
  have hW : 0 < 2 ^ Wd := Nat.two_pow_pos Wd
  have hA : compPayBase l Wd Rpad - 1 + (s.val + 1) = (l + 1) * 2 ^ Wd + (Rpad + s.val) := by
    unfold compPayBase; omega
  rw [hA]
  have hshift : (l + 1) * 2 ^ Wd + (Rpad + s.val) - 2 ^ Wd
      = l * 2 ^ Wd + (Rpad + s.val) := by
    rw [Nat.succ_mul]; omega
  have hge : ¬ ((l + 1) * 2 ^ Wd + (Rpad + s.val) < 2 ^ Wd) := by
    rw [Nat.succ_mul]; omega
  have hfit' : Rpad + s.val < 2 ^ Wd := hfit
  have hdiv : (l * 2 ^ Wd + (Rpad + s.val)) / 2 ^ Wd = l :=
    nat_div_mul_add (2 ^ Wd) hW l (Rpad + s.val) hfit'
  have hmod : (l * 2 ^ Wd + (Rpad + s.val)) % 2 ^ Wd = Rpad + s.val :=
    nat_mod_mul_add (2 ^ Wd) l (Rpad + s.val) hfit'
  unfold compUpDetB
  rw [if_neg hge, hshift,
    compDet_cr dt (compCRDet Rpad dcr b) (a := l * 2 ^ Wd + (Rpad + s.val)) hdiv, hmod]
  unfold compCRDet compPayTbl
  rw [if_neg (by omega), dif_pos ⟨Nat.le_add_right _ _, by omega⟩]
  exact congrArg b (Fin.ext (by simp))

/-! ## B. `crSetup`: the two instructions between the loop and the `CR` block -/

/-- The setup of the `CR` block's two address registers: `r14 := r1 * r3` (the `det` base
`(l+1) * 2^Wd`, since the loop exits with `r1 = l+1`, `r3 = 2^Wd`) and `r15 := det 3` (the payload
word base `blkTotal W f`).  `r7` is dead at the loop exit, so it carries the constant `3`. -/
def crSetup : List Instr := [iMul r14 r1 r3, iImm r7 3, iTbl r15 r7]

theorem crSetup_noBranch : NoBranch crSetup := by
  simp [crSetup, NoBranch, Instr.NoBranchI]

/-- `crSetup` advances the program counter by three. -/
theorem crSetup_pc (E : RAMEnv) (s : RAMState) : (runBlock crSetup E s).pc = s.pc + 3 := by
  simp [crSetup, runBlock_cons, runBlock_nil, execInstr]

/-- `crSetup` does not touch memory. -/
theorem crSetup_mem (E : RAMEnv) (s : RAMState) : (runBlock crSetup E s).mem = s.mem := by
  simp [crSetup, runBlock_cons, runBlock_nil, execInstr]

/-- `crSetup`, run. -/
theorem crSetup_regs (E : RAMEnv) (s : RAMState) :
    (runBlock crSetup E s).regs
      = Function.update (Function.update (Function.update s.regs r14
          (s.regs 1 * s.regs 3 % 2 ^ E.W)) r7 (3 % 2 ^ E.W))
          r15 (E.det (3 % 2 ^ E.W) % 2 ^ E.W) := by
  simp [crSetup, runBlock_cons, runBlock_nil, execInstr]

/-- `r14` after `crSetup`. -/
theorem crSetup_regs_fourteen (E : RAMEnv) (s : RAMState) :
    (runBlock crSetup E s).regs r14 = s.regs 1 * s.regs 3 % 2 ^ E.W := by
  rw [crSetup_regs, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self]

/-- `r15` after `crSetup`. -/
theorem crSetup_regs_fifteen (E : RAMEnv) (s : RAMState) :
    (runBlock crSetup E s).regs r15 = E.det (3 % 2 ^ E.W) % 2 ^ E.W := by
  rw [crSetup_regs, Function.update_self]

/-- Registers other than `r14`, `r7`, `r15` after `crSetup`. -/
theorem crSetup_regs_of_ne (E : RAMEnv) (s : RAMState) {d : Fin 16}
    (h14 : d ≠ r14) (h7 : d ≠ r7) (h15 : d ≠ r15) :
    (runBlock crSetup E s).regs d = s.regs d := by
  rw [crSetup_regs, Function.update_of_ne h15, Function.update_of_ne h7,
    Function.update_of_ne h14]

/-- A form of `crSetup_regs_of_ne` for the four dispatcher registers. -/
theorem crSetup_regs_low (E : RAMEnv) (s : RAMState) {d : Fin 16}
    (h : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) :
    (runBlock crSetup E s).regs d = s.regs d := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    first
      | (rw [crSetup_regs, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)])
      | (rw [crSetup_regs, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)])

/-! ## C. The composite programme -/

/-- The `CR` part of the programme: the setup, then 2.3's `CR` block. -/
def compUpScrStmt (Scr : Stmt) : Stmt := .seq (.code crSetup) Scr

/-- The last piece: `halt`. -/
def sufB8 : Program := [Instr.halt]

/-- The `CR` block followed by `halt`. -/
def sufB7 (Sup Scr : Stmt) : Program := Scr.compile (18 + Sup.len) ++ sufB8

/-- `crSetup`, the `CR` block and `halt`. -/
def sufB6 (Sup Scr : Stmt) : Program := crSetup ++ sufB7 Sup Scr

/-- The trailing jump and the `CR` region. -/
def sufB5 (Sup Scr : Stmt) : Program := [iJmp 7] ++ sufB6 Sup Scr

/-- The increment and the tail. -/
def sufB4 (Sup Scr : Stmt) : Program := blkInc ++ sufB5 Sup Scr

/-- The child block and the tail. -/
def sufB3 (Sup Scr : Stmt) : Program := Sup.compile 12 ++ sufB4 Sup Scr

/-- The body setup and the tail. -/
def sufB2 (Sup Scr : Stmt) : Program := blkSetup ++ sufB3 Sup Scr

/-- The loop's `jz` and the tail. -/
def sufB1 (Sup Scr : Stmt) : Program := [iJz r7 (15 + Sup.len)] ++ sufB2 Sup Scr

/-- The loop test and the tail. -/
def sufB0 (Sup Scr : Stmt) : Program := blkCond.code ++ sufB1 Sup Scr

/-- The assembled toggle programme: the published prologue `compProCode`, the published loop with
exit address `15 + Sup.len`, `crSetup`, 2.3's `CR` block `Scr` at `18 + Sup.len`, then `halt`.  It is
written as a right-nested chain of literal pieces, so every address the composition needs is a
literal. -/
def progUpOfProB (Sup Scr : Stmt) : Program := compProCode ++ sufB0 Sup Scr

/-! ## D. The `At` facts, and the prologue's `Sem` -/

/-- The length of the loop setup. -/
@[simp] theorem blkSetup_length : blkSetup.length = 3 := rfl

/-- The length of the increment. -/
@[simp] theorem blkInc_length : blkInc.length = 2 := rfl

/-- The length of the loop test. -/
@[simp] theorem blkCond_code_length : blkCond.code.length = 1 := rfl

/-- The length of the prologue. -/
@[simp] theorem compProCode_length : compProCode.length = 7 := rfl

/-- The length of `crSetup`. -/
@[simp] theorem crSetup_length : crSetup.length = 3 := rfl

/-- `At` of the head of a right-nested chain. -/
theorem At.headR (l rest : Program) : At (l ++ rest) 0 l := by
  intro r hr
  rw [List.getElem?_append_left (l₁ := l) (by omega : 0 + r < l.length), Nat.zero_add]

/-- Moving an `At` fact one piece to the left along the chain. -/
theorem At.tailR {A B : Program} {a : ℕ} {l : List Instr} (h : At B a l) :
    At (A ++ B) (A.length + a) l := by
  intro r hr
  rw [show A.length + a + r = A.length + (a + r) from by omega]
  rw [List.getElem?_append_right (l₁ := A) (l₂ := B) (by omega)]
  rw [show A.length + (a + r) - A.length = a + r from by omega]
  exact h r hr

/-- Reindex an `At` fact. -/
theorem At.congr {P : Program} {a a' : ℕ} {l : List Instr} (h : At P a l) (e : a = a') :
    At P a' l := by
  subst e
  exact h

/-- Piece 1 of the chain. -/
theorem at_proCodeB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) 0 compProCode := by
  refine At.congr (At.headR compProCode (sufB0 Sup Scr)) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 2 of the chain. -/
theorem at_testB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) 7 blkCond.code := by
  refine At.congr (At.tailR (A := compProCode) (At.headR blkCond.code (sufB1 Sup Scr))) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 3 of the chain. -/
theorem getElem?_jzB (Sup Scr : Stmt) :
    (progUpOfProB Sup Scr)[8]? = some (iJz r7 (15 + Sup.len)) := by
  have h : At (progUpOfProB Sup Scr) 8 [iJz r7 (15 + Sup.len)] := by
    refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.headR [iJz r7 (15 + Sup.len)] (sufB2 Sup Scr)))) ?_
    simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega
  have h0 := h 0 (by simp)
  simpa using h0

/-- Piece 4 of the chain. -/
theorem at_setupB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) 9 blkSetup := by
  refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.headR blkSetup (sufB3 Sup Scr))))) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 5 of the chain. -/
theorem at_supB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) 12 (Sup.compile 12) := by
  refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.tailR (A := blkSetup) (At.headR (Sup.compile 12) (sufB4 Sup Scr)))))) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 6 of the chain. -/
theorem at_incB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) (12 + Sup.len) blkInc := by
  refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.tailR (A := blkSetup) (At.tailR (A := (Sup.compile 12)) (At.headR blkInc (sufB5 Sup Scr))))))) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 7 of the chain. -/
theorem getElem?_jmpB (Sup Scr : Stmt) :
    (progUpOfProB Sup Scr)[14 + Sup.len]? = some (iJmp 7) := by
  have h : At (progUpOfProB Sup Scr) (14 + Sup.len) [iJmp 7] := by
    refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.tailR (A := blkSetup) (At.tailR (A := (Sup.compile 12)) (At.tailR (A := blkInc) (At.headR [iJmp 7] (sufB6 Sup Scr)))))))) ?_
    simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega
  have h0 := h 0 (by simp)
  simpa using h0

/-- Piece 8 of the chain. -/
theorem at_crSetupB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) (15 + Sup.len) crSetup := by
  refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.tailR (A := blkSetup) (At.tailR (A := (Sup.compile 12)) (At.tailR (A := blkInc) (At.tailR (A := [iJmp 7]) (At.headR crSetup (sufB7 Sup Scr))))))))) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 9 of the chain. -/
theorem at_crB (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) (18 + Sup.len) (Scr.compile (18 + Sup.len)) := by
  refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.tailR (A := blkSetup) (At.tailR (A := (Sup.compile 12)) (At.tailR (A := blkInc) (At.tailR (A := [iJmp 7]) (At.tailR (A := crSetup) (At.headR (Scr.compile (18 + Sup.len)) (sufB8)))))))))) ?_
  simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega

/-- Piece 10 of the chain. -/
theorem progUpOfProB_halt (Sup Scr : Stmt) :
    (progUpOfProB Sup Scr)[18 + Sup.len + Scr.len]? = some Instr.halt := by
  have h : At (progUpOfProB Sup Scr) (18 + Sup.len + Scr.len) [Instr.halt] := by
    refine At.congr (At.tailR (A := compProCode) (At.tailR (A := blkCond.code) (At.tailR (A := [iJz r7 (15 + Sup.len)]) (At.tailR (A := blkSetup) (At.tailR (A := (Sup.compile 12)) (At.tailR (A := blkInc) (At.tailR (A := [iJmp 7]) (At.tailR (A := crSetup) (At.tailR (A := (Scr.compile (18 + Sup.len))) (At.headR [Instr.halt] (([] : Program)))))))))))) ?_
    simp only [compProCode_length, blkCond_code_length, blkSetup_length, blkInc_length, crSetup_length, List.length_cons, List.length_nil, Stmt.length_compile] <;> omega
  have h0 := h 0 (by simp)
  simpa using h0

/-- **The six `At` facts** the published `upLoop_iterate` asks for. -/
theorem loop_at_B (Sup Scr : Stmt) :
    At (progUpOfProB Sup Scr) 7 blkCond.code ∧
      ((progUpOfProB Sup Scr)[8]? = some (iJz r7 (15 + Sup.len))) ∧
      At (progUpOfProB Sup Scr) 9 blkSetup ∧
      At (progUpOfProB Sup Scr) 12 (Sup.compile 12) ∧
      At (progUpOfProB Sup Scr) (12 + Sup.len) blkInc ∧
      (progUpOfProB Sup Scr)[14 + Sup.len]? = some (iJmp 7) :=
  ⟨at_testB Sup Scr, getElem?_jzB Sup Scr, at_setupB Sup Scr, at_supB Sup Scr,
    at_incB Sup Scr, getElem?_jmpB Sup Scr⟩

/-- **The prologue's run**: seven steps from `initState` reach `pc = 7` with `r1 = 1`, `r2 = l+1`,
`r3 = 2^Wd`, `r4 = compPayBase - 1`, `r0` still the coordinate, and the memory untouched.  (The
published `compPro_sem`, at the flat programme.) -/
theorem pro_sem (Sup Scr : Stmt) (E : RAMEnv) {l Wd Rpad N M : ℕ}
    {y : Fin M → ZMod 2} {i : Fin N}
    (hdet0 : E.det 0 = l + 1) (hdet1 : E.det 1 = 2 ^ Wd)
    (hdet2 : E.det 2 = compPayBase l Wd Rpad - 1)
    (hW1 : 1 < 2 ^ E.W) (h2 : 2 < 2 ^ E.W) (hl : l + 1 < 2 ^ E.W) (hWd : 2 ^ Wd < 2 ^ E.W)
    (hPB : compPayBase l Wd Rpad - 1 < 2 ^ E.W) :
    Sem (progUpOfProB Sup Scr) E 0 7 (initState (packMem E.W y) i.val 0 0)
      (fun k out => k = 7 ∧ out.pc = 7 ∧ out.mem = packMem E.W y ∧
        out.regs 0 = i.val ∧ out.regs 1 = 1 ∧ out.regs 2 = l + 1 ∧
        out.regs 3 = 2 ^ Wd ∧ out.regs 4 = compPayBase l Wd Rpad - 1) := by
  have hno : NoBranch compProCode := compProCode_noBranch
  have e0 : E.det 0 % 2 ^ E.W = l + 1 := by rw [hdet0]; exact Nat.mod_eq_of_lt hl
  have e1 : E.det 1 % 2 ^ E.W = 2 ^ Wd := by rw [hdet1]; exact Nat.mod_eq_of_lt hWd
  have e2 : E.det 2 % 2 ^ E.W = compPayBase l Wd Rpad - 1 := by
    rw [hdet2]; exact Nat.mod_eq_of_lt hPB
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW1
  have h0m : (0 : ℕ) % 2 ^ E.W = 0 := Nat.zero_mod _
  have h2m : (2 : ℕ) % 2 ^ E.W = 2 := Nat.mod_eq_of_lt h2
  refine Sem.mono (Sem.block (progUpOfProB Sup Scr) E 0 compProCode
    (initState (packMem E.W y) i.val 0 0) (at_proCodeB Sup Scr) hno (by simp [initState])) ?_
  intro k s' h
  obtain ⟨rfl, rfl⟩ := h
  have hpc : (runBlock compProCode E (initState (packMem E.W y) i.val 0 0)).pc = 7 := by
    rw [runBlock_pc _ _ _ hno]
    simp [compProCode, initState]
  have hmem : (runBlock compProCode E (initState (packMem E.W y) i.val 0 0)).mem
      = packMem E.W y := by
    simp [compProCode, runBlock_cons, runBlock_nil, execInstr, initState]
  refine ⟨rfl, hpc, hmem, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [compProCode, runBlock_cons, runBlock_nil, execInstr, initState,
      e0, e1, e2, h1m, h0m, h2m]

/-! ## E. The composite linear map -/

/-- The composite column map: block `s` gets `H_s x`, the `CR` block gets `Hcr x`. -/
def compH {l N : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin l → ℕ) (R : ℕ)
    (Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2))
    (Hcr : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2)) :
    (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (W * blkTotal W f + R) → ZMod 2) where
  toFun x := compAsm W hW f R (fun s => Hs s x) (Hcr x)
  map_add' x y := by
    have hv : (fun s : Fin l => Hs s (x + y)) = (fun s => Hs s x) + (fun s => Hs s y) := by
      funext s
      exact map_add (Hs s) x y
    rw [hv, Hcr.map_add, compAsm_add]
  map_smul' c x := by
    have hv : (fun s : Fin l => Hs s (c • x)) = c • (fun s => Hs s x) := by
      funext s
      exact map_smul (Hs s) c x
    rw [hv, Hcr.map_smul]
    exact compAsm_smul W hW f R c (fun s => Hs s x) (Hcr x)

@[simp] theorem compH_apply {l N : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin l → ℕ) (R : ℕ)
    (Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2))
    (Hcr : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2)) (x : Fin N → ZMod 2) :
    compH W hW f R Hs Hcr x = compAsm W hW f R (fun s => Hs s x) (Hcr x) := rfl

/-- packMem_add_compAsm_cr, spelled with y + compAsm (the form the composite payload has). -/
theorem packMem_add_compAsm_cr_add {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (t : Fin L) → Fin (f t) → ZMod 2) (u : Fin R → ZMod 2)
    (y : Fin (W * blkTotal W f + R) → ZMod 2) {q : ℕ} (hq : q < wordsOf W R) :
    packMem W (y + compAsm W hW f R v u) (blkTotal W f + q)
      = packMem W (fun p : Fin R => y ⟨W * blkTotal W f + p.val, by
          have := p.isLt; omega⟩ + u p) q :=
  packMem_add_compAsm_cr W hW f R v u y hq



/-! ## 2. The `l`-block loop at the pinned width

`Top65Up.upBody_step`/`upLoop_iterate` are copied verbatim below; the **only** change is that `hUp`
is `UpChildSemC Sup E Tu (2 ^ Wd) f Hs` and the per-block payload fit
`blkOff E.W f p + wordsOf E.W (f p) ≤ 2^E.W` is supplied by the caller.  The `∀ Bw` form of
`UpChildSem` is unusable: it cannot be fed from a pinned-width contract.  (At the assembly level
that fit is *derived* from the single fit `hbtfit`, via `blkOff_succ`/`blkOff_total`.) -/


set_option maxHeartbeats 1600000 in
/-- **One dispatch.**  From the loop body's entry (program counter `9`, `r1 = j+1`), the fixed setup,
one copy of `Sup` and the increment return to the loop head (`7`) with `r1 = j+2` and the payload
invariant advanced from `upPart w j` to `upPart w (j+1)`. -/
theorem upBody_step_at (P : Program) (Sup : Stmt) (E : RAMEnv)
    {l N Wd Rpad Rcr : ℕ} {f : Fin l → ℕ} {w : (s : Fin l) → Fin (f s) → ZMod 2}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {dt : Fin l → ℕ → ℕ} {b : Fin l → ℕ} {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd) (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSemC Sup E Tu (2 ^ Wd) f Hs)
    (hchildfit : ∀ s : Fin l, blkOff E.W f s.val + wordsOf E.W (f s) ≤ 2 ^ E.W)
    (hdt : ∀ (s : Fin l) (a : ℕ), a < 2 ^ Wd → E.det ((s.val + 1) * 2 ^ Wd + a) = dt s a)
    (hb : ∀ s : Fin l, b s = blkOff E.W f s.val)
    (hfit2 : ∀ s : Fin l, (s.val + 2) * 2 ^ Wd ≤ 2 ^ E.W)
    (hPB : ∀ s : Fin l, compPayBase l Wd Rpad - 1 + (s.val + 1) = compPayBase l Wd Rpad + s.val)
    (hPBlt : ∀ s : Fin l, compPayBase l Wd Rpad + s.val < 2 ^ E.W)
    (hbw : ∀ s : Fin l, b s < 2 ^ E.W)
    (hpaydet : ∀ s : Fin l, E.det (compPayBase l Wd Rpad + s.val) = b s)
    (hAtSetup : At P 9 blkSetup) (hAtSup : At P 12 (Sup.compile 12))
    (hAtInc : At P (12 + Sup.len) blkInc) (hjmp : P[14 + Sup.len]? = some (iJmp 7))
    (y : Fin (E.W * blkTotal E.W f + Rcr) → ZMod 2) (i : Fin N) (j : Fin l) (s : RAMState)
    (hpc : s.pc = 9) (h0 : s.regs 0 = i.val) (h1 : s.regs 1 = j.val + 1)
    (h2 : s.regs 2 = l + 1) (h3 : s.regs 3 = 2 ^ Wd)
    (h4 : s.regs 4 = compPayBase l Wd Rpad - 1)
    (hw : w = fun (s : Fin l) => Hs s (Pi.single i 1))
    (hmem : ∀ q, s.mem q = packMem E.W (y + compAsm E.W hW f Rcr (upPart w j.val) 0) q) :
    ∃ (c : ℕ) (out : RAMState), (c : ℝ) ≤ Tu + 6 ∧ (step P E)^[c] s = out ∧
      out.pc = 7 ∧ out.regs 0 = i.val ∧ out.regs 1 = j.val + 2 ∧ out.regs 2 = l + 1 ∧
      out.regs 3 = 2 ^ Wd ∧ out.regs 4 = compPayBase l Wd Rpad - 1 ∧
      (∀ q, out.mem q = packMem E.W (y + compAsm E.W hW f Rcr (upPart w (j.val + 1)) 0) q) := by
  -- the setup, run
  have hs1pc : s.pc + 3 = 12 := by rw [hpc]
  have hreg14 : s.regs 1 * s.regs 3 % 2 ^ E.W = (j.val + 1) * 2 ^ Wd := by
    rw [h1, h3]
    exact Nat.mod_eq_of_lt (blk_fit (hfit2 j)).2
  have hreg7 : (s.regs 4 + s.regs 1) % 2 ^ E.W = compPayBase l Wd Rpad + j.val := by
    rw [h4, h1, hPB j]
    exact Nat.mod_eq_of_lt (hPBlt j)
  have hreg15 : E.det ((s.regs 4 + s.regs 1) % 2 ^ E.W) % 2 ^ E.W = b j := by
    rw [hreg7, hpaydet j]
    exact Nat.mod_eq_of_lt (hbw j)
  obtain ⟨hs2pc, hs2regs, hs2mem⟩ : (runBlock blkSetup E s).pc = 12 ∧
      (runBlock blkSetup E s).regs = Function.update (Function.update
        (Function.update s.regs r14 ((j.val + 1) * 2 ^ Wd)) r7 (compPayBase l Wd Rpad + j.val))
        r15 (b j) ∧ (runBlock blkSetup E s).mem = s.mem := by
    refine ⟨?_, ?_, ?_⟩
    · rw [setup_pc]; exact hs1pc
    · rw [setup_regs, hreg14, hreg15, hreg7]
    · rw [setup_mem]
  have hstep_setup : (step P E)^[3] s = runBlock blkSetup E s := by
    have h := iterate_runBlock_of_at P E blkSetup s (by rw [hpc]; exact hAtSetup) blkSetup_noBranch
    simpa [blkSetup] using h
  -- the register facts at the child's entry
  set s3 := runBlock blkSetup E s with hs3
  have hpc3 : s3.pc = 12 := hs2pc
  have hr14 : s3.regs 14 = (j.val + 1) * 2 ^ Wd := by
    rw [hs2regs]; simp
  have hr7 : s3.regs 7 = compPayBase l Wd Rpad + j.val := by
    rw [hs2regs]; simp
  have hr15 : s3.regs 15 = b j := by
    rw [hs2regs]; simp
  have hr0 : s3.regs 0 = i.val := by rw [hs2regs]; simp [h0]
  have hr1 : s3.regs 1 = j.val + 1 := by rw [hs2regs]; simp [h1]
  have hr2 : s3.regs 2 = l + 1 := by rw [hs2regs]; simp [h2]
  have hr3 : s3.regs 3 = 2 ^ Wd := by rw [hs2regs]; simp [h3]
  have hr4 : s3.regs 4 = compPayBase l Wd Rpad - 1 := by rw [hs2regs]; simp [h4]
  have hmem3 : s3.mem = s.mem := hs2mem
  -- the payload slice the block sees
  set ys : Fin (f j) → ZMod 2 :=
    fun k => y (blkEmb E.W hW f Rcr j k) + upPart w j.val j k with hys
  have hpay : ∀ q < wordsOf E.W (f j), s3.mem (b j + q) = packMem E.W ys q := by
    intro q hq
    rw [hmem3, hmem (b j + q), hb j]
    exact packMem_add_compAsm_blk E.W hW f hpad Rcr (upPart w j.val) 0 y j hq
  -- the per-block contract
  obtain ⟨k, s4, hk, hstep_child, hpc4, hpay4, hframe4, hr0', hr1', hr2', hr3', hr4'⟩ :=
    hUp j P 12 ((j.val + 1) * 2 ^ Wd) (b j) (by rw [hb j]; exact hchildfit j)
      (dt j) ys i s3 hAtSup hpc3
      (blk_fit (hfit2 j)).1 (hdt j) hr14 hr15 hr0 hpay
  -- the increment, run
  have hpc4' : s4.pc = 12 + Sup.len := hpc4
  have hstep_inc : (step P E)^[2] s4 = runBlock blkInc E s4 := by
    have h := iterate_runBlock_of_at P E blkInc s4 (by rw [hpc4']; exact hAtInc) blkInc_noBranch
    simpa [blkInc] using h
  set s5 := runBlock blkInc E s4 with hs5
  have hpc5 : s5.pc = 14 + Sup.len := by rw [inc_pc, hpc4']; omega
  have hmem5 : s5.mem = s4.mem := inc_mem E s4
  have hstep_jmp : (step P E)^[1] s5 = { s5 with pc := 7 } := by
    rw [Function.iterate_one, step_eq_execInstr P E s5 (iJmp 7) (by rw [hpc5]; exact hjmp),
      execInstr_jmp]
  -- glue the iterates
  have glue : ∀ (m n : ℕ) (x y z : RAMState), (step P E)^[m] x = y →
      (step P E)^[n] y = z → (step P E)^[n + m] x = z := by
    intro m n x y z h1' h2'
    rw [Function.iterate_add_apply, h1', h2']
  have e1 : (step P E)^[k + 3] s = s4 := glue 3 k s s3 s4 hstep_setup hstep_child
  have e2 : (step P E)^[2 + (k + 3)] s = s5 := glue (k + 3) 2 s s4 s5 e1 hstep_inc
  have e3 : (step P E)^[1 + (2 + (k + 3))] s = { s5 with pc := 7 } :=
    glue (2 + (k + 3)) 1 s s5 { s5 with pc := 7 } e2 hstep_jmp
  have eall : (step P E)^[k + 6] s = { s5 with pc := 7 } := by
    rwa [show 1 + (2 + (k + 3)) = k + 6 from by omega] at e3
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW1
  have hreg_out : ({ s5 with pc := 7 } : RAMState).regs
      = Function.update (Function.update s4.regs r7 (1 % 2 ^ E.W))
          r1 ((s4.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W) := by
    rw [hs5, inc_regs]
  refine ⟨k + 6, { s5 with pc := 7 }, ?_, eall, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have hkR : (k : ℝ) ≤ Tu := hk
    have hk6 : ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 := by push_cast; ring
    rw [hk6]; linarith
  · simp
  · rw [hreg_out, upd2_zero, hr0', hr0]
  · rw [hreg_out]
    have h5 : (Function.update (Function.update s4.regs r7 (1 % 2 ^ E.W))
        r1 ((s4.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W)) 1
        = (s4.regs 1 + 1 % 2 ^ E.W) % 2 ^ E.W := Function.update_self _ _ _
    rw [h5, hr1', hr1, h1m]
    rw [show j.val + 1 + 1 = j.val + 2 from by omega]
    exact Nat.mod_eq_of_lt (blk_fit_lt hWd1 (hfit2 j))
  · rw [hreg_out, upd2_two, hr2', hr2]
  · rw [hreg_out, upd2_three, hr3', hr3]
  · rw [hreg_out, upd2_four, hr4', hr4]
  · -- the payload invariant advances
    intro q
    have hmem5' : ({ s5 with pc := 7 } : RAMState).mem q = s4.mem q := by rw [hmem5]
    rw [hmem5']
    by_cases hq : b j ≤ q ∧ q < b j + wordsOf E.W (f j)
    · obtain ⟨hq1, hq2⟩ := hq
      have ha : q - b j < wordsOf E.W (f j) := by omega
      have hqe : b j + (q - b j) = q := by omega
      have hL : s4.mem q = packMem E.W (ys + Hs j (Pi.single i 1)) (q - b j) := by
        conv_lhs => rw [show q = b j + (q - b j) from by omega]
        exact hpay4 (q - b j) ha
      rw [hL]
      have hslice : (fun k : Fin (f j) => y (blkEmb E.W hW f Rcr j k)
            + upPart w (j.val + 1) j k) = ys + Hs j (Pi.single i 1) := by
        funext k
        have h1' : upPart w (j.val + 1) j k = w j k := by
          rw [upPart_apply, if_pos (by omega)]
        have h2' : upPart w j.val j k = 0 := by
          rw [upPart_apply, if_neg (by omega)]
        have h3' : w j k = Hs j (Pi.single i 1) k := by rw [hw]
        simp only [hys, Pi.add_apply, h1', h2', h3', add_zero, zero_add]
      have hstep := packMem_add_compAsm_blk E.W hW f hpad Rcr (upPart w (j.val + 1)) 0 y j ha
      rw [hslice, ← hb j, hqe] at hstep
      exact hstep.symm
    · have hout : s4.mem q = s.mem q := by
        rcases not_and_or.mp hq with h | h
        · exact hframe4 q (Or.inl (by omega))
        · exact hframe4 q (Or.inr (by omega))
      rw [hout, hmem q]
      exact (packMem_compAsmV_congr (W := E.W) (hW := hW) (f := f) (R := Rcr) (s := j)
        (v := upPart w j.val) (v' := upPart w (j.val + 1)) (u := 0) (u' := 0)
        (fun t ht => (upPart_of_ne (f := f) w (j := j.val) (s := t)
          (by intro hc; exact ht (Fin.ext hc))).symm) (fun _ => rfl) y (by
          intro hc
          exact hq ⟨by rw [hb j]; exact hc.1, by rw [hb j]; exact hc.2⟩))



set_option maxHeartbeats 1600000 in
/-- **The `l`-block stitching.**  From the loop head with `r1 = 1`, `l` iterations of the dispatch
reach the loop head again with `r1 = l+1` and the payload equal to `y` toggled by all `l` blocks. -/
theorem upLoop_iterate_at (P : Program) (Sup : Stmt) (E : RAMEnv)
    {l N Wd Rpad Rcr : ℕ} {f : Fin l → ℕ} {w : (s : Fin l) → Fin (f s) → ZMod 2}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {dt : Fin l → ℕ → ℕ} {b : Fin l → ℕ} {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd)
    (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSemC Sup E Tu (2 ^ Wd) f Hs)
    (hchildfit : ∀ s : Fin l, blkOff E.W f s.val + wordsOf E.W (f s) ≤ 2 ^ E.W)
    (hdt : ∀ (s : Fin l) (a : ℕ), a < 2 ^ Wd → E.det ((s.val + 1) * 2 ^ Wd + a) = dt s a)
    (hb : ∀ s : Fin l, b s = blkOff E.W f s.val)
    (hfit2 : ∀ s : Fin l, (s.val + 2) * 2 ^ Wd ≤ 2 ^ E.W)
    (hPB : ∀ s : Fin l, compPayBase l Wd Rpad - 1 + (s.val + 1) = compPayBase l Wd Rpad + s.val)
    (hPBlt : ∀ s : Fin l, compPayBase l Wd Rpad + s.val < 2 ^ E.W)
    (hbw : ∀ s : Fin l, b s < 2 ^ E.W)
    (hpaydet : ∀ s : Fin l, E.det (compPayBase l Wd Rpad + s.val) = b s)
    (hAtCode : At P 7 blkCond.code) (hjz : ∃ t : ℕ, P[8]? = some (iJz r7 t))
    (hAtSetup : At P 9 blkSetup) (hAtSup : At P 12 (Sup.compile 12))
    (hAtInc : At P (12 + Sup.len) blkInc) (hjmp : P[14 + Sup.len]? = some (iJmp 7))
    (y : Fin (E.W * blkTotal E.W f + Rcr) → ZMod 2) (i : Fin N)
    (hw : w = fun (s : Fin l) => Hs s (Pi.single i 1)) (s0 : RAMState)
    (hpc0 : s0.pc = 7) (h0 : s0.regs 0 = i.val) (h10 : s0.regs 1 = 1)
    (h20 : s0.regs 2 = l + 1) (h30 : s0.regs 3 = 2 ^ Wd)
    (h40 : s0.regs 4 = compPayBase l Wd Rpad - 1)
    (hmem0 : ∀ q, s0.mem q = packMem E.W y q) :
    ∀ j, j ≤ l → ∃ (c : ℕ) (out : RAMState), (c : ℝ) ≤ 8 * (j : ℝ) + (j : ℝ) * Tu ∧
      (step P E)^[c] s0 = out ∧ out.pc = 7 ∧ out.regs 0 = i.val ∧
      out.regs 1 = j + 1 ∧ out.regs 2 = l + 1 ∧ out.regs 3 = 2 ^ Wd ∧
      out.regs 4 = compPayBase l Wd Rpad - 1 ∧
      (∀ q, out.mem q = packMem E.W (y + compAsm E.W hW f Rcr (upPart w j) 0) q) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨0, s0, by simp, rfl, hpc0, h0, ?_, h20, h30, h40, ?_⟩
      · simpa using h10
      · intro q
        rw [hmem0 q, upPart_zero]
        have hz : compAsm E.W hW f Rcr (0 : (s : Fin l) → Fin (f s) → ZMod 2)
            (0 : Fin Rcr → ZMod 2) = 0 := compAsm_zero E.W hW f Rcr
        rw [hz, add_zero]
  | succ j ih =>
      intro hj
      have hj' : j < l := by omega
      obtain ⟨c, out, hc, hstep, hpc, h0, h1, h2, h3, h4, hmem⟩ := ih (by omega)
      -- the test and the `jz` fall-through
      have hlt : out.regs 1 < out.regs 2 := by rw [h1, h2]; omega
      have htest : (step P E)^[1] out = runBlock blkCond.code E out := by
        have h := iterate_runBlock_of_at P E blkCond.code out (by rw [hpc]; exact hAtCode)
          (Cond.noBranch_code _)
        simpa [blkCond, Cond.code] using h
      have hs1 : runBlock blkCond.code E out
          = { out with pc := out.pc + 1, regs := Function.update out.regs r7 1 } :=
        runBlock_test E out hlt hW1
      have hreg7 : (runBlock blkCond.code E out).regs r7 = 1 := by rw [hs1]; simp
      have hpc8 : (runBlock blkCond.code E out).pc = 8 := by rw [hs1]; simp [hpc]
      obtain ⟨tz, hjzt⟩ := hjz
      have hjz8 : P[(runBlock blkCond.code E out).pc]? = some (iJz r7 tz) := by
        rw [hpc8]; exact hjzt
      have hstep_jz : (step P E)^[1] (runBlock blkCond.code E out)
          = { runBlock blkCond.code E out with pc := 9 } := by
        rw [Function.iterate_one,
          step_eq_execInstr P E _ (iJz r7 tz) hjz8, execInstr_jz]
        rw [hreg7]
        simp [hpc8]
      -- the body
      obtain ⟨k, out', hk, hstep_body, hpc', h0', h1', h2', h3', h4', hmem'⟩ :=
        upBody_step_at P Sup E (l := l) (N := N) (Wd := Wd) (Rpad := Rpad) (Rcr := Rcr)
          (f := f) (w := w) (Hs := Hs) (dt := dt) (b := b) (Tu := Tu)
          hTu hW hW1 hWd1 hpad hUp hchildfit hdt hb hfit2 hPB hPBlt hbw hpaydet
          hAtSetup hAtSup hAtInc hjmp y i ⟨j, hj'⟩
          { runBlock blkCond.code E out with pc := 9 } rfl
          (by rw [hs1]; simp [h0])
          (by rw [hs1]; simp [h1])
          (by rw [hs1]; simp [h2])
          (by rw [hs1]; simp [h3])
          (by rw [hs1]; simp [h4])
          hw
          (by intro q
              show (runBlock blkCond.code E out).mem q = _
              rw [show (runBlock blkCond.code E out).mem = out.mem from by rw [hs1]]
              exact hmem q)
      -- glue the pieces: test+jz (2 steps), then the body (`k` steps)
      have g1 : (step P E)^[1 + 1] out
          = { runBlock blkCond.code E out with pc := 9 } := by
        rw [Function.iterate_add_apply, htest, hstep_jz]
      have g2 : (step P E)^[k + 2] out = out' :=
        step_glue P E 2 k out { runBlock blkCond.code E out with pc := 9 } out'
          (by simpa using g1) hstep_body
      have gall : (step P E)^[(k + 2) + c] s0 = out' :=
        step_glue P E c (k + 2) s0 out out' hstep g2
      have hcost : ((c + (k + 2) : ℕ) : ℝ) ≤ 8 * ((j + 1 : ℕ) : ℝ)
          + ((j + 1 : ℕ) : ℝ) * Tu := by
        have hkR : (k : ℝ) ≤ Tu + 6 := hk
        have hcj : (c : ℝ) ≤ 8 * (j : ℝ) + (j : ℝ) * Tu := hc
        have hck : ((c + (k + 2) : ℕ) : ℝ) = (c : ℝ) + ((k : ℝ) + 2) := by
          push_cast; ring
        have hj1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hck, hj1]
        have h1 : (k : ℝ) + 2 ≤ Tu + 8 := by linarith
        have h2 : (c : ℝ) + ((k : ℝ) + 2) ≤
            (8 * (j : ℝ) + (j : ℝ) * Tu) + (Tu + 8) := by linarith
        calc (c : ℝ) + ((k : ℝ) + 2)
            ≤ (8 * (j : ℝ) + (j : ℝ) * Tu) + (Tu + 8) := h2
          _ = 8 * ((j : ℝ) + 1) + ((j : ℝ) + 1) * Tu := by ring
      refine ⟨c + (k + 2), out', hcost, ?_, hpc', h0', ?_, h2', h3', h4', hmem'⟩
      · rw [show c + (k + 2) = (k + 2) + c from by omega]
        exact gall
      · show out'.regs 1 = j + 1 + 1
        rw [h1']


/-! ## 3. The assembly, with `hCr` discharged -/


/-- The payload slice the `CR` block sees: the composite's `CR` coordinates. -/
def crSlice {R : ℕ} (T : ℕ) (y : Fin (T + R) → ZMod 2) : Fin R → ZMod 2 :=
  fun p => y ⟨T + p.val, by have := p.isLt; omega⟩


set_option maxHeartbeats 1600000 in
/-- **The assembly.**  From the per-block contract `hUp` and the `CR` contract `hCr`, the composite
programme toggles the composite column into the packed payload, in `7 + (8l + l·Tu) + 2 + 3 + (65536 * lg ((N : ℝ) + 2) ^ 2)`
steps. -/
theorem conj6_assembly_CR
    (Sup : Stmt) (E : RAMEnv) {l N t Wd Rpad : ℕ} {f : Fin l → ℕ}
    {dt : Fin l → ℕ → ℕ}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {C : Fin N → Fin (cr23D N) → Fin (cr23M t)}
    {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd) (hWd2 : 2 ≤ Wd)
    (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSemC Sup E Tu (2 ^ Wd) f Hs)
    (hE : E.det = compUpDetB Wd Rpad dt (cr23DecDetAt N t C (blkTotal E.W f))
      (fun s => blkOff E.W f s.val) (blkTotal E.W f))
    (hN : 1 ≤ N) (htN : t ≤ N) (hEW : E.W = cr23Word N) (hBw : cr23Graph0 N ≤ Rpad)
    (hWdW : 2 ^ Wd < 2 ^ E.W) (hlW : l + 1 < 2 ^ E.W)
    (hRpad : 0 < Rpad) (hRfit : Rpad ≤ 2 ^ Wd) (hpayfit : Rpad + l ≤ 2 ^ Wd)
    (hlWd : (l + 1) * 2 ^ Wd < 2 ^ E.W)
    (hcrfit : (l + 1) * 2 ^ Wd + Rpad ≤ 2 ^ E.W)
    (hpaylt : compPayBase l Wd Rpad + l ≤ 2 ^ E.W)
    (hbtlt : blkTotal E.W f < 2 ^ E.W)
    (hbtfit : blkTotal E.W f + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W)
    (y : Fin (E.W * blkTotal E.W f + (cr23R N t)) → ZMod 2) (i : Fin N) :
    ∃ s' : RAMState,
      HaltsWithin (progUpOfProB Sup cr23UpStmtAt) E
        (7 + (8 * (l : ℝ) + (l : ℝ) * Tu) + 2 + 3 + (65536 * lg ((N : ℝ) + 2) ^ 2))
        (initState (packMem E.W y) i.val 0 0) s' ∧
      (∀ addr < wordsOf E.W (E.W * blkTotal E.W f + (cr23R N t)),
        s'.mem addr
          = packMem E.W (y + compH E.W hW f (cr23R N t) Hs (cr23Sketch N t C) (Pi.single i 1)) addr) := by
  -- ### the `det` cells
  have h2Wd : 2 ≤ 2 ^ Wd := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) hWd1
  have h4Wd : 4 ≤ 2 ^ Wd := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) hWd2
  have hPB0 : 0 < compPayBase l Wd Rpad := by unfold compPayBase; omega
  have hdet0 : E.det 0 = l + 1 := by
    rw [hE]; exact compUpDetB_zero dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ (Nat.two_pow_pos Wd)
  have hdet1 : E.det 1 = 2 ^ Wd := by
    rw [hE]; exact compUpDetB_one dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ (by omega)
  have hdet2 : E.det 2 = compPayBase l Wd Rpad - 1 := by
    rw [hE]; exact compUpDetB_two dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ (by omega)
  have hdet3 : E.det 3 = blkTotal E.W f := by
    rw [hE]; exact compUpDetB_three dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ (by omega)
  have hW3 : 3 < 2 ^ E.W := by
    have h4 : 4 ≤ 2 ^ Wd := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) hWd2
    omega
  have hPBlt : compPayBase l Wd Rpad - 1 < 2 ^ E.W := by
    have h1 : compPayBase l Wd Rpad - 1 < compPayBase l Wd Rpad + l := by omega
    exact lt_of_lt_of_le h1 hpaylt
  -- ### the prologue
  obtain ⟨-, k0, s1, hstep1, -, hQ1⟩ :=
    pro_sem (Sup := Sup) (Scr := cr23UpStmtAt) (E := E) (y := y) (i := i)
      hdet0 hdet1 hdet2 hW1 (by omega) hlW hWdW hPBlt
  obtain ⟨hk0, hpc1, hmem1, h01, h11, h21, h31, h41⟩ := hQ1
  -- (k0 is still needed for the gluing below)
  -- ### the `det` facts the loop needs
  have hdtup : ∀ (s : Fin l) (a : ℕ), a < 2 ^ Wd →
      E.det ((s.val + 1) * 2 ^ Wd + a) = dt s a := by
    intro s a ha
    rw [hE]; exact compUpDetB_child dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ s ha
  have hpaydet : ∀ s : Fin l, E.det (compPayBase l Wd Rpad + s.val) = blkOff E.W f s.val := by
    intro s
    have h1 : compPayBase l Wd Rpad + s.val = compPayBase l Wd Rpad - 1 + (s.val + 1) := by omega
    rw [h1, hE]
    exact compUpDetB_pay dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ s hRpad (by have := s.isLt; omega)
  have hfit2 : ∀ s : Fin l, (s.val + 2) * 2 ^ Wd ≤ 2 ^ E.W := by
    intro s
    have h1 : s.val + 2 ≤ l + 1 := by have := s.isLt; omega
    have h2 : (s.val + 2) * 2 ^ Wd ≤ (l + 1) * 2 ^ Wd := Nat.mul_le_mul_right (2 ^ Wd) h1
    exact le_of_lt (lt_of_le_of_lt h2 hlWd)
  have hPBlt' : ∀ s : Fin l, compPayBase l Wd Rpad + s.val < 2 ^ E.W := by
    intro s
    have h1 : compPayBase l Wd Rpad + s.val < compPayBase l Wd Rpad + l := by
      have := s.isLt; omega
    exact lt_of_lt_of_le h1 hpaylt
  have hbw : ∀ s : Fin l, blkOff E.W f s.val < 2 ^ E.W := by
    intro s
    have h1 : blkOff E.W f s.val ≤ blkTotal E.W f := by
      rw [← blkOff_total f (le_refl l)]
      exact blkOff_mono f (by have := s.isLt; omega)
    exact lt_of_le_of_lt h1 hbtlt
  -- ### the published `l`-block loop
  obtain ⟨hAtCode, -, hAtSetup, hAtSup, hAtInc, hjmp⟩ := loop_at_B Sup cr23UpStmtAt
  obtain ⟨-, hjz, -, -, -, -⟩ := loop_at_B Sup cr23UpStmtAt
  have hPBcon : ∀ s : Fin l, compPayBase l Wd Rpad - 1 + (s.val + 1)
      = compPayBase l Wd Rpad + s.val := by
    intro s
    omega
  -- ### the per-block payload fits, derived from the single fit `hbtfit`
  have hchildfit : ∀ s : Fin l, blkOff E.W f s.val + wordsOf E.W (f s) ≤ 2 ^ E.W := by
    intro s
    rw [← blkOff_succ f s]
    have h1 : blkOff E.W f (s.val + 1) ≤ blkTotal E.W f := by
      rw [← blkOff_total f (le_refl l)]
      exact blkOff_mono f (by have := s.isLt; omega)
    omega
  obtain ⟨c, s2, hc, hstep2, hpc2, h02, h12, h22, h32, h42, hmem2raw⟩ :=
    upLoop_iterate_at (progUpOfProB Sup cr23UpStmtAt) Sup E hTu hW hW1 hWd1 hpad hUp
      hchildfit hdtup
      (fun _ => rfl) hfit2 hPBcon hPBlt' hbw hpaydet
      hAtCode ⟨15 + Sup.len, hjz⟩ hAtSetup hAtSup hAtInc hjmp y i rfl s1
      hpc1 h01 (by simpa using h11) h21 h31 h41 (fun q => by rw [hmem1]) l (le_refl l)
  have hmem2 : ∀ q, s2.mem q
      = packMem E.W (y + compAsm E.W hW f (cr23R N t) (fun s => Hs s (Pi.single i 1)) 0) q := by
    intro q
    rw [hmem2raw q, upPart_top]
  -- ### the loop's failing test and `jz`
  have hlt1 : ¬ (s2.regs 1 < s2.regs 2) := by rw [h12, h22]; omega
  have htest : (step (progUpOfProB Sup cr23UpStmtAt) E)^[1] s2
      = runBlock blkCond.code E s2 := by
    have h := iterate_runBlock_of_at (progUpOfProB Sup cr23UpStmtAt) E blkCond.code s2
      (by rw [hpc2]; exact hAtCode) (Cond.noBranch_code _)
    simpa [blkCond, Cond.code] using h
  have hs1 : runBlock blkCond.code E s2
      = { s2 with pc := 8, regs := Function.update s2.regs r7 0 } := by
    rw [show blkCond.code = [iLt r7 r1 r2] from rfl, runBlock_cons, runBlock_nil, execInstr_lt,
      hpc2, if_neg hlt1, Nat.zero_mod]
  have hreg7 : (Function.update s2.regs r7 0) r7 = 0 := Function.update_self ..
  have hstep_a : (step (progUpOfProB Sup cr23UpStmtAt) E)^[1] s2
      = { s2 with pc := 8, regs := Function.update s2.regs r7 0 } := by
    rw [htest, hs1]
  have hstep_b : (step (progUpOfProB Sup cr23UpStmtAt) E)^[1]
      { s2 with pc := 8, regs := Function.update s2.regs r7 0 }
      = { s2 with pc := 15 + Sup.len, regs := Function.update s2.regs r7 0 } := by
    have h8 : ({ s2 with pc := 8, regs := Function.update s2.regs r7 0 } : RAMState).pc = 8 := rfl
    have h9 : ({ s2 with pc := 8, regs := Function.update s2.regs r7 0 } : RAMState).regs r7 = 0 := by
      simpa using hreg7
    have hAt8 : (progUpOfProB Sup cr23UpStmtAt)[
        ({ s2 with pc := 8, regs := Function.update s2.regs r7 0 } : RAMState).pc]?
        = some (iJz r7 (15 + Sup.len)) := by rw [h8]; exact hjz
    rw [Function.iterate_one,
      step_eq_execInstr (progUpOfProB Sup cr23UpStmtAt) E _ (iJz r7 (15 + Sup.len)) hAt8,
      execInstr_jz, h9]
    simp
  set s3 : RAMState := { s2 with pc := 15 + Sup.len, regs := Function.update s2.regs r7 0 } with hs3
  have hstep_exit : (step (progUpOfProB Sup cr23UpStmtAt) E)^[2] s2 = s3 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, hstep_a]
    simpa [hs3] using hstep_b
  -- ### `crSetup`
  have hs3pc : s3.pc = 15 + Sup.len := by rw [hs3]
  have hstep_setup : (step (progUpOfProB Sup cr23UpStmtAt) E)^[3] s3
      = runBlock crSetup E s3 := by
    have h := iterate_runBlock_of_at (progUpOfProB Sup cr23UpStmtAt) E crSetup s3
      (by rw [hs3pc]; exact at_crSetupB Sup cr23UpStmtAt) crSetup_noBranch
    simpa using h
  set s4 : RAMState := runBlock crSetup E s3 with hs4
  have hs3mem : s3.mem = s2.mem := rfl
  have hs3one : s3.regs 1 = s2.regs 1 := by
    have h : (Function.update s2.regs r7 0) 1 = s2.regs 1 := by
      rw [Function.update_apply]; simp
    rw [hs3]; exact h
  have hs3three : s3.regs 3 = s2.regs 3 := by
    have h : (Function.update s2.regs r7 0) 3 = s2.regs 3 := by
      rw [Function.update_apply]; simp
    rw [hs3]; exact h
  have hs3zero : s3.regs 0 = s2.regs 0 := by
    have h : (Function.update s2.regs r7 0) 0 = s2.regs 0 := by
      rw [Function.update_apply]; simp
    rw [hs3]; exact h
  have hs4mem : s4.mem = s2.mem := by
    rw [hs4, crSetup_mem, hs3mem]
  have hs4pc : s4.pc = 18 + Sup.len := by
    rw [hs4, crSetup_pc, hs3pc]; omega
  have hr14 : s4.regs 14 = (l + 1) * 2 ^ Wd := by
    rw [hs4, crSetup_regs_fourteen, hs3one, hs3three, h12, h32]
    exact Nat.mod_eq_of_lt hlWd
  have hr15 : s4.regs 15 = blkTotal E.W f := by
    rw [hs4, crSetup_regs_fifteen, Nat.mod_eq_of_lt hW3, hdet3]
    exact Nat.mod_eq_of_lt hbtlt
  have hr0 : s4.regs 0 = i.val := by
    have h0 : (runBlock crSetup E s3).regs 0 = s3.regs 0 :=
      crSetup_regs_of_ne E s3 (by decide) (by decide) (by decide)
    rw [hs4, h0, hs3zero, h02]
  -- ### the `CR` block
  have hdtcr : ∀ a < Rpad, E.det ((l + 1) * 2 ^ Wd + a) = (cr23DecDetAt N t C (blkTotal E.W f)) a := by
    intro a ha
    rw [hE]; exact compUpDetB_cr dt (cr23DecDetAt N t C (blkTotal E.W f)) _ _ ha hRfit
  have hpayCR : ∀ q < wordsOf E.W (cr23R N t), s4.mem (blkTotal E.W f + q)
      = packMem E.W (crSlice (E.W * blkTotal E.W f) y) q := by
    intro q hq
    rw [hs4mem, hs3mem, hmem2 (blkTotal E.W f + q),
      packMem_add_compAsm_cr_add E.W hW f (cr23R N t) (fun s => Hs s (Pi.single i 1))
        (0 : Fin (cr23R N t) → ZMod 2) y hq]
    congr 1
    funext p
    simp only [crSlice, Pi.zero_apply, add_zero]

  have hCr := crSemAtW_cr_block N t hN htN C E hEW Rpad hBw
  obtain ⟨kcr, s5, hkcr, hstepCR, hpc5, hpay5, hframe5⟩ :=
    hCr (progUpOfProB Sup cr23UpStmtAt) (18 + Sup.len) ((l + 1) * 2 ^ Wd)
      (blkTotal E.W f) hbtfit (crSlice (E.W * blkTotal E.W f) y) i s4
      (at_crB Sup cr23UpStmtAt) hs4pc hcrfit hdtcr hr14 hr15 hr0 hpayCR
  -- ### glue the five runs
  have g1 : (step (progUpOfProB Sup cr23UpStmtAt) E)^[kcr + 3] s3 = s5 :=
    step_glue (progUpOfProB Sup cr23UpStmtAt) E 3 kcr s3 s4 s5 hstep_setup hstepCR
  have g2 : (step (progUpOfProB Sup cr23UpStmtAt) E)^[(kcr + 3) + 2] s2 = s5 :=
    step_glue (progUpOfProB Sup cr23UpStmtAt) E 2 (kcr + 3) s2 s3 s5 hstep_exit g1
  have g3 : (step (progUpOfProB Sup cr23UpStmtAt) E)^[((kcr + 3) + 2) + c] s1 = s5 :=
    step_glue (progUpOfProB Sup cr23UpStmtAt) E c ((kcr + 3) + 2) s1 s2 s5 hstep2 g2
  have g4 : (step (progUpOfProB Sup cr23UpStmtAt) E)^[(((kcr + 3) + 2) + c) + k0]
      (initState (packMem E.W y) i.val 0 0) = s5 :=
    step_glue (progUpOfProB Sup cr23UpStmtAt) E k0 (((kcr + 3) + 2) + c)
      (initState (packMem E.W y) i.val 0 0) s1 s5 hstep1 g3
  have hhalt : Halted (progUpOfProB Sup cr23UpStmtAt) s5 := by
    have hpc : s5.pc = 18 + Sup.len + cr23UpStmtAt.len := by rw [hpc5]
    simp only [Halted, hpc, progUpOfProB_halt]
  refine ⟨s5, ⟨(((kcr + 3) + 2) + c) + k0, ?_, g4, hhalt⟩, ?_⟩
  · -- the cost
    have hcR : (c : ℝ) ≤ 8 * (l : ℝ) + (l : ℝ) * Tu := hc
    have hkcrR : (kcr : ℝ) ≤ (65536 * lg ((N : ℝ) + 2) ^ 2) := hkcr
    have hk0R : (k0 : ℝ) = 7 := by exact_mod_cast hk0
    have hcast : (((((kcr + 3) + 2) + c) + k0 : ℕ) : ℝ)
        = (k0 : ℝ) + 5 + ((kcr : ℝ) + (c : ℝ)) := by
      push_cast
      ring
    rw [hcast, hk0R]
    nlinarith [hcR, hkcrR]
  · -- the payload
    intro addr haddr
    have hM : wordsOf E.W (E.W * blkTotal E.W f + (cr23R N t))
        = blkTotal E.W f + wordsOf E.W (cr23R N t) := wordsOf_mul_add E.W (blkTotal E.W f) (cr23R N t) hW
    rw [hM] at haddr
    have hcw : compH E.W hW f (cr23R N t) Hs (cr23Sketch N t C) (Pi.single i 1)
        = compAsm E.W hW f (cr23R N t) (fun s => Hs s (Pi.single i 1)) ((cr23Sketch N t C) (Pi.single i 1)) := rfl
    by_cases hlt : addr < blkTotal E.W f
    · rw [hframe5 addr (Or.inl hlt), hs4mem, hs3mem, hmem2 addr, hcw]
      exact (packMem_compAsmV_congr_v (W := E.W) (hW := hW) (f := f) (R := (cr23R N t))
        (v := fun s => Hs s (Pi.single i 1)) (u := (cr23Sketch N t C) (Pi.single i 1))
        (u' := 0) rfl y hlt).symm
    · have hq : addr - blkTotal E.W f < wordsOf E.W (cr23R N t) := by omega
      have he : addr = blkTotal E.W f + (addr - blkTotal E.W f) := by omega
      rw [he, hcw,
        packMem_add_compAsm_cr_add E.W hW f (cr23R N t) (fun s => Hs s (Pi.single i 1))
          ((cr23Sketch N t C) (Pi.single i 1)) y hq,
        hpay5 (addr - blkTotal E.W f) hq]
      rfl

/-! ## 4. What is assumed, and why the `CR` side is not

* **`hCr` is discharged, not assumed.**  `crSemAtW_cr_block` is 2.3's published export
  `cr23UpStmtAt_crSemAtW` in the exact shape the assembly consumes, and `crSemAtW_inhabited` is the
  same contract *proved* at a concrete environment, so `CrSemAtW` is an inhabited predicate.  The
  only arithmetic input is `hBw : cr23Graph0 N ≤ Rpad` (the block width must cover 2.3's graph) ---
  no word fit is needed for the `CR` side beyond the payload fit `hbtfit` that the composite's own
  payload needs.
* **Its `det` premise is met by construction.**  With
  `E.det = compUpDetB Wd Rpad dt (cr23DecDetAt N t C (blkTotal E.W f)) (fun s => blkOff E.W f s.val)
  (blkTotal E.W f)` --- the assembly's `hE` --- the `CR` window reads exactly 2.3's rebased table:
  `compUpDetB_cr` (section 1) gives `∀ a < Rpad, E.det ((l+1)*2^Wd + a) = cr23DecDetAt N t C
  (blkTotal E.W f) a`, which is the `hdet` premise of `CrSemAtW`.
* **`hUp` is the only remaining per-block assumption**, and it is Theorem 5.1's obligation, in the
  pinned-width shape `UpChildSemC Sup E Tu (2 ^ Wd) f Hs` (`upChildSemC_iff` spells it out).  The
  old `UpChildSem` cannot be fed to the loop: it quantifies `Bw` universally, so a contract at a
  *pinned* `2 ^ Wd` does not imply it.
* The other hypotheses are a **single** payload fit `hbtfit : blkTotal E.W f + wordsOf E.W (cr23R N t)
  ≤ 2 ^ E.W` (ours to choose; the per-block fits are derived from it in the proof, through
  `blkOff_succ`/`blkOff_total`/`blkOff_mono`) and the layout bounds `2 ^ Wd < 2 ^ E.W`,
  `l + 1 < 2 ^ E.W`, `(l + 1) * 2 ^ Wd < 2 ^ E.W`,
  `(l + 1) * 2 ^ Wd + Rpad ≤ 2 ^ E.W`, `compPayBase l Wd Rpad + l ≤ 2 ^ E.W`,
  `blkTotal E.W f < 2 ^ E.W`, which say that the composite `det` and the payload live below
  `2 ^ E.W`.
-/

/-! ## 5. The fit is not vacuous

`hbtfit` is the only arithmetic hypothesis about the payload.  It is satisfiable at the canonical
parameters: at `N = t = 1` the `CR` payload occupies `wordsOf 2048 (cr23R 1 1) = 2^68` words, far
below `2^2048 = 2 ^ cr23Word 1`; at `l = 0` it is the *only* fit (`blkTotal = 0`). -/

/-- `wordsOf (cr23Word 1) (cr23R 1 1) = 2 ^ 68` --- a concrete value, by evaluation. -/
theorem wordsOf_cr23R_one : wordsOf (cr23Word 1) (cr23R 1 1) = 2 ^ 68 := by decide

/-- The payload fit `hbtfit` holds at `N = t = 1`, `W = cr23Word 1 = 2048`: `2^68 ≤ 2^2048`. -/
theorem hbtfit_satisfiable : wordsOf (cr23Word 1) (cr23R 1 1) ≤ 2 ^ cr23Word 1 := by
  have hw : cr23Word 1 = 2048 := by decide
  rw [wordsOf_cr23R_one, hw]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num : 68 ≤ 2048)

end

end LinearSetReconciliation327.Main


