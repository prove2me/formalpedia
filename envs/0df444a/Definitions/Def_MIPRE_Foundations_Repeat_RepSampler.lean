-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
-- name    : MIPRE_Foundations_Repeat_RepSampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T15:39:54.466396+00:00
-- url     : https://prove2.me/theorems/62976784-c55d-4ea0-a623-42b54841f4d5
-- title:
--   Definitions of RepSampler: The repeated sampler The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `CL.Sampler`: on an…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.RepSampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The repeated sampler. The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `CL.Sampler`: on an `ℓ`-level sampler `S` with dimension `s(n)` and parameters `(λ, τ)`, the sampler of dimension `k(n) s(n)`, `k(n) = 2^{τ(|λ| + |n|)}` (`MIPRE.Repetition.reps`), whose CL functions are the `k(n)`-fold direct sums `CLFun.famSum` of those of `S`, and whose program is the fixed core `Prog.repSampCore` of `MIPRE.Foundations.Repeat.Sampler`, run through the self-interpreter `selfUniversal` and the s-m-n construction `hardcode` on `(S.prog, λ, τ)` (`planning/repetition-verifier.md`,…
--
--   **Definitions** (5): `MIPRE.Repeat.anyCost` (The cost of the core on a query of size `D` at index `n`, with the dimension query answered in time `td` and each block query in time `Tu`:…); `MIPRE.Repeat.blockQueries` (The block queries the core asks `S̄` on the query datum `d`, at dimension `s`: for a query `(kind, w, j, u, y)` of nonzero kind and `s >…); `MIPRE.Repeat.repSampler` (**The repeated sampler** (`ComputeParrepVerifier`, sampler half): `k(n)` independent copies of `S`, `k(n) = 2^{τ(|λ| + |n|)}`.); `MIPRE.Repeat.repSamplerProg` (The program of the repeated sampler on `(S̄, λ, τ)`: the core, hardcoded.); `MIPRE.Repeat.zBound` (A bound on the sizes in the block loop of the core on a query of size `D`.).
--
--   **Embedded lemmas** (27): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `block_call`, `chunk_toBits_truncate`, `dimProg_runs_encode`, `dim_call`, `encode_factor`, `encode_linear`, `encode_marginal`, `encode_nat_one`, `encode_nat_three`, `encode_nat_two`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.RepSampler` (`MIPRE/Foundations/Repeat/RepSampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 36 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/RepSampler.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/RepSampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_CL_CLFun_eval_truncate_famSum
import Theorems.Thm_MIPRE_CL_CLFun_exactlyOn_famSum
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_famSum
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_famSum
import Theorems.Thm_MIPRE_CL_block_ofBits
import Theorems.Thm_MIPRE_CL_chunk_flatten_ofFn
import Theorems.Thm_MIPRE_CL_chunk_map
import Theorems.Thm_MIPRE_CL_indicatorBits_blockSet
import Theorems.Thm_MIPRE_CL_length_chunk
import Theorems.Thm_MIPRE_CL_length_flatten_ofFn
import Theorems.Thm_MIPRE_CL_toBits_join
import Theorems.Thm_MIPRE_Cost_Data_chunkPairs_eq_ofFn
import Theorems.Thm_MIPRE_Cost_Data_encode_nat_eq_list
import Theorems.Thm_MIPRE_Cost_Data_length_le_size_list_prime
import Theorems.Thm_MIPRE_Cost_Data_replicate_nil_eq_map
import Theorems.Thm_MIPRE_Cost_Data_toList_encode_bitStr
import Theorems.Thm_MIPRE_Cost_Prog_coreDispatch_dim
import Theorems.Thm_MIPRE_Cost_Prog_coreDispatch_lock
import Theorems.Thm_MIPRE_Cost_Prog_coreDispatch_nil
import Theorems.Thm_MIPRE_Cost_Prog_dimProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_dimProg_runs_nil
import Theorems.Thm_MIPRE_Cost_Prog_lockProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_lockProg_runs_zero
import Theorems.Thm_MIPRE_Cost_Prog_repSampCore_prefix
import Theorems.Thm_MIPRE_Cost_Prog_repSampCore_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
import Theorems.Thm_Nat_bits_two_pow_mul

/-!
# The repeated sampler

The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `CL.Sampler`: on an
`ℓ`-level sampler `S` with dimension `s(n)` and parameters `(λ, τ)`, the sampler of dimension
`k(n) s(n)`, `k(n) = 2^{τ(|λ| + |n|)}` (`MIPRE.Repetition.reps`), whose CL functions are the
`k(n)`-fold direct sums `CLFun.famSum` of those of `S`, and whose program is the fixed core
`Prog.repSampCore` of `MIPRE.Foundations.Repeat.Sampler`, run through the self-interpreter
`selfUniversal` and the s-m-n construction `hardcode` on `(S.prog, λ, τ)`
(`planning/repetition-verifier.md`, R3(b)).

The correctness clauses reduce to those of `S` on the blocks of the query (`Bits.lean`), the
halting clause to the case analysis `repSampCore_runs_any` on the shape of the query, which
also carries the explicit cost used by the time bound (`MIPRE.Foundations.Repeat.SamplerCost`).
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-- A finite list of halting runs halts within a common bound. -/
theorem exists_uniform_bound {α : Type*} (L : List α) (Q : α → ℕ → Prop)
    (h : ∀ a ∈ L, ∃ t, Q a t) : ∃ T, ∀ a ∈ L, ∃ t ≤ T, Q a t := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨T, hT⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨t, ht⟩ := h a (List.mem_cons_self ..)
    refine ⟨max t T, fun b hb => ?_⟩
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨t, le_max_left _ _, ht⟩
    · obtain ⟨t', ht', hq⟩ := hT b hb
      exact ⟨t', ht'.trans (le_max_right _ _), hq⟩

/-! ## Halting on every query -/

/-- The block queries the core asks `S̄` on the query datum `d`, at dimension `s`: for a query
`(kind, w, j, u, y)` of nonzero kind and `s > 0`, the queries `(kind, w, j, blockU, blockY)` on
the pairs of blocks; none otherwise. -/
def blockQueries (s : ℕ) : Data → List Data
  | .cons (.cons k₀ k₁) (.cons wD (.cons jD (.cons uD yD))) =>
    if hs : 0 < s then
      (chunkPairs s hs (toList uD) (toList yD)).map fun p =>
        .cons (.cons k₀ k₁) (.cons wD (.cons jD (.cons (list p.1) (list p.2))))
    else []
  | _ => []

theorem lockProg_runs_malformed (univ : Prog) (sD nD sz kD qr : Data)
    (h : qr = .nil ∨ (∃ wD, qr = .cons wD .nil) ∨ ∃ wD jD, qr = .cons wD (.cons jD .nil)) :
    ∃ t ≤ 8, Eval [Data.cons sD (.cons nD (.cons sz (.cons kD qr)))] (lockProg univ) .nil t := by
  rcases h with rfl | ⟨wD, rfl⟩ | ⟨wD, jD, rfl⟩
  · exact ⟨6, by omega, Eval.elim_cons (i := 0) (n := .nil) (a := sD)
      (b := .cons nD (.cons sz (.cons kD .nil))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD) (b := .cons sz (.cons kD .nil)) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := sz) (b := .cons kD .nil) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .nil) (by simp)
            (Eval.elim_nil (i := 1) (by simp) (Eval.nil _)))))⟩
  · exact ⟨7, by omega, Eval.elim_cons (i := 0) (n := .nil) (a := sD)
      (b := .cons nD (.cons sz (.cons kD (.cons wD .nil)))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD) (b := .cons sz (.cons kD (.cons wD .nil)))
        (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := sz) (b := .cons kD (.cons wD .nil)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .cons wD .nil) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := .nil) (by simp)
              (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))))))⟩
  · exact ⟨8, by omega, Eval.elim_cons (i := 0) (n := .nil) (a := sD)
      (b := .cons nD (.cons sz (.cons kD (.cons wD (.cons jD .nil))))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
        (b := .cons sz (.cons kD (.cons wD (.cons jD .nil)))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := sz) (b := .cons kD (.cons wD (.cons jD .nil)))
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .cons wD (.cons jD .nil)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := .cons jD .nil) (by simp)
              (Eval.elim_cons (i := 1) (n := .nil) (a := jD) (b := .nil) (by simp)
                (Eval.elim_nil (i := 1) (by simp) (Eval.nil _)))))))⟩

theorem lockCost_mono {s C C' U U' Y Y' Z : ℕ} (hC : C ≤ C') (hU : U ≤ U') (hY : Y ≤ Y') :
    lockCost s C U Y Z ≤ lockCost s C' U' Y' Z := by
  unfold lockCost
  have := Nat.mul_le_mul_right (mapIter Z) (Nat.add_le_add_right hU 1)
  omega

theorem encode_nat_zero : (encode (0 : ℕ) : Data) = .nil := rfl

/-- The dimension branch on `(s, λ, n, τ)`, `s` in binary: the numeral `2^{τ(|λ| + |n|)} s`. -/
theorem dimProg_runs_encode (lam tau n s : ℕ) :
    ∃ t ≤ dimCost tau (Nat.size lam + Nat.size n) (esize lam) (esize n) (esize s) + 3,
      Eval [Data.cons (encode s) (.cons (encode lam) (.cons (encode n) (encode tau)))] dimProg
        (encode (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) t := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [encode_nat_zero, mul_zero]
    exact ⟨3, by omega, dimProg_runs_nil _⟩
  · have hne : s.bits ≠ [] := by
      intro h
      have h1 := Nat.size_eq_bits_len s
      rw [h, List.length_nil] at h1
      have h2 := Nat.size_pos.mpr hs
      omega
    obtain ⟨h, l, hl⟩ := List.exists_cons_of_ne_nil hne
    have hs' : (encode s : Data) = list (ofBool h :: l.map ofBool) := by
      rw [encode_nat_eq_list, hl, List.map_cons]
    obtain ⟨t, ht, run⟩ := dimProg_runs tau (lam.bits.map ofBool) (n.bits.map ofBool) (ofBool h)
      (l.map ofBool)
    refine ⟨t, ?_, ?_⟩
    · refine le_trans ht ?_
      simp only [List.length_map, Nat.size_eq_bits_len]
      rw [← hs', ← encode_nat_eq_list, ← encode_nat_eq_list]
      exact Nat.le_add_right _ _
    · rw [← List.map_cons, ← hl, ← encode_nat_eq_list, ← encode_nat_eq_list,
        ← encode_nat_eq_list] at run
      convert run using 2
      rw [encode_nat_eq_list, Nat.bits_two_pow_mul _ hs.ne', List.map_append,
        replicate_nil_eq_map, List.length_map, List.length_map, Nat.size_eq_bits_len,
        Nat.size_eq_bits_len]

/-- A bound on the sizes in the block loop of the core on a query of size `D`. -/
def zBound (sD : Data) (n s D Tu : ℕ) : ℕ :=
  s + 3 * D + (sD.size + esize n + D + 4) + 1 + D * (Tu + 1) + Tu

/-- The cost of the core on a query of size `D` at index `n`, with the dimension query
answered in time `td` and each block query in time `Tu`: the sum of the branches' bounds. -/
def anyCost (lam tau n : ℕ) (sD : Data) (s D td Tu : ℕ) : ℕ :=
  td + 2 * (sD.size + esize n) + 40 +
    (2 * (esize s + esize lam + esize n + esize tau) + 20 +
      dimCost tau (Nat.size lam + Nat.size n) (esize lam) (esize n) (esize s)) +
    (2 * (sD.size + esize n + esize s + D) + 40 +
      lockCost s (sD.size + esize n + D + 4) D D (zBound sD n s D Tu) +
      esize 0 + toUnaryCost 0 + sD.size + esize n + 3 * D)

/-- **The core halts on every query**, within `anyCost`, given the dimension of `S̄` at `n`
and the answers of `S̄` on the block queries. -/
theorem repSampCore_runs_any {univ : Prog} (hU : univ.WellScoped 1) (sD : Data)
    (lam tau n s : ℕ) (d : Data) {td : ℕ}
    (hdim : Eval [Data.cons sD (.cons (encode n) (encode CL.Sampler.Query.dimension))] univ
      (encode s) td)
    (fq : Data → Data) (Tu : ℕ)
    (hq : ∀ q ∈ blockQueries s d,
      ∃ t ≤ Tu, Eval [Data.cons sD (.cons (encode n) q)] univ (fq q) t) :
    ∃ r t, t ≤ anyCost lam tau n sD s d.size td Tu ∧
      Eval [Data.cons (sampParams sD (encode lam) (encode tau)) (.cons (encode n) d)]
        (repSampCore univ) r t := by
  have hN : (encode n : Data).size = esize n := rfl
  rcases d with _ | ⟨_ | ⟨k₀, k₁⟩, qr⟩
  · refine ⟨.nil, _, ?_, repSampCore_prefix hU _ _ _ _ _ hdim (coreDispatch_nil univ _ _ _ _ _)⟩
    unfold anyCost; rw [hN]; omega
  · obtain ⟨t, ht, run⟩ := dimProg_runs_encode lam tau n s
    refine ⟨_, _, ?_, repSampCore_prefix hU _ _ _ _ _ hdim (coreDispatch_dim univ sD _ _ _ qr _ run)⟩
    have hL : (encode lam : Data).size = esize lam := rfl
    have hT : (encode tau : Data).size = esize tau := rfl
    have hS : (encode s : Data).size = esize s := rfl
    unfold anyCost; rw [hN, hL, hT, hS]; omega
  · set kD : Data := .cons k₀ k₁ with hkD
    have hlock : ∀ {r t}, Eval [Data.cons sD (.cons (encode n) (.cons (encode s) (.cons kD qr)))]
        (lockProg univ) r t →
        Eval [Data.cons (sampParams sD (encode lam) (encode tau)) (.cons (encode n) (.cons kD qr))]
          (repSampCore univ) r
          (t + 2 * (sD.size + esize n + esize s + k₀.size + k₁.size + qr.size) + 20 + td +
            2 * (sD.size + esize n) + 32) := fun h =>
      repSampCore_prefix hU _ _ _ _ _ hdim (coreDispatch_lock hU sD _ _ _ k₀ k₁ qr _ h)
    have hS : (encode s : Data).size = esize s := rfl
    rcases qr with _ | ⟨wD, _ | ⟨jD, _ | ⟨uD, yD⟩⟩⟩
    · obtain ⟨t, ht, run⟩ := lockProg_runs_malformed univ sD (encode n) (encode s) kD .nil (Or.inl rfl)
      refine ⟨_, _, ?_, hlock run⟩
      unfold anyCost; simp only [hkD, size_cons, size_nil]; omega
    · obtain ⟨t, ht, run⟩ := lockProg_runs_malformed univ sD (encode n) (encode s) kD _
        (Or.inr (Or.inl ⟨wD, rfl⟩))
      refine ⟨_, _, ?_, hlock run⟩
      unfold anyCost; simp only [hkD, size_cons, size_nil]; omega
    · obtain ⟨t, ht, run⟩ := lockProg_runs_malformed univ sD (encode n) (encode s) kD _
        (Or.inr (Or.inr ⟨wD, jD, rfl⟩))
      refine ⟨_, _, ?_, hlock run⟩
      unfold anyCost; simp only [hkD, size_cons, size_nil]; omega
    · rcases Nat.eq_zero_or_pos s with rfl | hs
      · obtain ⟨t, ht, run⟩ := lockProg_runs_zero univ sD (encode n) kD wD jD uD yD
        refine ⟨_, _, ?_, hlock run⟩
        unfold anyCost; simp only [hN, hkD, size_cons] at ht ⊢; omega
      · set D := (Data.cons kD (.cons wD (.cons jD (.cons uD yD)))).size with hD
        have hDeq : D = kD.size + wD.size + jD.size + uD.size + yD.size + 4 := by
          simp only [hD, size_cons]; omega
        have hkDsz : kD.size = k₀.size + k₁.size + 1 := by simp [hkD]
        set f : List Data → List Data → Data := fun cU cY =>
          fq (.cons kD (.cons wD (.cons jD (.cons (list cU) (list cY))))) with hf
        have hf' : ∀ p ∈ chunkPairs s hs (toList uD) (toList yD),
            ∃ t ≤ Tu, Eval [mapQuery sD (encode n) kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t := by
          intro p hp
          refine hq _ ?_
          simp only [blockQueries, hkD, dif_pos hs, List.mem_map]
          exact ⟨p, hp, rfl⟩
        have hZ : s + (list (toList uD)).size + (list (toList yD)).size +
            (mapCtx sD (encode n) kD wD jD).size + 1 + (toList uD).length * (Tu + 1) + Tu ≤
            zBound sD n s D Tu := by
          have h1 : (toList uD).length ≤ D := by
            have := length_le_size_list_prime (toList uD)
            rw [list_toList] at this
            omega
          have h2 : (toList uD).length * (Tu + 1) ≤ D * (Tu + 1) := Nat.mul_le_mul_right _ h1
          simp only [list_toList, mapCtx, size_cons, zBound]
          omega
        obtain ⟨t, ht, run⟩ := lockProg_runs hU hs sD (encode n) kD wD jD (toList uD) (toList yD)
          f Tu (zBound sD n s D Tu) hf' hZ
        simp only [list_toList] at run
        refine ⟨_, _, ?_, hlock run⟩
        have hmono := lockCost_mono (s := s) (Z := zBound sD n s D Tu)
          (C := (mapCtx sD (encode n) kD wD jD).size) (C' := sD.size + esize n + D + 4)
          (U := uD.size) (U' := D) (Y := yD.size) (Y' := D)
          (by simp only [mapCtx, size_cons, hN]; omega) (by omega) (by omega)
        unfold anyCost
        simp only [hN, size_cons, mapCtx, list_toList] at ht hmono ⊢
        omega

/-! ## The sampler -/

/-- The program of the repeated sampler on `(S̄, λ, τ)`: the core, hardcoded. -/
noncomputable def repSamplerProg (sp : Prog) (lam tau : ℕ) : Prog :=
  hardcode (repSampCore selfUniversal.univ) (encode (sp, lam, tau))

theorem repSamplerProg_wellScoped (sp : Prog) (lam tau : ℕ) :
    (repSamplerProg sp lam tau).WellScoped 1 :=
  hardcode_wellScoped (repSampCore_wellScoped selfUniversal.closed) _

theorem repSamplerProg_runs (sp : Prog) (lam tau n : ℕ) (d : Data) {r : Data} {t : ℕ}
    (h : Eval [Data.cons (sampParams (encode sp) (encode lam) (encode tau)) (.cons (encode n) d)]
      (repSampCore selfUniversal.univ) r t) :
    (repSamplerProg sp lam tau).Runs (.cons (encode n) d) r
      (t + (encode (sp, lam, tau) : Data).size + (Data.cons (encode n) d).size + 3) :=
  hardcode_time (repSampCore_wellScoped selfUniversal.closed) h

variable {ℓ : ℕ} (S : CL.Sampler ℓ)

/-- The dimension query to `S`, through the universal machine. -/
theorem dim_call (n : ℕ) :
    ∃ td, Eval [Data.cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension))]
      selfUniversal.univ (encode (S.dim n)) td := by
  obtain ⟨t, h⟩ := S.runs_dimension n
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
  exact ⟨t', h'⟩

/-- Any block query to `S`, through the universal machine, halts with `S`'s own result. -/
theorem block_call (n : ℕ) (q : Data) :
    ∃ r t, Eval [Data.cons (encode S.prog) (.cons (encode n) q)] selfUniversal.univ r t := by
  obtain ⟨r, t, h⟩ := S.halts n q
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
  exact ⟨r, t', h'⟩

/-- **The repeated sampler halts on every input.** -/
theorem repSampler_halts (lam tau n : ℕ) (d : Data) :
    Halts (repSamplerProg S.prog lam tau) (.cons (encode n) d) := by
  obtain ⟨td, hdim⟩ := dim_call S n
  classical
  let fq : Data → Data := fun q => (block_call S n q).choose
  have hfq : ∀ q, ∃ t, Eval [Data.cons (encode S.prog) (.cons (encode n) q)] selfUniversal.univ
      (fq q) t := fun q => (block_call S n q).choose_spec
  obtain ⟨Tu, hTu⟩ := exists_uniform_bound (blockQueries (S.dim n) d)
    (fun q t => Eval [Data.cons (encode S.prog) (.cons (encode n) q)] selfUniversal.univ (fq q) t)
    (fun q _ => hfq q)
  obtain ⟨r, t, -, run⟩ := repSampCore_runs_any selfUniversal.closed (encode S.prog) lam tau n
    (S.dim n) d hdim fq Tu hTu
  exact ⟨r, _, repSamplerProg_runs S.prog lam tau n d run⟩

/-- The universal machine on a block query, from `S`'s answer. -/
theorem univ_call (n : ℕ) (q r : Data) {t : ℕ} (h : S.prog.Runs (.cons (encode n) q) r t) :
    ∃ t', Eval [Data.cons (encode S.prog) (.cons (encode n) q)] selfUniversal.univ r t' := by
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
  exact ⟨t', h'⟩

/-- **The dimension query.** -/
theorem repSampler_runs_dimension (lam tau n : ℕ) :
    ∃ t, (repSamplerProg S.prog lam tau).Runs (encode (n, CL.Sampler.Query.dimension))
      (encode (Repetition.reps lam tau n * S.dim n)) t := by
  obtain ⟨td, hdim⟩ := dim_call S n
  obtain ⟨t, -, run⟩ := dimProg_runs_encode lam tau n (S.dim n)
  exact ⟨_, repSamplerProg_runs S.prog lam tau n _
    (repSampCore_prefix selfUniversal.closed _ _ _ _ _ hdim
      (coreDispatch_dim selfUniversal.univ (encode S.prog) _ _ _ _ _ run))⟩

/-- `lockProg` on well-formed blocks: with `g` the answer of `S̄` on a pair of blocks, the
concatenation of the answers on the `k` pairs. -/
theorem lockProg_runs_blocks {univ : Prog} (hU : univ.WellScoped 1) {s : ℕ} (hs : 0 < s)
    (sD nD kD wD jD : Data) (k : ℕ) (z y' : BitStr) (hz : z.length = k * s)
    (g : BitStr → BitStr → BitStr)
    (hg : ∀ i : Fin k, ∃ t, Eval [mapQuery sD nD kD wD jD (encode (chunk s i z))
      (encode (chunk s i y'))] univ (encode (g (chunk s i z) (chunk s i y'))) t) :
    ∃ t, Eval [lockInput sD nD (encode s) kD wD jD (encode z) (encode y')] (lockProg univ)
      (encode (List.ofFn fun i : Fin k => g (chunk s i z) (chunk s i y')).flatten) t := by
  set f : List Data → List Data → Data := fun cU cY => encode (g (bitsOf cU) (bitsOf cY)) with hf
  have hpairs : chunkPairs s hs (z.map ofBool) (y'.map ofBool) =
      List.ofFn fun i : Fin k => ((chunk s i z).map ofBool, (chunk s i y').map ofBool) := by
    rw [chunkPairs_eq_ofFn s hs k _ _ (by simp [hz])]
    simp only [chunk_map]
  have hcalls : ∀ p ∈ chunkPairs s hs (z.map ofBool) (y'.map ofBool),
      ∃ t, Eval [mapQuery sD nD kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t := by
    intro p hp
    rw [hpairs, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨t, h⟩ := hg i
    refine ⟨t, ?_⟩
    simpa only [hf, bitsOf_map_ofBool, encode_bitStr_eq_list] using h
  obtain ⟨Tu, hTu⟩ := exists_uniform_bound _ _ hcalls
  obtain ⟨t, -, run⟩ := lockProg_runs hU hs sD nD kD wD jD (z.map ofBool) (y'.map ofBool) f Tu _
    hTu le_rfl
  have hout : list ((chunkPairs s hs (z.map ofBool) (y'.map ofBool)).map
      fun p => toList (f p.1 p.2)).flatten =
      encode (List.ofFn fun i : Fin k => g (chunk s i z) (chunk s i y')).flatten := by
    rw [hpairs, List.map_ofFn, encode_bitStr_eq_list, List.map_flatten, List.map_ofFn]
    refine congrArg (fun L : List (List Data) => list L.flatten)
      (congrArg List.ofFn (funext fun i => ?_))
    simp [hf, bitsOf_map_ofBool, toList_encode_bitStr]
  rw [hout, ← encode_bitStr_eq_list z, ← encode_bitStr_eq_list y'] at run
  exact ⟨t, run⟩

/-- The run of the repeated sampler on a query of nonzero kind, from a run of `lockProg`. -/
theorem repSampler_runs_of_lock (lam tau n : ℕ) (k₀ k₁ qr : Data) {r : Data} {t td : ℕ}
    (hdim : Eval [Data.cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension))]
      selfUniversal.univ (encode (S.dim n)) td)
    (run : Eval [Data.cons (encode S.prog) (.cons (encode n) (.cons (encode (S.dim n))
      (.cons (.cons k₀ k₁) qr)))] (lockProg selfUniversal.univ) r t) :
    ∃ t', (repSamplerProg S.prog lam tau).Runs (.cons (encode n) (.cons (.cons k₀ k₁) qr)) r t' :=
  ⟨_, repSamplerProg_runs S.prog lam tau n _
    (repSampCore_prefix selfUniversal.closed _ _ _ _ _ hdim
      (coreDispatch_lock selfUniversal.closed (encode S.prog) _ _ _ k₀ k₁ qr _ run))⟩

theorem encode_nat_one : (encode (1 : ℕ) : Data) = .cons (.cons .nil .nil) .nil := rfl
theorem encode_nat_two : (encode (2 : ℕ) : Data) = .cons .nil (.cons (.cons .nil .nil) .nil) := rfl
theorem encode_nat_three :
    (encode (3 : ℕ) : Data) = .cons (.cons .nil .nil) (.cons (.cons .nil .nil) .nil) := rfl

theorem encode_marginal (n : ℕ) (w : Player) (j : ℕ) (z : BitStr) :
    (encode (n, CL.Sampler.Query.marginal w j z) : Data) =
      .cons (encode n) (.cons (.cons (.cons .nil .nil) .nil)
        (.cons (encode w) (.cons (encode j) (.cons (encode z) .nil)))) := by
  show Data.cons (encode n) (.cons (encode (1 : ℕ)) (.cons (encode w) (.cons (encode j)
    (.cons (encode z) .nil)))) = _
  rw [encode_nat_one]

theorem encode_linear (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr) :
    (encode (n, CL.Sampler.Query.linear w j u y) : Data) =
      .cons (encode n) (.cons (.cons .nil (.cons (.cons .nil .nil) .nil))
        (.cons (encode w) (.cons (encode j) (.cons (encode u) (encode y))))) := by
  show Data.cons (encode n) (.cons (encode (2 : ℕ)) (.cons (encode w) (.cons (encode j)
    (.cons (encode u) (encode y))))) = _
  rw [encode_nat_two]

theorem encode_factor (n : ℕ) (w : Player) (j : ℕ) (u : BitStr) :
    (encode (n, CL.Sampler.Query.factor w j u) : Data) =
      .cons (encode n) (.cons (.cons (.cons .nil .nil) (.cons (.cons .nil .nil) .nil))
        (.cons (encode w) (.cons (encode j) (.cons (encode u) .nil)))) := by
  show Data.cons (encode n) (.cons (encode (3 : ℕ)) (.cons (encode w) (.cons (encode j)
    (.cons (encode u) .nil)))) = _
  rw [encode_nat_three]

/-- **The marginal query.** -/
theorem repSampler_runs_marginal (lam tau n : ℕ) (w : Player) (j : ℕ) (z : BitStr) (hj : 1 ≤ j)
    (hj' : j ≤ ℓ) (hz : z.length = Repetition.reps lam tau n * S.dim n) :
    ∃ t, (repSamplerProg S.prog lam tau).Runs (encode (n, CL.Sampler.Query.marginal w j z))
      (encode (toBits (((CLFun.famSum finProdFinEquiv ℓ
        fun _ : Fin (Repetition.reps lam tau n) => S.cl n w).truncate j).eval
        (ofBits (Repetition.reps lam tau n * S.dim n) z)))) t := by
  obtain ⟨td, hdim⟩ := dim_call S n
  rw [encode_marginal, CLFun.eval_truncate_famSum, toBits_join]
  simp only [block_ofBits]
  rcases Nat.eq_zero_or_pos (S.dim n) with hs | hs
  · have hz0 : z = [] := List.eq_nil_of_length_eq_zero (by rw [hz, hs, mul_zero])
    have hout : (List.ofFn fun i : Fin (Repetition.reps lam tau n) =>
        toBits (((S.cl n w).truncate j).eval (ofBits (S.dim n) (chunk (S.dim n) i z)))).flatten = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [length_flatten_ofFn _ fun i => CL.length_toBits _, hs, mul_zero]
    rw [hout]
    obtain ⟨t, -, run⟩ := lockProg_runs_zero selfUniversal.univ (encode S.prog) (encode n)
      (encode (1 : ℕ)) (encode w) (encode j) (encode z) .nil
    have run' : Eval [Data.cons (encode S.prog) (.cons (encode n) (.cons (encode (S.dim n))
        (.cons (.cons (.cons .nil .nil) .nil) (.cons (encode w) (.cons (encode j)
          (.cons (encode z) .nil))))))] (lockProg selfUniversal.univ) .nil t := by
      rw [hs]; exact run
    subst hz0
    exact repSampler_runs_of_lock S lam tau n (.cons .nil .nil) .nil _ hdim run'
  · obtain ⟨t, run⟩ := lockProg_runs_blocks selfUniversal.closed hs (encode S.prog) (encode n)
      (encode (1 : ℕ)) (encode w) (encode j) (Repetition.reps lam tau n) z [] hz
      (fun c _ => toBits (((S.cl n w).truncate j).eval (ofBits (S.dim n) c))) (fun i => by
        obtain ⟨t, h⟩ := S.runs_marginal n w j (chunk (S.dim n) i z) hj hj' (length_chunk hz i)
        rw [chunk_nil]
        exact univ_call S n _ _ h)
    exact repSampler_runs_of_lock S lam tau n (.cons .nil .nil) .nil _ hdim run

/-- The blocks of a string in the image of a truncation of the direct sum are in the images
of the truncations of the summands. -/
theorem chunk_toBits_truncate (lam tau n : ℕ) (w : Player) (j : ℕ) (u : BitStr)
    (hu : ∃ x, u = toBits (((CLFun.famSum finProdFinEquiv ℓ
      fun _ : Fin (Repetition.reps lam tau n) => S.cl n w).truncate j).eval x)) :
    u.length = Repetition.reps lam tau n * S.dim n ∧
      ∀ i : Fin (Repetition.reps lam tau n),
        ∃ x, chunk (S.dim n) i u = toBits (((S.cl n w).truncate j).eval x) := by
  obtain ⟨x, rfl⟩ := hu
  rw [CLFun.eval_truncate_famSum, toBits_join]
  refine ⟨length_flatten_ofFn _ fun i => CL.length_toBits _, fun i => ⟨block finProdFinEquiv i x, ?_⟩⟩
  rw [chunk_flatten_ofFn _ fun i => CL.length_toBits _]

/-- **The linear query.** -/
theorem repSampler_runs_linear (lam tau n : ℕ) (w : Player) (j : ℕ) (u y : BitStr) (hj : 1 ≤ j)
    (hj' : j ≤ ℓ)
    (hu : ∃ x, u = toBits (((CLFun.famSum finProdFinEquiv ℓ
      fun _ : Fin (Repetition.reps lam tau n) => S.cl n w).truncate (j - 1)).eval x))
    (hy : y.length = Repetition.reps lam tau n * S.dim n) :
    ∃ t, (repSamplerProg S.prog lam tau).Runs (encode (n, CL.Sampler.Query.linear w j u y))
      (encode (toBits ((CLFun.famSum finProdFinEquiv ℓ
        fun _ : Fin (Repetition.reps lam tau n) => S.cl n w).mapOfPrefix (j - 1)
        (ofBits (Repetition.reps lam tau n * S.dim n) u)
        (ofBits (Repetition.reps lam tau n * S.dim n) y)))) t := by
  obtain ⟨td, hdim⟩ := dim_call S n
  obtain ⟨hu', hblocks⟩ := chunk_toBits_truncate S lam tau n w (j - 1) u hu
  rw [encode_linear, CLFun.mapOfPrefix_famSum, toBits_join]
  simp only [block_ofBits]
  rcases Nat.eq_zero_or_pos (S.dim n) with hs | hs
  · have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by rw [hu', hs, mul_zero])
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by rw [hy, hs, mul_zero])
    have hout : (List.ofFn fun i : Fin (Repetition.reps lam tau n) =>
        toBits ((S.cl n w).mapOfPrefix (j - 1) (ofBits (S.dim n) (chunk (S.dim n) i u))
          (ofBits (S.dim n) (chunk (S.dim n) i y)))).flatten = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [length_flatten_ofFn _ fun i => CL.length_toBits _, hs, mul_zero]
    rw [hout]
    obtain ⟨t, -, run⟩ := lockProg_runs_zero selfUniversal.univ (encode S.prog) (encode n)
      (encode (2 : ℕ)) (encode w) (encode j) (encode u) (encode y)
    have run' : Eval [Data.cons (encode S.prog) (.cons (encode n) (.cons (encode (S.dim n))
        (.cons (.cons .nil (.cons (.cons .nil .nil) .nil)) (.cons (encode w) (.cons (encode j)
          (.cons (encode u) (encode y)))))))] (lockProg selfUniversal.univ) .nil t := by
      rw [hs]; exact run
    subst hu0 hy0
    exact repSampler_runs_of_lock S lam tau n .nil (.cons (.cons .nil .nil) .nil) _ hdim run'
  · obtain ⟨t, run⟩ := lockProg_runs_blocks selfUniversal.closed hs (encode S.prog) (encode n)
      (encode (2 : ℕ)) (encode w) (encode j) (Repetition.reps lam tau n) u y hu'
      (fun c c' => toBits ((S.cl n w).mapOfPrefix (j - 1) (ofBits (S.dim n) c) (ofBits (S.dim n) c')))
      (fun i => by
        obtain ⟨t, h⟩ := S.runs_linear n w j (chunk (S.dim n) i u) (chunk (S.dim n) i y) hj hj'
          (hblocks i) (length_chunk hy i)
        exact univ_call S n _ _ h)
    exact repSampler_runs_of_lock S lam tau n .nil (.cons (.cons .nil .nil) .nil) _ hdim run

/-- **The factor query.** -/
theorem repSampler_runs_factor (lam tau n : ℕ) (w : Player) (j : ℕ) (u : BitStr) (hj : 1 ≤ j)
    (hj' : j ≤ ℓ)
    (hu : ∃ x, u = toBits (((CLFun.famSum finProdFinEquiv ℓ
      fun _ : Fin (Repetition.reps lam tau n) => S.cl n w).truncate (j - 1)).eval x)) :
    ∃ t, (repSamplerProg S.prog lam tau).Runs (encode (n, CL.Sampler.Query.factor w j u))
      (encode (indicatorBits ((CLFun.famSum finProdFinEquiv ℓ
        fun _ : Fin (Repetition.reps lam tau n) => S.cl n w).factorOfPrefix (j - 1)
        (ofBits (Repetition.reps lam tau n * S.dim n) u)))) t := by
  obtain ⟨td, hdim⟩ := dim_call S n
  obtain ⟨hu', hblocks⟩ := chunk_toBits_truncate S lam tau n w (j - 1) u hu
  rw [encode_factor, CLFun.factorOfPrefix_famSum, indicatorBits_blockSet]
  simp only [block_ofBits]
  rcases Nat.eq_zero_or_pos (S.dim n) with hs | hs
  · have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by rw [hu', hs, mul_zero])
    have hout : (List.ofFn fun i : Fin (Repetition.reps lam tau n) =>
        indicatorBits ((S.cl n w).factorOfPrefix (j - 1)
          (ofBits (S.dim n) (chunk (S.dim n) i u)))).flatten = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [length_flatten_ofFn _ fun i => length_indicatorBits _, hs, mul_zero]
    rw [hout]
    obtain ⟨t, -, run⟩ := lockProg_runs_zero selfUniversal.univ (encode S.prog) (encode n)
      (encode (3 : ℕ)) (encode w) (encode j) (encode u) .nil
    have run' : Eval [Data.cons (encode S.prog) (.cons (encode n) (.cons (encode (S.dim n))
        (.cons (.cons (.cons .nil .nil) (.cons (.cons .nil .nil) .nil)) (.cons (encode w)
          (.cons (encode j) (.cons (encode u) .nil))))))] (lockProg selfUniversal.univ) .nil t := by
      rw [hs]; exact run
    subst hu0
    exact repSampler_runs_of_lock S lam tau n (.cons .nil .nil) (.cons (.cons .nil .nil) .nil) _
      hdim run'
  · obtain ⟨t, run⟩ := lockProg_runs_blocks selfUniversal.closed hs (encode S.prog) (encode n)
      (encode (3 : ℕ)) (encode w) (encode j) (Repetition.reps lam tau n) u [] hu'
      (fun c _ => indicatorBits ((S.cl n w).factorOfPrefix (j - 1) (ofBits (S.dim n) c)))
      (fun i => by
        obtain ⟨t, h⟩ := S.runs_factor n w j (chunk (S.dim n) i u) hj hj' (hblocks i)
        rw [chunk_nil]
        exact univ_call S n _ _ h)
    exact repSampler_runs_of_lock S lam tau n (.cons .nil .nil) (.cons (.cons .nil .nil) .nil) _
      hdim run

/-- **The repeated sampler** (`ComputeParrepVerifier`, sampler half): `k(n)` independent
copies of `S`, `k(n) = 2^{τ(|λ| + |n|)}`. -/
noncomputable def repSampler (lam tau : ℕ) : CL.Sampler ℓ where
  prog := repSamplerProg S.prog lam tau
  closed := repSamplerProg_wellScoped _ _ _
  dim n := Repetition.reps lam tau n * S.dim n
  cl n w := CLFun.famSum finProdFinEquiv ℓ fun _ : Fin (Repetition.reps lam tau n) => S.cl n w
  cl_exactlyOn n w := by
    have := CLFun.exactlyOn_famSum finProdFinEquiv ℓ
      (fun _ : Fin (Repetition.reps lam tau n) => S.cl n w) (fun _ => Finset.univ)
      (fun _ => S.cl_exactlyOn n w)
    rwa [blockSet_univ] at this
  runs_dimension n := repSampler_runs_dimension S lam tau n
  runs_marginal n w j z hj hj' hz := repSampler_runs_marginal S lam tau n w j z hj hj' hz
  runs_linear n w j u y hj hj' hu hy := repSampler_runs_linear S lam tau n w j u y hj hj' hu hy
  runs_factor n w j u hj hj' hu := repSampler_runs_factor S lam tau n w j u hj hj' hu
  halts n d := repSampler_halts S lam tau n d

@[simp] theorem repSampler_prog (lam tau : ℕ) :
    (repSampler S lam tau).prog = repSamplerProg S.prog lam tau := rfl

@[simp] theorem repSampler_dim (lam tau n : ℕ) :
    (repSampler S lam tau).dim n = Repetition.reps lam tau n * S.dim n := rfl

end MIPRE.Repeat


