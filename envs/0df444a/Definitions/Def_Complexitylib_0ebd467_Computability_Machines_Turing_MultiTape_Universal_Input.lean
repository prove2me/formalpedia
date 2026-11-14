-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Input
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Input
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:54:33.993305+00:00
-- url     : https://prove2.me/theorems/9156dc36-6e17-4251-bb34-41f8c2c89b16
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Input — Streaming lookup of the simulated input symbol
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Input` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   After linear argument reordering, `inputSymbol_stream_inO` streams the unary-encoded list once,
--   retaining a binary countdown. The selected symbol is emitted directly; it is never retained across
--   later rounds. With encoded
--   input length `N` and binary position length `b`, lookup takes `O((N + 1) * (b + 1)²)` time and
--   linear workspace. The square comes from the existing binary predecessor certificate.
--
--   The public theorem supplies a plain machine certificate. Its implementation uses the streaming
--   fold backend and includes the linear cost of moving the position before the list in the encoding.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Input`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Input.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_StreamFold
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinarySizeFacts
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Input` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Streaming lookup of the simulated input symbol

After linear argument reordering, `inputSymbol_stream_inO` streams the unary-encoded list once,
retaining a binary countdown. The selected symbol is emitted directly; it is never retained across
later rounds. With encoded
input length `N` and binary position length `b`, lookup takes `O((N + 1) * (b + 1)²)` time and
linear workspace. The square comes from the existing binary predecessor certificate.

The public theorem supplies a plain machine certificate. Its implementation uses the streaming
fold backend and includes the linear cost of moving the position before the list in the encoding.
-/

namespace Turing.MultiTapeTM.Universal

private def symbolReader : InputReader Bool Bool where
  q₀ := false
  step
    | false, true => (some true, none)
    | false, false => (none, none)
    | true, b => (some false, some b)

private theorem read_symbolReader (w rest : List Bool) :
    symbolReader.read false (frame w ++ rest) = (w, (frame w).length) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [frame_cons, List.cons_append, List.cons_append,
      symbolReader.read_cons_of_some (q' := true) _ rfl,
      symbolReader.read_cons_of_some (q' := false) _ rfl, ih]
    simp [symbolReader, Nat.add_assoc]

private def inputNext (q : ℕ × ℕ) : ℕ := q.1 - 1

private def inputEmit (q : ℕ × ℕ) : Option ℕ := if q.1 = 1 then some q.2 else none

private theorem input_state (p : ℕ) (x : List ℕ) (j : ℕ) :
    streamState p inputNext x j = p - (x.take j).length := by
  have hfold (l : List ℕ) (k : ℕ) :
      l.foldl (fun s a => inputNext (s, a)) k = k - l.length := by
    induction l generalizing k with
    | nil => simp
    | cons a l ih =>
      rw [List.foldl_cons, ih]
      simp only [inputNext, List.length_cons, Nat.sub_sub]
      omega
  exact hfold _ _

private theorem input_emission (p : ℕ) (x : List ℕ) :
    streamEmit inputNext (fun q => encOption encUnary (inputEmit q)) p x =
      encOption encUnary (inputSymbol x p) := by
  induction x generalizing p with
  | nil => simp [streamEmit, inputSymbol]
  | cons a x ih =>
    rw [streamEmit, ih]
    rcases p with _ | (_ | p) <;> simp [inputNext, inputEmit, inputSymbol]

private theorem inputNext_inO :
    ComputableInO inputNext (encPair encNat encUnary) encNat
      (fun q => ((encNat q.1).length + 1) ^ 2 + q.2 + 1)
      (fun q => (encNat q.1).length + q.2 + 1) := by
  refine ((ComputableInO.natPred.comp (ComputableInO.fst encNat encUnary)).mono 8
    (fun q => ?_) (fun q => ?_)).of_enc_eq (fun _ => rfl)
  · simp only [length_encPair, encUnary_apply, List.length_replicate]
    nlinarith
  · simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega

private theorem inputEmit_inO :
    ComputableInO inputEmit (encPair encNat encUnary) (encOption encUnary)
      (fun q => (encPair encNat encUnary q).length)
      (fun q => (encPair encNat encUnary q).length) := by
  have hc := (ComputableInO.eq encNat).comp
    ((ComputableInO.const (encIn := encPair encNat encUnary) (encMid := encNat) 1).prod
      (ComputableInO.fst encNat encUnary))
  have hs := (ComputableInO.of_linear
    (OptionEncoding.some (enc₁ := encUnary) (enc := encOption encUnary))).comp_linear
      (ComputableInO.snd encNat encUnary)
  refine ((hc.ite hs (ComputableInO.const none)).mono 16 (fun q => ?_) (fun q => ?_)).of_enc_eq
    (fun q => by simp [inputEmit, Function.comp_apply, eq_comm])
  all_goals
    simp only [length_encPair, show (encNat 1).length = 1 from rfl,
      Function.comp_apply]
    split_ifs <;> omega

/-- A lookup returns at most one input symbol, with one additional bit for the option tag. -/
public theorem length_inputSymbol_le (x : List ℕ) (p : ℕ) :
    (encOption encUnary (inputSymbol x p)).length ≤ (encList encUnary x).length + 1 := by
  unfold inputSymbol
  split_ifs
  · simp
  · cases h : (x.drop (p - 1)).head? with
    | none => simp
    | some a =>
      have ha : a ∈ x := List.mem_of_mem_drop (List.mem_of_mem_head? h)
      have := length_le_encList_of_mem encUnary ha
      simpa using Nat.succ_le_succ this

private theorem inputSymbol_pair_inO :
    ComputableInO (fun q : ℕ × List ℕ => inputSymbol q.2 q.1)
      (encPair encNat (encList encUnary)) (encOption encUnary)
      (fun q => ((encList encUnary q.2).length + 1) * ((encNat q.1).length + 1) ^ 2)
      (fun q => (encPair encNat (encList encUnary) q).length) := by
  obtain ⟨cN, hN, -⟩ := inputNext_inO.tidy
  obtain ⟨cE, hE, -⟩ := inputEmit_inO.tidy
  obtain ⟨cF, hF, -⟩ := (ComputableInO.const (encIn := encNat)
    (encMid := encOption encUnary) none).tidy
  let B (q : ℕ × List ℕ) := (encNat q.1).length
  let N (q : ℕ × List ℕ) := (encList encUnary q.2).length
  let K := 3 * cN + 3 * cE + 3
  let W (x : List ℕ) (j : ℕ) :=
    ((x.map fun a => frame (encUnary a))[j]?.getD []).length
  have hW (x : List ℕ) (j : ℕ) (hj : j < x.length) : W x j = 2 * x[j] + 1 := by
    simp [W, hj, encUnary_apply]
  have hsum (x : List ℕ) : ∑ j ∈ Finset.range x.length, W x j = (encList encUnary x).length := by
    simpa [W, List.flatMap_def, encList, Function.comp_def] using
      sum_length_getD (x.map fun a => frame (encUnary a))
  have hstate (q : ℕ × List ℕ) (j : ℕ) :
      (encNat (streamState q.1 inputNext q.2 j)).length ≤ B q := by
    rw [input_state]
    exact ComputableTidilyInO.length_encNat_mono (Nat.sub_le _ _)
  have helem (q : ℕ × List ℕ) (j : ℕ) (hj : j < q.2.length) : q.2[j] ≤ N q := by
    simpa [encUnary_apply] using length_le_encList_of_mem encUnary (List.getElem_mem hj)
  have hstream := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (encIn := encPair encNat (encList encUnary)) (encOut := encOption encUnary)
    symbolReader (fun a => frame (encUnary a)) (fun a => frame_ne_nil _)
    (fun a rest => read_symbolReader _ _) Prod.fst Prod.snd (fun _ => rfl)
    hN hE hF
    (fun q => by simpa using (input_emission q.1 q.2).symm)
    (roundCost := fun q j => K * ((B q + 1) ^ 2 * W q.2 j))
    (sMax := fun q => (cN + cE) * (2 * B q + N q + 2))
    (lMax := fun q => B q + N q) ?_ ?_ ?_ ?_
  · obtain ⟨c, h⟩ := hstream
    have hcost (q : ℕ × List ℕ) :
        ∑ j ∈ Finset.range q.2.length, K * ((B q + 1) ^ 2 * W q.2 j) =
          K * (B q + 1) ^ 2 * N q := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hsum]
      ring
    let C := c * (cF + K + 2 * (cN + cE) + 16) + 1
    refine ComputableInO.of_bounds h.computableInTimeAndSpace C
      (fun q => ?_) (fun q => ?_) (fun q => ?_)
    · let Z := (N q + 1) * (B q + 1) ^ 2
      have hb : B q + 1 ≤ (B q + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
      have hpow : 1 ≤ (B q + 1) ^ 2 := (show 1 ≤ B q + 1 by omega).trans hb
      have hzB : B q + 1 ≤ Z := hb.trans (Nat.le_mul_of_pos_left _ (by omega))
      have hzN : N q + 1 ≤ Z := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N q + 1) hpow
      have hfc := Nat.mul_le_mul_left cF
        ((Nat.add_le_add_right (hstate q q.2.length) 1).trans hzB)
      have hk : K * (B q + 1) ^ 2 * N q ≤ K * Z := by
        have hm := Nat.mul_le_mul_left ((B q + 1) ^ 2) (Nat.le_succ (N q))
        simpa only [Z, Nat.mul_assoc, Nat.mul_comm ((B q + 1) ^ 2)] using
          Nat.mul_le_mul_left K hm
      have hr : (2 * B q + 1 + N q) + (B q + N q) + 1 ≤ 5 * Z := by omega
      have hsum : cF * ((encNat (streamState q.1 inputNext q.2 q.2.length)).length + 1) +
          (2 * B q + 1 + N q) + K * (B q + 1) ^ 2 * N q + (B q + N q) + 1 ≤
          (cF + K + 5) * Z := by
        calc
          _ ≤ cF * Z + K * Z + 5 * Z := by omega
          _ = _ := by ring
      have hcoeff : c * (cF + K + 5) ≤ C :=
        (Nat.mul_le_mul_left c (show cF + K + 5 ≤ cF + K + 2 * (cN + cE) + 16
          by omega)).trans (Nat.le_succ _)
      simp only [length_encPair, hcost]
      change c * (cF * ((encNat (streamState q.1 inputNext q.2 q.2.length)).length + 1) +
        (2 * B q + 1 + N q) + K * (B q + 1) ^ 2 * N q + (B q + N q) + 1) ≤ C * (Z + 1)
      calc
        _ ≤ c * ((cF + K + 5) * Z) := Nat.mul_le_mul_left c hsum
        _ = (c * (cF + K + 5)) * Z := by rw [Nat.mul_assoc]
        _ ≤ C * Z := Nat.mul_le_mul_right Z hcoeff
        _ ≤ C * (Z + 1) := Nat.mul_le_mul_left C (Nat.le_succ _)
    · let Z := 2 * B q + N q + 2
      have hf : (encNat (streamState q.1 inputNext q.2 q.2.length)).length + 1 ≤ Z := by
        have := hstate q q.2.length
        dsimp only [Z]
        omega
      have hfc := Nat.mul_le_mul_left cF hf
      have hr : B q + N q + 1 ≤ Z := by dsimp only [Z]; omega
      have hsum : cF * ((encNat (streamState q.1 inputNext q.2 q.2.length)).length + 1) +
          (cN + cE) * Z + (B q + N q) + 1 ≤ (cF + cN + cE + 1) * Z := by
        calc
          _ ≤ cF * Z + (cN + cE) * Z + Z := by omega
          _ = _ := by ring
      have hcoeff : c * (cF + cN + cE + 1) ≤ C :=
        (Nat.mul_le_mul_left c (show cF + cN + cE + 1 ≤ cF + K + 2 * (cN + cE) + 16
          by omega)).trans (Nat.le_succ _)
      simp only [length_encPair]
      change c * (cF * ((encNat (streamState q.1 inputNext q.2 q.2.length)).length + 1) +
        (cN + cE) * Z + (B q + N q) + 1) ≤ C * (2 * B q + 1 + N q + 1)
      calc
        _ ≤ c * ((cF + cN + cE + 1) * Z) := Nat.mul_le_mul_left c hsum
        _ = (c * (cF + cN + cE + 1)) * Z := by rw [Nat.mul_assoc]
        _ ≤ C * Z := Nat.mul_le_mul_right Z hcoeff
        _ = _ := by
          congr 1
          dsimp only [Z]
          omega
    · have ho := length_inputSymbol_le q.2 q.1
      have hC : 1 ≤ C := by dsimp [C]; omega
      have := Nat.mul_le_mul_right ((encPair encNat (encList encUnary) q).length + 1) hC
      simp only [length_encPair] at this ⊢
      omega
  · intro q j hj
    have hb := hstate q j
    have hb' := hstate q (j + 1)
    rw [hW q.2 j hj]
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    let V := (B q + 1) ^ 2 * (2 * q.2[j] + 1)
    have hv : (B q + 1) ^ 2 ≤ V := Nat.le_mul_of_pos_right _ (by omega)
    have ha : q.2[j] + 1 ≤ V := by
      have hp : 1 ≤ (B q + 1) ^ 2 := by nlinarith
      have := Nat.mul_le_mul_right (2 * q.2[j] + 1) hp
      dsimp only [V]
      nlinarith
    have hp := (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2).trans hv
    have hl : B q + 1 ≤ V := (Nat.le_self_pow two_ne_zero _).trans hv
    have hn := Nat.mul_le_mul_left cN (show
      ((encNat (streamState q.1 inputNext q.2 j)).length + 1) ^ 2 + q.2[j] + 1 + 1 ≤
        3 * V by omega)
    have he := Nat.mul_le_mul_left cE (show
      2 * (encNat (streamState q.1 inputNext q.2 j)).length + 1 + q.2[j] + 1 ≤
        3 * V by omega)
    change _ ≤ K * V
    dsimp only [K]
    nlinarith
  · intro q j hj
    have hb := hstate q j
    have ha := helem q j hj
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    have hn := Nat.mul_le_mul_left cN (show
      (encNat (streamState q.1 inputNext q.2 j)).length + q.2[j] + 1 + 1 ≤
        2 * B q + N q + 2 by omega)
    have he := Nat.mul_le_mul_left cE (show
      2 * (encNat (streamState q.1 inputNext q.2 j)).length + 1 + q.2[j] + 1 ≤
        2 * B q + N q + 2 by omega)
    nlinarith
  · intro q j _
    exact (hstate q j).trans (Nat.le_add_right _ _)
  · intro q j hj
    simpa [encUnary_apply] using (helem q j hj).trans (Nat.le_add_left _ _)

/-- After linear argument reordering, the simulated input symbol can be found by streaming the
encoded list once, with a binary countdown. Time is linear in encoded list length times the square
of the binary position length; workspace is linear in the complete encoded input. The returned
certificate contains an actual multitape machine, including the cost of reordering the arguments
for the streaming pass. -/
public theorem inputSymbol_stream_inO :
    ComputableInO (fun q : List ℕ × ℕ => inputSymbol q.1 q.2)
      (encPair (encList encUnary) encNat) (encOption encUnary)
      (fun q => ((encList encUnary q.1).length + 1) * ((encNat q.2).length + 1) ^ 2)
      (fun q => (encPair (encList encUnary) encNat q).length) := by
  have hswap := (ComputableInO.snd (encList encUnary) encNat).prod
    (ComputableInO.fst (encList encUnary) encNat)
  refine ((inputSymbol_pair_inO.comp hswap).mono 8 (fun q => ?_) (fun q => ?_)).of_enc_eq
    (fun _ => rfl)
  · simp only [length_encPair]
    have hb : (encNat q.2).length + 1 ≤ ((encNat q.2).length + 1) ^ 2 :=
      Nat.le_self_pow two_ne_zero _
    have hn := Nat.mul_le_mul_left ((encList encUnary q.1).length + 1) hb
    nlinarith
  · simp only [length_encPair]
    omega

end Turing.MultiTapeTM.Universal


