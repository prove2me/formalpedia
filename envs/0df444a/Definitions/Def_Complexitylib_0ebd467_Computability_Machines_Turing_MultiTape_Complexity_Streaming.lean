-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Streaming
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Streaming
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:54:51.36695+00:00
-- url     : https://prove2.me/theorems/ff2e9bd5-0c6f-446f-a6f5-1a42857732ac
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming — Quantitative streaming folds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Ordinary `List.foldl` expressions over raw bit strings use Christian Reitwiessner's streaming
--   backend. A round holds the accumulator and one bit, and does not copy the input list. Time, work
--   space and encoded accumulator size remain separate in the contract. Space counts visited work-tape
--   cells, excluding the read-only input and write-only output; retained accumulators are charged.
--   The invariant wrappers use the same pure prefix-fold rule, keeping their distinct resource
--   contracts separate from invariant propagation.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum`: cumulative
--     computation and copying costs, with peak workspace bounds.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec`: an invariant
--     supplies the cumulative cost and postcondition.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum`: stream a paired
--     initial accumulator and bit list `(s₀, l)` on `encPair enc encBits` with cumulative round costs
--     and workspace independent of `l.length`.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum_spec`: invariant
--     wrapper for paired bit-list streaming folds.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`: stream `k` rounds
--     of a state map from `(s, k)`, emitting per round, with cumulative round costs and workspace
--     independent of `k`.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream`: the uniform-round
--     specialization.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec`: an invariant
--     supplies the bounds and a postcondition.
--   * `Turing.MultiTapeTM.ComputableTidilyInO.foldl_bits_finite`: a fixed finite-state fold takes
--     linear time and constant work space, including a bound on its encoded final state.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.map_bits`: a bitwise map emits its output
--     as it scans, in linear time and zero work space.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.reverse_bits`,
--     `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_bits`,
--     `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.dropLast_bits`,
--     `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.getLast?_toList_bits`,
--     `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.getLast?_bits`: linear-time zero-workspace
--     bit-list reversal, unary length, prefix (`List.dropLast`), and last-bit (`List.getLast?.toList`,
--     `List.getLast?`) primitives.
--
--   ### References
--
--   Uses Christian Reitwiessner's `ComputableTidilyInTimeAndSpace.streamFold` from the
--   `crei/tidy-universal` branch; see the source marker in
--   `Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean`.
--
--   **Contents.** The module is published as a whole: 17 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Streaming`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Reverse
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Fold
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_StreamFold
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Quantitative streaming folds

Ordinary `List.foldl` expressions over raw bit strings use Christian Reitwiessner's streaming
backend. A round holds the accumulator and one bit, and does not copy the input list. Time, work
space and encoded accumulator size remain separate in the contract. Space counts visited work-tape
cells, excluding the read-only input and write-only output; retained accumulators are charged.
The invariant wrappers use the same pure prefix-fold rule, keeping their distinct resource
contracts separate from invariant propagation.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum`: cumulative
  computation and copying costs, with peak workspace bounds.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec`: an invariant
  supplies the cumulative cost and postcondition.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum`: stream a paired
  initial accumulator and bit list `(s₀, l)` on `encPair enc encBits` with cumulative round costs
  and workspace independent of `l.length`.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum_spec`: invariant
  wrapper for paired bit-list streaming folds.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`: stream `k` rounds
  of a state map from `(s, k)`, emitting per round, with cumulative round costs and workspace
  independent of `k`.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream`: the uniform-round
  specialization.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec`: an invariant
  supplies the bounds and a postcondition.
* `Turing.MultiTapeTM.ComputableTidilyInO.foldl_bits_finite`: a fixed finite-state fold takes
  linear time and constant work space, including a bound on its encoded final state.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.map_bits`: a bitwise map emits its output
  as it scans, in linear time and zero work space.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.reverse_bits`,
  `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_bits`,
  `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.dropLast_bits`,
  `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.getLast?_toList_bits`,
  `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.getLast?_bits`: linear-time zero-workspace
  bit-list reversal, unary length, prefix (`List.dropLast`), and last-bit (`List.getLast?.toList`,
  `List.getLast?`) primitives.

## References

Uses Christian Reitwiessner's `ComputableTidilyInTimeAndSpace.streamFold` from the
`crei/tidy-universal` branch; see the source marker in
`Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Stream a bit list with cumulative round costs. `R l i` includes the step, the current and next
encoded state lengths, and control. `Q` and `B` bound peak step workspace and encoded state size.
The input is scanned without copying; final output and tape restoration are charged too.
The constant is independent of the input, and the bounds need not be computable. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    {R : List Bool → ℕ → ℕ} {Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length), t ((l.take i).foldl step init, l[i]) +
      (enc ((l.take i).foldl step init)).length +
      (enc ((l.take (i + 1)).foldl step init)).length + 1 ≤ R l i)
    (hspace : ∀ l i (hi : i < l.length), s ((l.take i).foldl step init, l[i]) ≤ Q l)
    (hstate : ∀ l i, i ≤ l.length → (enc ((l.take i).foldl step init)).length ≤ B l) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * ((∑ i ∈ Finset.range l.length, R l i) + B l + 1))
      (fun l => c * (Q l + B l + 1)) := by
  obtain ⟨ci, hi⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := enc) init
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair enc encBool) (encOut := encBits) []
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold_sum
    (g := fun l => l.foldl step init) (encOut := enc)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    id (fun l => by simp) hi.computableTidilyInTimeAndSpace hstep
    he.computableTidilyInTimeAndSpace computableTidilyInTimeAndSpace_id
    (fun l => by simp [streamState])
    (roundCost := fun l i => (2 * ce + 4) * R l i) (sMax := Q)
    (lMax := fun l => B l + 1)
    (fun l i hi => by
      have hr := hcost l i hi
      have hR : 1 ≤ R l i := by lia
      have hm := Nat.mul_le_mul_left (2 * ce + 3) hR
      simp only [streamState, Function.const_apply, encBool_apply, List.length_singleton, id_eq]
      nlinarith)
    (fun l i hi => hspace l i hi)
    (fun l i hi => (hstate l i hi).trans (Nat.le_succ _))
    (fun _ _ _ => by simp)
  have hn (l : List Bool) : l.length ≤ ∑ i ∈ Finset.range l.length, R l i := by
    calc
      l.length = ∑ _i ∈ Finset.range l.length, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        have hr := hcost l i (Finset.mem_range.mp hi)
        lia
  refine ⟨c * (2 * ci + 2 * ce + 20), h.mono (fun l => ?_) (fun l => ?_)⟩
  · have hf := hstate l l.length le_rfl
    simp only [List.take_length] at hf
    simp only [id_eq, encBits_apply, streamState, List.take_length, Function.const_apply]
    rw [Nat.mul_assoc, ← Finset.mul_sum]
    apply Nat.mul_le_mul_left c
    change 2 * ci + 2 + (2 * (enc (l.foldl step init)).length + 4) + l.length +
      (2 * ce + 4) * (∑ i ∈ Finset.range l.length, R l i) + (B l + 1) + 1 ≤ _
    have hr := hn l
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith

/-- Stream a bit list through a tidy step computation. Each round charges the step and the stored
state, without copying the input list. `R`, `Q` and `B` bound the time of a round, its work space
and the encoded state size, respectively. The final output and tape restoration are charged too.
The constant is independent of the input; the three bounds need not be computable. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    {R Q B : List Bool → ℕ}
    (htime : ∀ l i (hi : i < l.length), t ((l.take i).foldl step init, l[i]) ≤ R l)
    (hspace : ∀ l i (hi : i < l.length), s ((l.take i).foldl step init, l[i]) ≤ Q l)
    (hstate : ∀ l i, i ≤ l.length → (enc ((l.take i).foldl step init)).length ≤ B l) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * (l.length * (R l + B l + 1) + B l + 1))
      (fun l => c * (Q l + B l + 1)) := by
  obtain ⟨c, h⟩ := hstep.foldl_bits_stream_sum init
    (R := fun l _ => R l + 2 * B l + 1) (Q := Q) (B := B)
    (fun l i hi => by
      have ht := htime l i hi
      have h₀ := hstate l i hi.le
      have h₁ := hstate l (i + 1) hi
      lia) hspace hstate
  refine ⟨c * 2, h.mono (fun l => ?_) (fun l => ?_)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    lia

/-- An invariant supplies cumulative computation and copying costs, peak workspace and a
postcondition. Each round's bound includes both the old and the new encoded state. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    (invariant : List Bool → ℕ → σ → Prop)
    (hbase : ∀ l, invariant l 0 init)
    (hpreserve : ∀ l i (hi : i < l.length) state, invariant l i state →
      invariant l (i + 1) (step state l[i]))
    {R : List Bool → ℕ → ℕ} {Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length) state, invariant l i state →
      t (state, l[i]) + (enc state).length + (enc (step state l[i])).length + 1 ≤ R l i ∧
        s (state, l[i]) ≤ Q l)
    (hsize : ∀ l i, i ≤ l.length → ∀ state, invariant l i state → (enc state).length ≤ B l) :
    (∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * ((∑ i ∈ Finset.range l.length, R l i) + B l + 1))
      (fun l => c * (Q l + B l + 1))) ∧
      ∀ l, invariant l l.length (l.foldl step init) := by
  have htrace (l : List Bool) :=
    List.foldl_take_invariant l step init (invariant l) (hbase l) (hpreserve l)
  exact ⟨hstep.foldl_bits_stream_sum init
    (fun l i hi => by
      simpa only [List.take_succ_eq_append_getElem hi, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using (hcost l i hi _ (htrace l i hi.le)).1)
    (fun l i hi => (hcost l i hi _ (htrace l i hi.le)).2)
    (fun l i hi => hsize l i hi _ (htrace l i hi)),
    fun l => by simpa using htrace l l.length le_rfl⟩

/-- An invariant supplies the streaming fold's resource bounds and postcondition. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    (invariant : List Bool → ℕ → σ → Prop)
    (hbase : ∀ l, invariant l 0 init)
    (hpreserve : ∀ l i (hi : i < l.length) state, invariant l i state →
      invariant l (i + 1) (step state l[i]))
    {R Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length) state, invariant l i state →
      t (state, l[i]) ≤ R l ∧ s (state, l[i]) ≤ Q l)
    (hsize : ∀ l i, i ≤ l.length → ∀ state, invariant l i state → (enc state).length ≤ B l) :
    (∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * (l.length * (R l + B l + 1) + B l + 1))
      (fun l => c * (Q l + B l + 1))) ∧
      ∀ l, invariant l l.length (l.foldl step init) := by
  obtain ⟨⟨c, h⟩, hpost⟩ := hstep.foldl_bits_stream_sum_spec init invariant hbase hpreserve
    (R := fun l _ => R l + 2 * B l + 1) (Q := Q) (B := B)
    (fun l i hi state hs => by
      have hc := hcost l i hi state hs
      have h₀ := hsize l i hi.le state hs
      have h₁ := hsize l (i + 1) hi _ (hpreserve l i hi state hs)
      exact ⟨by lia, hc.2⟩) hsize
  refine ⟨⟨c * 2, h.mono (fun l => ?_) (fun l => ?_)⟩, hpost⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    lia

/-- A fold with a fixed finite state type takes linear time and constant work space. The constant
may depend on the state type, its encoding and the transition function; this is not a uniform bound
for a family of growing state types. The encoded final state is bounded as well. -/
theorem ComputableTidilyInO.foldl_bits_finite {σ : Type} [Finite σ]
    (enc : σ ↪ List Bool) (step : σ → Bool → σ) (init : σ) :
    ComputableTidilyInO (fun l => l.foldl step init) encBits enc List.length (fun _ => 0) := by
  classical
  let := Fintype.ofFinite σ
  let b := Finset.univ.sup (fun s => (enc s).length)
  have hb (s : σ) : (enc s).length ≤ b :=
    Finset.le_sup (f := fun s => (enc s).length) (Finset.mem_univ s)
  obtain ⟨k, hk⟩ := computableInTimeAndSpace_of_finite
    (encIn := encPair enc encBool) (encOut := enc) (fun p : σ × Bool => step p.1 p.2)
  obtain ⟨c, h⟩ := hk.computableTidilyInTimeAndSpace.foldl_bits_stream init
    (R := fun _ => 2 * k + 2) (Q := fun _ => 0) (B := fun _ => b)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) (fun _ _ _ => hb _)
  refine ComputableTidilyInO.of_bounds h (c * (2 * k + 2 * b + 4) + b) ?_ ?_ ?_
  · intro l
    have hr : l.length * (2 * k + 2 + b + 1) + b + 1 ≤
        (2 * k + 2 * b + 4) * (l.length + 1) := by nlinarith
    exact (Nat.mul_le_mul_left c hr).trans (by nlinarith)
  · intro l
    nlinarith
  · intro l
    exact (hb _).trans (by simp)

/-- Emit a bitwise map directly, without a growing accumulator on a work tape. Unlike `InO`,
this numerical certificate does not include the emitted output in its space bound. -/
theorem ComputableTidilyInTimeAndSpace.map_bits (f : Bool → Bool) :
    ComputableTidilyInTimeAndSpace (List.map f) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  let transducer : Transducer Bool Unit :=
    ⟨(), fun _ b => ((), [f b]), fun _ => [], by simp, by simp⟩
  refine transducer.computableTidilyInTimeAndSpace ?_
  intro l
  induction l with
  | nil => rfl
  | cons b l ih => simpa [transducer, Transducer.run] using congrArg (List.cons (f b)) ih

/-- Stream a paired initial accumulator and bit list `(s₀, l)` on `encPair enc encBits` with
cumulative round costs. The framed initial accumulator `frame (enc s₀)` is copied once to the
state tape by `rawFrameReader`, and the remaining bits `l` are streamed directly from the input
tape without copying `l` onto work tapes, so workspace depends only on peak step workspace `Q` and
peak encoded accumulator length `B`. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    {R : σ × List Bool → ℕ → ℕ} {Q B : σ × List Bool → ℕ}
    (hcost : ∀ p i (hi : i < p.2.length), t ((p.2.take i).foldl step p.1, p.2[i]) +
      (enc ((p.2.take i).foldl step p.1)).length +
      (enc ((p.2.take (i + 1)).foldl step p.1)).length + 1 ≤ R p i)
    (hspace : ∀ p i (hi : i < p.2.length), s ((p.2.take i).foldl step p.1, p.2[i]) ≤ Q p)
    (hstate : ∀ p i, i ≤ p.2.length → (enc ((p.2.take i).foldl step p.1)).length ≤ B p) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun p : σ × List Bool => p.2.foldl step p.1)
      (encPair enc encBits) enc
      (fun p => c * ((∑ i ∈ Finset.range p.2.length, R p i) + B p + 1))
      (fun p => c * (Q p + B p + 1)) := by
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair enc encBool) (encOut := encBits) []
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun p : σ × List Bool => p.2.foldl step p.1)
    (encIn := encPair enc encBits) (encOut := enc)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    Prod.fst Prod.snd (fun p => by simp [encPair_apply])
    hstep he.computableTidilyInTimeAndSpace computableTidilyInTimeAndSpace_id
    (fun p => by simp [streamState])
    (roundCost := fun p i => (2 * ce + 4) * R p i) (sMax := Q)
    (lMax := fun p => B p + 1)
    (fun p i hi => by
      have hr := hcost p i hi
      have hR : 1 ≤ R p i := by lia
      have hm := Nat.mul_le_mul_left (2 * ce + 3) hR
      simp only [streamState, encBool_apply, List.length_singleton]
      nlinarith)
    (fun p i hi => hspace p i hi)
    (fun p i hi => (hstate p i hi).trans (Nat.le_succ _))
    (fun _ _ _ => by simp)
  have hn (p : σ × List Bool) : p.2.length ≤ ∑ i ∈ Finset.range p.2.length, R p i := by
    calc
      p.2.length = ∑ _i ∈ Finset.range p.2.length, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        have hr := hcost p i (Finset.mem_range.mp hi)
        lia
  refine ⟨c * (2 * ce + 20), h.mono (fun p => ?_) (fun p => ?_)⟩
  · have h₀ := hstate p 0 (Nat.zero_le _)
    have hf := hstate p p.2.length le_rfl
    simp only [List.take_zero, List.foldl_nil] at h₀
    simp only [List.take_length] at hf
    simp only [encPair_apply, length_frame, encBits_apply, List.length_append,
      streamState, List.take_length]
    rw [Nat.mul_assoc, ← Finset.mul_sum]
    apply Nat.mul_le_mul_left c
    change (2 * (enc (p.2.foldl step p.1)).length + 4) +
      ((2 * (enc p.1).length + 1) + p.2.length) +
      (2 * ce + 4) * (∑ i ∈ Finset.range p.2.length, R p i) + (B p + 1) + 1 ≤ _
    have hr := hn p
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith

/-- An invariant supplies cumulative computation and copying costs, peak workspace, and a
postcondition for a paired streaming fold over `(s₀, l) : σ × List Bool`. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum_spec {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    (invariant : σ × List Bool → ℕ → σ → Prop)
    (hbase : ∀ p, invariant p 0 p.1)
    (hpreserve : ∀ p i (hi : i < p.2.length) state, invariant p i state →
      invariant p (i + 1) (step state p.2[i]))
    {R : σ × List Bool → ℕ → ℕ} {Q B : σ × List Bool → ℕ}
    (hcost : ∀ p i (hi : i < p.2.length) state, invariant p i state →
      t (state, p.2[i]) + (enc state).length + (enc (step state p.2[i])).length + 1 ≤ R p i ∧
        s (state, p.2[i]) ≤ Q p)
    (hsize : ∀ p i, i ≤ p.2.length → ∀ state, invariant p i state → (enc state).length ≤ B p) :
    (∃ c, ComputableTidilyInTimeAndSpace (fun p : σ × List Bool => p.2.foldl step p.1)
      (encPair enc encBits) enc
      (fun p => c * ((∑ i ∈ Finset.range p.2.length, R p i) + B p + 1))
      (fun p => c * (Q p + B p + 1))) ∧
      ∀ p, invariant p p.2.length (p.2.foldl step p.1) := by
  have htrace (p : σ × List Bool) :=
    List.foldl_take_invariant p.2 step p.1 (invariant p) (hbase p) (hpreserve p)
  exact ⟨hstep.foldl_bits_pair_stream_sum
    (fun p i hi => by
      simpa only [List.take_succ_eq_append_getElem hi, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using (hcost p i hi _ (htrace p i hi.le)).1)
    (fun p i hi => (hcost p i hi _ (htrace p i hi.le)).2)
    (fun p i hi => hsize p i hi _ (htrace p i hi)),
    fun p => by simpa using htrace p p.2.length le_rfl⟩

/-- A fold whose step ignores its token iterates the state map, `j` times after `j` tokens. -/
theorem streamState_replicate {σ α : Type*} (f : σ → σ) (s : σ) (a : α) {k j : ℕ} (hj : j ≤ k) :
    streamState s (fun p : σ × α => f p.1) (List.replicate k a) j = f^[j] s := by
  simp only [streamState, List.take_replicate, Nat.min_eq_left hj, List.foldl_const,
    List.length_replicate]

/-- Stream `k` rounds of a state map `f` from `(s, k)` on `encPair enc encUnary`. Round `i` emits
`emit (f^[i] s)` directly to the output, and the final state is finished by `finish`. The unary
count is read from the input tape one bit per round and never copied, so workspace holds only the
current state and the callbacks. `R x i` charges round `i`: the step, the emission, and the current
and next encoded states; `Q` and `B` bound peak callback workspace and encoded state size. -/
theorem ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum {σ : Type} {enc : σ ↪ List Bool}
    {f : σ → σ} {emit finish : σ → List Bool} {tN sN tE sE tF sF : σ → ℕ}
    (hnext : ComputableTidilyInTimeAndSpace f enc enc tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit enc encBits tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish enc encBits tF sF)
    {R : σ × ℕ → ℕ → ℕ} {Q B : σ × ℕ → ℕ}
    (hcost : ∀ x i, i < x.2 → tN (f^[i] x.1) + tE (f^[i] x.1) + (enc (f^[i] x.1)).length +
      (enc (f^[i + 1] x.1)).length + 1 ≤ R x i)
    (hspace : ∀ x i, i < x.2 → sN (f^[i] x.1) + sE (f^[i] x.1) ≤ Q x)
    (hstate : ∀ x i, i ≤ x.2 → (enc (f^[i] x.1)).length ≤ B x) :
    ∃ c, ComputableTidilyInTimeAndSpace
      (fun x : σ × ℕ => ((List.range x.2).map fun i => emit (f^[i] x.1)).flatten ++
        finish (f^[x.2] x.1))
      (encPair enc encUnary) encBits
      (fun x => c * (tF (f^[x.2] x.1) + (∑ i ∈ Finset.range x.2, R x i) + B x + 1))
      (fun x => c * (sF (f^[x.2] x.1) + Q x + B x + 1)) := by
  -- each round reads its state from the stream state paired with the token bit
  obtain ⟨cfst, hfst⟩ := Internal.NormalForm.linear
    (PairEncoding.fst (enc₁ := enc) (enc₂ := encBool) (enc := encPair enc encBool))
  obtain ⟨cN, hN⟩ := hnext.comp_linear hfst
  obtain ⟨cE, hE⟩ := hemit.comp_linear hfst
  obtain ⟨D, hD⟩ : ∃ D, D = 6 * cfst + cN + cE + 2 := ⟨_, rfl⟩
  have hst (x : σ × ℕ) (j : ℕ) (hj : j ≤ x.2) :
      streamState x.1 (f ∘ Prod.fst) (List.replicate x.2 true) j = f^[j] x.1 :=
    streamState_replicate f x.1 true hj
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  have hsf := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun x : σ × ℕ => ((List.range x.2).map fun i => emit (f^[i] x.1)).flatten ++
      finish (f^[x.2] x.1))
    (encIn := encPair enc encUnary) (encOut := encBits)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    Prod.fst (fun x => List.replicate x.2 true) (fun x => by simp [encPair_apply, encUnary_apply])
    hN hE hfinish
    (fun x => by
      rw [streamEmit_eq, List.length_replicate, hst x x.2 le_rfl]
      simp only [encBits_apply]
      congr 2
      refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.mp hj
      simp [hj', hst x j hj'.le])
    (roundCost := fun x i => D * R x i) (sMax := fun x => D * (Q x + B x + 1))
    (lMax := fun x => B x + 1) ?_ ?_ ?_ (fun _ _ _ => by simp)
  · obtain ⟨c, h⟩ := hsf
    have hn (x : σ × ℕ) : x.2 ≤ ∑ i ∈ Finset.range x.2, R x i := by
      calc x.2 = ∑ _i ∈ Finset.range x.2, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => by
          have := hcost x i (Finset.mem_range.mp hi)
          omega
    refine ⟨c * (D + 4), h.mono (fun x => ?_) (fun x => ?_)⟩ <;>
      simp only [List.length_replicate, hst x x.2 le_rfl, ← Finset.mul_sum, Nat.mul_assoc] <;>
      refine Nat.mul_le_mul_left c ?_
    · have h₀ := hstate x 0 (Nat.zero_le _)
      have := hn x
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        Function.iterate_zero_apply] at h₀ ⊢
      nlinarith
    · nlinarith
  · intro x i hi
    have hi' : i < x.2 := by simpa using hi
    have hc := hcost x i hi'
    have hm := Nat.mul_le_mul_left (6 * cfst + cN + cE + 1)
      (show (enc (f^[i] x.1)).length + 1 ≤ R x i by omega)
    simp only [length_encPair, encBool_apply, List.length_singleton, List.getElem_replicate,
      hst x i hi'.le, hst x (i + 1) hi']
    subst hD
    nlinarith
  · intro x i hi
    have hi' : i < x.2 := by simpa using hi
    have hs := hspace x i hi'
    have hm := Nat.mul_le_mul_left (6 * cfst + cN + cE)
      (Nat.succ_le_succ (hstate x i hi'.le))
    simp only [length_encPair, encBool_apply, List.length_singleton, List.getElem_replicate,
      hst x i hi'.le]
    subst hD
    nlinarith
  · intro x i hi
    rw [hst x i (by simpa using hi)]
    exact (hstate x i (by simpa using hi)).trans (Nat.le_succ _)

/-- Reverse a bit list tidily in `2 * l.length + 2` steps and zero work-tape space, using the
two-state zero-work-tape primitive `Turing.MultiTapeTM.reverseInput`. -/
theorem ComputableTidilyInTimeAndSpace.reverse_bits :
    ComputableTidilyInTimeAndSpace List.reverse encBits encBits
      (fun l => 2 * l.length + 2) (fun _ => 0) :=
  computableTidilyInTimeAndSpace_reverse fun _ => rfl

/-- The length of a bit list, emitted in unary while scanning, in `4 * l.length + 8` steps and
zero work-tape space. -/
theorem ComputableTidilyInTimeAndSpace.length_bits :
    ComputableTidilyInTimeAndSpace List.length encBits encUnary
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := map_bits (fun _ => true)
  refine ⟨k, State, hfin, tm, fun l => ?_⟩
  have hmap : List.map (fun _ => true) l = encUnary l.length := by
    simp [encUnary_apply, List.map_const']
  exact hmap ▸ htm l

/-- Drop the last bit of a bit list (`List.dropLast`) tidily in `4 * l.length + 8` steps and zero
work-tape space, using a three-state (`Option Bool`) finite-state transducer that buffers one
lookahead symbol. -/
theorem ComputableTidilyInTimeAndSpace.dropLast_bits :
    ComputableTidilyInTimeAndSpace List.dropLast encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  let τ : Transducer Bool (Option Bool) :=
    { q₀ := none
      step
        | none, b => (some b, [])
        | some prev, b => (some b, [prev])
      final _ := []
      length_step_le q b := by cases q <;> simp
      length_final_le _ := by simp }
  have hrun (prev : Bool) (l : List Bool) :
      τ.run (some prev) l = (prev :: l).dropLast := by
    induction l generalizing prev with
    | nil => rfl
    | cons b l ih =>
      simpa only [τ, Transducer.run_cons, List.singleton_append,
        List.dropLast_cons_cons] using congrArg (List.cons prev) (ih b)
  refine τ.computableTidilyInTimeAndSpace ?_
  intro l
  cases l with
  | nil => rfl
  | cons b l =>
    simpa only [τ, Transducer.run_cons, List.nil_append, encBits_apply] using (hrun b l).symm

/-- The finite-state transducer that remembers the last bit read and ends with `final` of it. -/
private def lastBitT (final : Option Bool → List Bool) (hfinal : ∀ q, (final q).length ≤ 2) :
    Transducer Bool (Option Bool) where
  q₀ := none
  step _ b := (some b, [])
  final := final
  length_step_le _ _ := by simp
  length_final_le := hfinal

private lemma run_lastBitT (final : Option Bool → List Bool) (hfinal : ∀ q, (final q).length ≤ 2)
    (l : List Bool) :
    (lastBitT final hfinal).run (lastBitT final hfinal).q₀ l = final l.getLast? := by
  suffices ∀ q, (lastBitT final hfinal).run q l = final (l.getLast?.or q) from
    (this none).trans (by rw [Option.or_none])
  induction l with
  | nil => intro q; rfl
  | cons b l ih =>
    intro q
    rw [Transducer.run_cons, ih, List.getLast?_cons]
    cases l.getLast? <;> rfl

/-- Extract the last bit of a bit list as a 0-or-1-element list (`l.getLast?.toList`) tidily in
`4 * l.length + 8` steps and zero work-tape space. -/
theorem ComputableTidilyInTimeAndSpace.getLast?_toList_bits :
    ComputableTidilyInTimeAndSpace (fun l : List Bool => l.getLast?.toList) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) :=
  (lastBitT Option.toList fun q => by cases q <;> simp).computableTidilyInTimeAndSpace fun l =>
    (run_lastBitT Option.toList _ l).symm

/-- Extract the last bit of a bit list as an `Option Bool` (`l.getLast?`) tidily in
`4 * l.length + 8` steps and zero work-tape space. -/
theorem ComputableTidilyInTimeAndSpace.getLast?_bits :
    ComputableTidilyInTimeAndSpace (List.getLast? (α := Bool)) encBits (encOption encBool)
      (fun l => 4 * l.length + 8) (fun _ => 0) :=
  (lastBitT (encOption encBool) fun q => by cases q <;> simp).computableTidilyInTimeAndSpace
    fun l => (run_lastBitT (encOption encBool) _ l).symm

end Turing.MultiTapeTM


