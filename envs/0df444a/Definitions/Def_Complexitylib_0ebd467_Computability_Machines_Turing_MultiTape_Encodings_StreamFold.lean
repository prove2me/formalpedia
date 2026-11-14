-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_StreamFold
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_StreamFold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:06.404787+00:00
-- url     : https://prove2.me/theorems/3c47d023-c221-4da5-a114-acba16368266
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold — Streaming folds of tidily computable functions
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A list encoded as the concatenation of the *tokens* of its elements, each read by a finite-state
--   input reader, can be folded in one pass over the input. The fold keeps a state, starting with
--   `init l`; for each element `a` it moves from the state `s` to `next (s, a)` and emits `emit (s, a)`;
--   at the end it emits `finish` of the final state. Only the state and one element are ever held on
--   the work tapes.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.streamState`: the state of the fold after the first `j` elements.
--   * `Turing.MultiTapeTM.streamEmit`: the words the fold emits.
--   * `Turing.MultiTapeTM.rawFrameReader`: a two-state input reader that reads one framed word while
--     preserving its framing.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.transformsTapesAt_streamLoop_encoded`: a typed streaming phase, shared
--     by single-pass and multi-pass folds.
--   * `Turing.MultiTapeTM.transformsTapesAt_streamLoop_encoded_after`: a typed streaming phase
--     starting after a prefix on the input tape.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum_after`: streaming folds
--     after an initialization phase that writes the framed initial state and may move the input head
--     past a prefix, with cumulative round costs and peak workspace bounds.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum`: streaming folds with
--     cumulative computation and copying costs, and peak workspace bounds.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_pair_sum`: streaming folds whose
--     input begins with a framed initial state followed by encoded stream tokens.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold`: the uniform-round corollary.
--
--   The cumulative theorem generalizes Christian Reitwiessner's original encoding-layer proof.
--   The typed phase shares token decoding, callback adaptation and copying bounds with multi-pass
--   folds. `streamFold_sum_after` owns the machine and its resource proof once: `streamFold_sum`
--   computes the initial state from the whole input, `streamFold_pair_sum` reads it from a framed
--   input prefix, and the uniform-round corollary reuses the complete single-pass construction.
--
--   **Contents.** The module is published as a whole: 15 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_StreamFold`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Basic

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_StreamFold
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Streaming folds of tidily computable functions

A list encoded as the concatenation of the *tokens* of its elements, each read by a finite-state
input reader, can be folded in one pass over the input. The fold keeps a state, starting with
`init l`; for each element `a` it moves from the state `s` to `next (s, a)` and emits `emit (s, a)`;
at the end it emits `finish` of the final state. Only the state and one element are ever held on
the work tapes.

## Main definitions

* `Turing.MultiTapeTM.streamState`: the state of the fold after the first `j` elements.
* `Turing.MultiTapeTM.streamEmit`: the words the fold emits.
* `Turing.MultiTapeTM.rawFrameReader`: a two-state input reader that reads one framed word while
  preserving its framing.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_streamLoop_encoded`: a typed streaming phase, shared
  by single-pass and multi-pass folds.
* `Turing.MultiTapeTM.transformsTapesAt_streamLoop_encoded_after`: a typed streaming phase
  starting after a prefix on the input tape.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum_after`: streaming folds
  after an initialization phase that writes the framed initial state and may move the input head
  past a prefix, with cumulative round costs and peak workspace bounds.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum`: streaming folds with
  cumulative computation and copying costs, and peak workspace bounds.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_pair_sum`: streaming folds whose
  input begins with a framed initial state followed by encoded stream tokens.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold`: the uniform-round corollary.

The cumulative theorem generalizes Christian Reitwiessner's original encoding-layer proof.
The typed phase shares token decoding, callback adaptation and copying bounds with multi-pass
folds. `streamFold_sum_after` owns the machine and its resource proof once: `streamFold_sum`
computes the initial state from the whole input, `streamFold_pair_sum` reads it from a framed
input prefix, and the uniform-round corollary reuses the complete single-pass construction.
-/

namespace Turing.MultiTapeTM

universe u

variable {α σ : Type*}

/-- The state of a streaming fold after the first `j` elements of `l`. -/
@[expose] public def streamState (init : σ) (next : σ × α → σ) (l : List α) (j : ℕ) : σ :=
  (l.take j).foldl (fun s a => next (s, a)) init

/-- The words emitted by a streaming fold from the state `s` on the list `l`. -/
@[expose] public def streamEmit (next : σ × α → σ) (emit : σ × α → List Bool) :
    σ → List α → List Bool
  | _, [] => []
  | s, a :: l => emit (s, a) ++ streamEmit next emit (next (s, a)) l

@[simp]
public lemma streamState_zero (init : σ) (next : σ × α → σ) (l : List α) :
    streamState init next l 0 = init := rfl

public lemma streamState_succ (init : σ) (next : σ × α → σ) (l : List α) {j : ℕ}
    (hj : j < l.length) :
    streamState init next l (j + 1) = next (streamState init next l j, l[j]) := by
  rw [streamState, List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

/-- The emitted words, round by round. -/
public lemma streamEmit_eq (next : σ × α → σ) (emit : σ × α → List Bool) (s : σ) (l : List α) :
    streamEmit next emit s l = ((List.range l.length).map fun j =>
      (l[j]?.map fun a => emit (streamState s next l j, a)).getD []).flatten := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [streamEmit, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.flatten_cons]
    rfl

/-- The lengths of the tokens add up to the length of the input. -/
public lemma sum_length_getD (toks : List (List Bool)) :
    ∑ j ∈ Finset.range toks.length, (toks[j]?.getD []).length = toks.flatten.length := by
  induction toks with
  | nil => rfl
  | cons t toks ih => rw [List.length_cons, Finset.sum_range_succ']; simp [ih, Nat.add_comm]

-- upstream: candidate
/-- A streaming fold whose per-element callback emits nothing emits the empty word. -/
@[simp]
public lemma streamEmit_const_nil (next : σ × α → σ) (s : σ) (l : List α) :
    streamEmit next (fun _ => []) s l = [] := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => exact ih _

-- upstream: candidate
/-- An input reader that reads one framed word `[true, b₁, …, true, bₖ, false]` from the input
tape while keeping its framing, stopping immediately after the closing `false` (including on the
empty frame `[false]`). -/
@[expose] public def rawFrameReader : InputReader Bool Bool where
  q₀ := false
  step
    | false, true => (some true, some true)
    | false, false => (none, some false)
    | true, b => (some false, some b)

-- upstream: candidate
/-- `rawFrameReader` reads `frame w` from the start of `frame w ++ rest` in `(frame w).length`
steps, keeping the framing intact. -/
public theorem read_rawFrameReader (w rest : List Bool) :
    rawFrameReader.read false (frame w ++ rest) = (frame w, (frame w).length) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [frame_cons, List.cons_append, List.cons_append,
      rawFrameReader.read_cons_of_some (q' := true) _ rfl,
      rawFrameReader.read_cons_of_some (q' := false) _ rfl, ih]
    simp [rawFrameReader, Nat.add_assoc]

-- upstream: candidate
/-- A typed streaming phase starting after an input prefix `pre`. -/
public theorem transformsTapesAt_streamLoop_encoded_after {α σ : Type u} {Q SE SN : Type*} {K : ℕ}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool}
    {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN} {V N F : Fin K}
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (pre : List Bool) (s : σ) (l : List α) (next : σ × α → σ) (emit : σ × α → List Bool)
    {tE sE tN sN : σ × α → ℕ}
    (hE : ∀ p, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (encPair encS encA p))
      (fun _ ws ws' em => ws' = ws ∧ em = emit p) (tE p) (sE p))
    (hN : ∀ p, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (encPair encS encA p))
      (fun _ ws ws' em => ws' = Function.update ws N (frame (encS (next p))) ∧ em = [])
      (tN p) (sN p))
    {roundCost : ℕ → ℕ} {sMax lMax : ℕ}
    (hcost : ∀ j (hj : j < l.length),
      tE (streamState s next l j, l[j]) + tN (streamState s next l j, l[j]) +
        12 * ((encS (streamState s next l j)).length +
          (encS (streamState s next l (j + 1))).length + (encA l[j]).length) + 32 ≤ roundCost j)
    (hspace : ∀ j (hj : j < l.length),
      sE (streamState s next l j, l[j]) + sN (streamState s next l j, l[j]) ≤ sMax)
    (hstate : ∀ j ≤ l.length, (encS (streamState s next l j)).length ≤ lMax)
    (helem : ∀ j (hj : j < l.length), (encA l[j]).length ≤ lMax) :
    TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = pre ++ l.flatMap tok ∧ p.val = 1 + pre.length ∧
        ws = Function.update (fun _ => []) V (frame (encS s)))
      (fun input _ _ p' ws' em => input = pre ++ l.flatMap tok ∧
        p'.val = 1 + (pre ++ l.flatMap tok).length ∧
        ws' = Function.update (fun _ => []) V (frame (encS (streamState s next l l.length))) ∧
        em = streamEmit next emit s l)
      ((l.flatMap tok).length + (∑ j ∈ Finset.range l.length, roundCost j) + 1)
      (2 * K * (sMax + 16 * lMax + 4 * K + 26) + K) := by
  let st := streamState s next l
  let toks := l.map tok
  let cont (j : ℕ) : List Bool := (l[j]?.map encA).getD []
  let es (j : ℕ) : List Bool := (l[j]?.map fun a => emit (st j, a)).getD []
  let lift (f : σ × α → ℕ) (j : ℕ) : ℕ := (l[j]?.map fun a => f (st j, a)).getD 0
  have hlen : toks.length = l.length := List.length_map ..
  have hcont (j : ℕ) (hj : j < l.length) : cont j = encA l[j] := by
    simp [cont, List.getElem?_eq_getElem hj]
  have hlift (f : σ × α → ℕ) (j : ℕ) (hj : j < l.length) : lift f j = f (st j, l[j]) := by
    simp [lift, List.getElem?_eq_getElem hj]
  have htoks : ∀ t ∈ toks, t ≠ [] := by
    rintro t ht
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
    exact htok a
  have hread' : ∀ j (hj : j < toks.length), r.read r.q₀ (toks.flatten.drop
      ((toks.take j).flatten).length) = (cont j, toks[j].length) := by
    intro j hj
    rw [drop_flatten_take toks hj]
    simp [toks, hcont j (by omega), hread]
  have hE' : ∀ j < toks.length, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (st j)) ++ cont j))
      (fun _ ws ws' em => ws' = ws ∧ em = es j) (lift tE j) (lift sE j) := by
    intro j hj
    have hj' : j < l.length := by omega
    simpa [encPair_apply, hcont j hj', es, List.getElem?_eq_getElem hj', lift] using hE (st j, l[j])
  have hN' : ∀ j < toks.length, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (st j)) ++ cont j))
      (fun _ ws ws' em => ws' = Function.update ws N (frame (encS (st (j + 1)))) ∧ em = [])
      (lift tN j) (lift sN j) := by
    intro j hj
    have hj' : j < l.length := by omega
    simpa [encPair_apply, hcont j hj', lift, List.getElem?_eq_getElem hj', st,
      streamState_succ s next l hj'] using hN (st j, l[j])
  have h := transformsTapesAt_streamLoop_after (r := r) hVN hVF hNF pre toks htoks cont
    (fun j => frame (encS (st j))) es hread' hE' hN' (sR := sMax + 16 * lMax + 4 * K + 26) ?_
  · refine h.imp
      (fun _ _ _ h => by simpa only [toks, st, streamState_zero, List.flatMap_def] using h)
      ?_ ?_ le_rfl
    · intro input p ws p' ws' em _ hpost
      simpa only [hlen, toks, st, es, List.flatMap_def, streamEmit_eq] using hpost
    · have hs := Finset.sum_le_sum (s := Finset.range toks.length) fun j hj =>
        (show streamRoundTime toks cont
          (fun j => frame (encS (st j))) (lift tE) (lift tN) j + 1 ≤
          (toks[j]?.getD []).length + roundCost j from ?_)
      · simp only [Finset.sum_add_distrib] at hs ⊢
        rw [sum_length_getD] at hs
        simpa only [hlen, toks, ← List.flatMap_def] using Nat.add_le_add_right hs 1
      · have hj' : j < l.length := by simpa only [Finset.mem_range, hlen] using hj
        have hc := hcost j hj'
        simp only [streamRoundTime, hlift _ j hj', hcont j hj', List.length_append, length_frame]
        lia
  · intro j hj
    have hj' : j < l.length := by omega
    have hs := hspace j hj'
    have h₀ := hstate j hj'.le
    have h₁ := hstate (j + 1) hj'
    have ha := helem j hj'
    simp only [hlift _ j hj', hcont j hj', List.length_append, length_frame]
    lia

-- upstream: candidate
/-- A typed streaming phase on selected tapes. The state is framed, each token is decoded once,
and the callbacks receive the ordinary pair encoding. `roundCost` charges callback time and
copying of the current state, next state and decoded element. The phase leaves its final state
on tape `V` and the input cursor just past the last token, so another phase can consume them. -/
public theorem transformsTapesAt_streamLoop_encoded {α σ : Type u} {Q SE SN : Type*} {K : ℕ}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool}
    {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN} {V N F : Fin K}
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (s : σ) (l : List α) (next : σ × α → σ) (emit : σ × α → List Bool)
    {tE sE tN sN : σ × α → ℕ}
    (hE : ∀ p, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (encPair encS encA p))
      (fun _ ws ws' em => ws' = ws ∧ em = emit p) (tE p) (sE p))
    (hN : ∀ p, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (encPair encS encA p))
      (fun _ ws ws' em => ws' = Function.update ws N (frame (encS (next p))) ∧ em = [])
      (tN p) (sN p))
    {roundCost : ℕ → ℕ} {sMax lMax : ℕ}
    (hcost : ∀ j (hj : j < l.length),
      tE (streamState s next l j, l[j]) + tN (streamState s next l j, l[j]) +
        12 * ((encS (streamState s next l j)).length +
          (encS (streamState s next l (j + 1))).length + (encA l[j]).length) + 32 ≤ roundCost j)
    (hspace : ∀ j (hj : j < l.length),
      sE (streamState s next l j, l[j]) + sN (streamState s next l j, l[j]) ≤ sMax)
    (hstate : ∀ j ≤ l.length, (encS (streamState s next l j)).length ≤ lMax)
    (helem : ∀ j (hj : j < l.length), (encA l[j]).length ≤ lMax) :
    TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = l.flatMap tok ∧ p.val = 1 ∧
        ws = Function.update (fun _ => []) V (frame (encS s)))
      (fun input _ _ p' ws' em => input = l.flatMap tok ∧ p'.val = 1 + (l.flatMap tok).length ∧
        ws' = Function.update (fun _ => []) V (frame (encS (streamState s next l l.length))) ∧
        em = streamEmit next emit s l)
      ((l.flatMap tok).length + (∑ j ∈ Finset.range l.length, roundCost j) + 1)
      (2 * K * (sMax + 16 * lMax + 4 * K + 26) + K) := by
  simpa using transformsTapesAt_streamLoop_encoded_after r tok htok hread hVN hVF hNF [] s l
    next emit hE hN hcost hspace hstate helem

-- upstream: candidate
/-- **Streaming folds after an initialization phase.** The input `encIn x` is a prefix `pre x`
followed by the concatenated non-empty tokens `tok a` of the elements `elems x`, from each of which
the finite-state reader `r` reads `encA a`. On any selection `e` of tapes, the initializer `I e`
starts at the start of the input on blank tapes, writes the framed initial state
`frame (encS (init x))` to the selected tape `e (Fin.last kI)`, emits nothing and moves the input
head just past `pre x`, in time `tI x` and space `sI x` plus one cell for each unselected tape. If
`next`, `emit` and `finish` are tidily computable, and `g x` is encoded by the words emitted by the
fold over `elems x` followed by `finish` of its final state, then `g` is tidily computable. The
tokens are streamed directly from the input tape, which is never copied. The time bound sums the
initialization, the actual round costs `roundCost` (each round's computation, current and next
states, decoded element storage and control), finalization, input scanning and cleanup. Workspace
adds the initialization's to the peak callback workspace `sMax` and the stored-word bound `lMax`;
output is emitted directly and does not count as workspace. -/
public theorem ComputableTidilyInTimeAndSpace.streamFold_sum_after {α σ : Type u} {γ ε φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (pre : γ → List Bool) (elems : γ → List α)
    (hL : ∀ x, encIn x = pre x ++ (elems x).flatMap tok)
    {init : γ → σ} {next : σ × α → σ} {emit : σ × α → ε} {finish : σ → φ} {g : γ → ω}
    {kI : ℕ} {SI : Type} [Finite SI]
    (I : ∀ {K : ℕ}, (Fin (kI + 1) ↪ Fin K) → MultiTapeTM K Bool SI)
    {tI sI : γ → ℕ} {tN sN tE sE : σ × α → ℕ} {tF sF : σ → ℕ}
    (hinit : ∀ {K : ℕ} (e : Fin (kI + 1) ↪ Fin K) (x : γ), TransformsTapesAt (I e)
      (fun inp p ws => inp = encIn x ∧ p.val = 1 ∧ ws = fun _ => [])
      (fun _ _ _ p' ws' em => p'.val = 1 + (pre x).length ∧
        ws' = Function.update (fun _ => []) (e (Fin.last kI)) (frame (encS (init x))) ∧ em = [])
      (tI x) (sI x + (K - (kI + 1))))
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next (fun p => encE (emit p)) (init x) (elems x) ++
      encF (finish (streamState (init x) next (elems x) (elems x).length)))
    {roundCost : γ → ℕ → ℕ} {sMax lMax : γ → ℕ}
    (hcost : ∀ x j (hj : j < (elems x).length),
      tN (streamState (init x) next (elems x) j, (elems x)[j]) +
        tE (streamState (init x) next (elems x) j, (elems x)[j]) +
        (encS (streamState (init x) next (elems x) j)).length +
        (encS (streamState (init x) next (elems x) (j + 1))).length +
        (encA (elems x)[j]).length + 1 ≤ roundCost x j)
    (hsMax : ∀ x j (hj : j < (elems x).length),
      sN (streamState (init x) next (elems x) j, (elems x)[j]) +
        sE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ sMax x)
    (hS : ∀ x, ∀ j ≤ (elems x).length,
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tI x + tF (streamState (init x) next (elems x) (elems x).length) +
        (encIn x).length + (∑ j ∈ Finset.range (elems x).length, roundCost x j) + lMax x + 1))
      (fun x => c * (sI x + sF (streamState (init x) next (elems x) (elems x).length) + sMax x +
        lMax x + 1)) := by
  -- the framed next state, and finalization from the framed final state
  obtain ⟨cfr, hfr⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := id) (encIn := encS)
    (encOut := encFramed encS) fun _ => rfl
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cN, hN'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hnext
  obtain ⟨cuf, huf⟩ := ComputableTidilyInLinearTimeAndSpace.of_unframe (f := id)
    (encIn := encFramed encS) (encOut := encS) fun s => by simp
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cF, hF'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfinish huf
  obtain ⟨kE, SE, _, tmE, htmE⟩ := hemit
  obtain ⟨kN, SN, _, tmN, htmN⟩ := hN'
  obtain ⟨kF, SF, _, tmF, htmF⟩ := hF'
  -- the tapes: those of the machines, then the state `V`, the next state `N` and a flag `F`
  obtain ⟨M, hM⟩ : ∃ M, M = kI + kE + kN + kF + 8 := ⟨_, rfl⟩
  let V : Fin (M + 3) := ⟨M, by omega⟩
  let N : Fin (M + 3) := ⟨M + 1, by omega⟩
  let F : Fin (M + 3) := ⟨M + 2, by omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (K := M + 3) (by omega) (Fin.last kI) V
  obtain ⟨eE, heE⟩ := exists_embedding_eq (K := M + 3) (by omega) (Fin.natAdd kE (0 : Fin 2)) V
  obtain ⟨eN, heN, heN'⟩ := exists_embedding_eq₂ (K := M + 3) (by omega)
    (i := Fin.natAdd (kN + 1) (0 : Fin 2)) (o := (Fin.last kN).castAdd 2)
    (by simp [Fin.ext_iff]) hVN
  obtain ⟨eF, heF⟩ := exists_embedding_eq (K := M + 3) (by omega) (Fin.natAdd kF (0 : Fin 2)) V
  refine ⟨(40 * M + 200) * (cfr + cN + cuf + cF + M + 100), _, _, inferInstance,
    streamTM r (I eI) ((tmE.inputFromWord true).extendTapes eE)
      ((tmN.onWords true).extendTapes eN) ((tmF.inputFromWord true).extendTapes eF)
      V N F hVN hVF hNF, fun x => ?_⟩
  set l := elems x with hl
  set n := l.length with hn
  let st := streamState (init x) next l
  set L := lMax x with hLdef
  have hSj (j : ℕ) (hj : j ≤ n) : (encS (st j)).length ≤ L := hS x j hj
  have hI := hinit eI x
  rw [heI] at hI
  have hE := fun p => (htmE p).inputFromWord_extendTapes true heE
  have hN := fun p => (htmN p).onWords_extendTapes true heN heN'
  have hloop := transformsTapesAt_streamLoop_encoded_after r tok htok hread hVN hVF hNF (pre x)
    (init x) l next (fun p => encE (emit p)) hE hN
    (roundCost := fun j => (cfr + cN + 60) * roundCost x j)
    (sMax := sMax x + (cfr + cN + 10 * M + 40) * (L + 1)) (lMax := L) ?_ ?_ (hS x) (hA x)
  · simp only [← Finset.mul_sum] at hloop
    rw [← hL x] at hloop
    have h := computesTidily_streamTM_after (r := r) hVN hVF hNF (encIn x) (pre x)
      (frame (encS (init x))) (frame (encS (st n)))
      (streamEmit next (fun p => encE (emit p)) (init x) l) (encF (finish (st n)))
      hI hloop ((htmF (st n)).inputFromWord_extendTapes true heF)
    rw [hg x]
    have hSn : (encS (st n)).length ≤ L := hSj n le_rfl
    set D := cfr + cN + cuf + cF + M + 100 with hD
    refine h.mono ?_ ?_
    · simp only [id_eq, encFramed_apply, length_frame, st] at hSn ⊢
      rw [← hl, ← hn, ← hLdef]
      clear_value D L
      have hD1 : 1 ≤ D := by omega
      have f₂ := Nat.mul_le_mul (show cuf ≤ D by omega)
        (show 2 * (encS (streamState (init x) next l n)).length + 1 + 1 ≤ 2 * (L + 1) by omega)
      have f₃ := Nat.mul_le_mul (show cF ≤ D by omega) (Nat.add_le_add_right hSn 1)
      have f₄ := Nat.mul_le_mul_right (∑ j ∈ Finset.range n, roundCost x j)
        (show cfr + cN + 60 ≤ D by lia)
      have f₅ := Nat.mul_le_mul_right (tI x + tF (streamState (init x) next l n) +
        (encIn x).length + (∑ j ∈ Finset.range n, roundCost x j) + L + 1)
        (show 26 * D ≤ (40 * M + 200) * D from Nat.mul_le_mul_right _ (by omega))
      have f₆ := Nat.le_mul_of_pos_left (tI x) hD1
      have f₇ := Nat.le_mul_of_pos_left (tF (streamState (init x) next l n)) hD1
      have f₈ := Nat.le_mul_of_pos_left (encIn x).length hD1
      have f₉ := Nat.mul_le_mul_right (L + 1) (show 20 ≤ D by omega)
      have hlen : ((elems x).flatMap tok).length ≤ (encIn x).length := by
        rw [hL x, List.length_append]
        omega
      have f₁₀ : ((elems x).flatMap tok).length ≤ D * (encIn x).length := hlen.trans f₈
      have z₁ := Nat.zero_le (D * L)
      have z₂ := Nat.zero_le (D * ∑ j ∈ Finset.range n, roundCost x j)
      ring_nf at f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ z₁ ⊢
      linarith
    · simp only [id_eq, encFramed_apply, length_frame, st] at hSn ⊢
      rw [← hl, ← hn, ← hLdef]
      have hpeak : sMax x + (cfr + cN + 10 * M + 40) * (L + 1) + 16 * L + 4 * (M + 3) + 26 ≤
          sMax x + (cfr + cN + 20 * M + 100) * (L + 1) := by nlinarith
      clear_value D L
      have hD1 : 1 ≤ D := by omega
      have hED : cfr + cN + 20 * M + 100 ≤ 20 * D := by omega
      have g₁ := Nat.mul_le_mul_left (2 * (M + 3)) hpeak
      have g₂ : 2 * (M + 3) * ((cfr + cN + 20 * M + 100) * (L + 1)) ≤
          (40 * M + 120) * (D * (L + 1)) :=
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hED)).trans_eq (by ring)
      have g₃ : 2 * (M + 3) * sMax x ≤ (40 * M + 200) * D * sMax x :=
        Nat.mul_le_mul_right _ ((show 2 * (M + 3) ≤ 40 * M + 200 by omega).trans
          (Nat.le_mul_of_pos_right _ hD1))
      have g₄ : sI x ≤ (40 * M + 200) * D * sI x :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hD1)
      have g₅ : sF (streamState (init x) next l n) ≤
          (40 * M + 200) * D * sF (streamState (init x) next l n) :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hD1)
      have g₇ := Nat.mul_le_mul (show cuf ≤ D by omega)
        (show 2 * (encS (streamState (init x) next l n)).length + 1 + 1 ≤ 2 * (L + 1) by omega)
      have g₈ := Nat.mul_le_mul (show cF ≤ D by omega) (Nat.add_le_add_right hSn 1)
      have q₂ : L + 1 ≤ D * (L + 1) := Nat.le_mul_of_pos_left _ hD1
      have : kI ≤ M := by omega
      have : kF ≤ M := by omega
      have : M ≤ D := by omega
      have hd₁ : M + 3 - (kI + 1) ≤ M + 2 := by omega
      have hd₂ : M + 3 - (kF + 2) ≤ M + 1 := by omega
      generalize M + 3 - (kI + 1) = d₁ at hd₁ ⊢
      generalize M + 3 - (kF + 2) = d₂ at hd₂ ⊢
      have z₁ := Nat.zero_le (D * L)
      ring_nf at g₁ g₂ g₃ g₄ g₅ g₇ g₈ q₂ z₁ ⊢
      linarith
  · intro j hj
    have ht := hcost x j hj
    have hnext : next (st j, l[j]) = st (j + 1) := (streamState_succ _ _ _ hj).symm
    have hsize : (encS (st (j + 1))).length + 1 ≤ roundCost x j := by lia
    have hm₁ := Nat.mul_le_mul_left cfr hsize
    have hm₂ := Nat.mul_le_mul_left cN hsize
    dsimp only [st, l] at hnext hm₁ hm₂ ⊢
    simp only [Function.comp_apply, id_eq, encFramed_apply, hnext, length_frame]
    linarith only [ht, hm₁, hm₂]
  · intro j hj
    have h₀ := hSj j hj.le
    have h₁ := hSj (j + 1) hj
    have ha := hA x j hj
    have hs := hsMax x j hj
    have hnext : next (st j, l[j]) = st (j + 1) := (streamState_succ _ _ _ hj).symm
    have hm₁ := Nat.mul_le_mul_left cfr (Nat.add_le_add_right h₁ 1)
    have hm₂ := Nat.mul_le_mul_left cN (Nat.add_le_add_right h₁ 1)
    dsimp only [st, l] at hnext hm₁ hm₂ h₀ h₁ ⊢
    simp only [← hLdef] at ha
    simp only [Function.comp_apply, id_eq, encFramed_apply, hnext, length_frame,
      encPair_apply, List.length_append]
    have : kE ≤ M := by omega
    have : kN ≤ M := by omega
    have : M + 3 - (kE + 2) ≤ M + 1 := by omega
    have : M + 3 - (kN + 1 + 2) ≤ M := by omega
    have := Nat.zero_le (M * L)
    linarith

-- upstream: candidate
-- vendored: generalize the original proof to sum actual round costs; the machine and resource
-- proof are shared with `streamFold_sum_after`.
/-- **Streaming folds with cumulative round costs.** The input `x` is encoded by concatenating the
non-empty tokens `tok a` of the elements `elems x`, from each of which the finite-state reader `r`
reads `encA a`. If `init`, `next`, `emit` and `finish` are tidily computable, and `g x` is encoded
by the words emitted by the fold over `elems x` followed by `finish` of its final state, then `g`
is tidily computable. The time bound sums `roundCost`, including each round's computation, current
and next states, decoded element storage and control. Initialization, finalization, input scanning
and cleanup are charged separately. `sMax` and `lMax` bound peak callback workspace and stored
words; output is emitted directly and does not count as workspace. -/
public theorem ComputableTidilyInTimeAndSpace.streamFold_sum {α σ : Type u} {γ ε φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (elems : γ → List α) (hL : ∀ x, encIn x = (elems x).flatMap tok)
    {init : γ → σ} {next : σ × α → σ} {emit : σ × α → ε} {finish : σ → φ} {g : γ → ω}
    {tI sI : γ → ℕ} {tN sN tE sE : σ × α → ℕ} {tF sF : σ → ℕ}
    (hinit : ComputableTidilyInTimeAndSpace init encIn encS tI sI)
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next (fun p => encE (emit p)) (init x) (elems x) ++
      encF (finish (streamState (init x) next (elems x) (elems x).length)))
    {roundCost : γ → ℕ → ℕ} {sMax lMax : γ → ℕ}
    (hcost : ∀ x j (hj : j < (elems x).length),
      tN (streamState (init x) next (elems x) j, (elems x)[j]) +
        tE (streamState (init x) next (elems x) j, (elems x)[j]) +
        (encS (streamState (init x) next (elems x) j)).length +
        (encS (streamState (init x) next (elems x) (j + 1))).length +
        (encA (elems x)[j]).length + 1 ≤ roundCost x j)
    (hsMax : ∀ x j (hj : j < (elems x).length),
      sN (streamState (init x) next (elems x) j, (elems x)[j]) +
        sE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ sMax x)
    (hS : ∀ x, ∀ j ≤ (elems x).length,
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tI x + tF (streamState (init x) next (elems x) (elems x).length) +
        (encIn x).length + (∑ j ∈ Finset.range (elems x).length, roundCost x j) + lMax x + 1))
      (fun x => c * (sI x + sF (streamState (init x) next (elems x) (elems x).length) + sMax x +
        lMax x + 1)) := by
  -- the initial state is computed from the whole input and framed onto the selected tape
  obtain ⟨cfr, hfr⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := id) (encIn := encS)
    (encOut := encFramed encS) fun _ => rfl
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cI, hI'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hinit
  obtain ⟨kI, SI, _, tmI, htmI⟩ := hI'
  obtain ⟨C, hC⟩ : ∃ C, C = cfr + cI + 6 := ⟨_, rfl⟩
  have hsum := streamFold_sum_after r tok htok hread (fun _ => []) elems hL
    (fun e => tmI.outputToWord.extendTapes e) (tI := fun x => tI x + C * (lMax x + 1))
    (sI := fun x => sI x + C * (lMax x + 1) + kI) (fun e x => ?_)
    hnext hemit hfinish hg hcost hsMax hS hA
  · obtain ⟨c, h⟩ := hsum
    refine ⟨c * (C + kI + 1), h.mono (fun x => ?_) (fun x => ?_)⟩ <;> rw [Nat.mul_assoc] <;>
      refine Nat.mul_le_mul_left c ?_
    · generalize tI x = a, tF (streamState (init x) next (elems x) (elems x).length) = b,
        (encIn x).length = e, ∑ j ∈ Finset.range (elems x).length, roundCost x j = s, lMax x = L
      nlinarith [Nat.mul_le_mul_left C (show L + 1 ≤ a + b + e + s + L + 1 by omega),
        Nat.zero_le (kI * (a + b + e + s + L + 1))]
    · generalize sI x = a, sF (streamState (init x) next (elems x) (elems x).length) = b,
        sMax x = s, lMax x = L
      nlinarith [Nat.mul_le_mul_left C (show L + 1 ≤ a + b + s + L + 1 by omega),
        Nat.mul_le_mul_left kI (show 1 ≤ a + b + s + L + 1 by omega)]
  · have h₀ : (encS (init x)).length + 1 ≤ lMax x + 1 :=
      Nat.succ_le_succ (hS x 0 (Nat.zero_le _))
    have h₁ := Nat.mul_le_mul_left cfr h₀
    have h₂ := Nat.mul_le_mul_left cI h₀
    refine ((htmI x).outputToWord_onTape rfl).transformsTapesAt_eq.imp (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ _ ⟨_, hp, hws, he⟩ => ⟨hp, by simpa using hws, he⟩) ?_ ?_ <;>
    · simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hC]
      nlinarith

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: derived from `streamFold_sum` to share the machine and resource proof.
/-- **Streaming folds are tidily computable.** The input `x` is encoded by concatenating the non-
empty tokens `tok a` of the elements `elems x`, from each of which the finite-state reader `r`
reads `encA a`. If `init`, `next`, `emit` and `finish` are tidily computable, and `g x` is encoded
by the words emitted by the fold over `elems x` followed by `finish` of its final state, then `g`
is tidily computable. Its time is linear in the input plus the rounds. Workspace uses peak bounds
on states, elements and callbacks. The bounds `tMax`, `sMax` and `lMax` bound the time and space
of a round and the lengths of the states and elements. -/
public theorem ComputableTidilyInTimeAndSpace.streamFold {α σ : Type u} {γ ε φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (elems : γ → List α) (hL : ∀ x, encIn x = (elems x).flatMap tok)
    {init : γ → σ} {next : σ × α → σ} {emit : σ × α → ε} {finish : σ → φ} {g : γ → ω}
    {tI sI : γ → ℕ} {tN sN tE sE : σ × α → ℕ} {tF sF : σ → ℕ}
    (hinit : ComputableTidilyInTimeAndSpace init encIn encS tI sI)
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next (fun p => encE (emit p)) (init x) (elems x) ++
      encF (finish (streamState (init x) next (elems x) (elems x).length)))
    {tMax sMax lMax : γ → ℕ}
    (htMax : ∀ x j (hj : j < (elems x).length),
      tN (streamState (init x) next (elems x) j, (elems x)[j]) +
        tE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ tMax x)
    (hsMax : ∀ x j (hj : j < (elems x).length),
      sN (streamState (init x) next (elems x) j, (elems x)[j]) +
        sE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ sMax x)
    (hS : ∀ x, ∀ j ≤ (elems x).length,
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tI x + tF (streamState (init x) next (elems x) (elems x).length) +
        (encIn x).length + (elems x).length * (tMax x + lMax x + 1) + lMax x + 1))
      (fun x => c * (sI x + sF (streamState (init x) next (elems x) (elems x).length) + sMax x +
        lMax x + 1)) := by
  obtain ⟨c, h⟩ := streamFold_sum r tok htok hread elems hL hinit hnext hemit hfinish hg
    (roundCost := fun x _ => tMax x + 3 * lMax x + 1) (sMax := sMax) (lMax := lMax)
    (fun x j hj => by
      have ht := htMax x j hj
      have h₀ := hS x j hj.le
      have h₁ := hS x (j + 1) hj
      have ha := hA x j hj
      lia) hsMax hS hA
  refine ⟨c * 3, h.mono (fun x => ?_) (fun x => ?_)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    lia

-- upstream: candidate
/-- **Streaming folds from a framed initial state prefix.** When `encIn x` consists of the framed
initial state `frame (encS (init x))` followed directly by the concatenated tokens of `elems x`
(for example, on `encPair encS encBits` or `encPair encS encUnary`), `appendRead rawFrameReader V`
copies the framed initial state onto tape `V` and leaves the input cursor at the start of the
token stream, so the tokens are streamed directly from the input tape without copying the remainder
of the input onto work tapes. -/
public theorem ComputableTidilyInTimeAndSpace.streamFold_pair_sum {α σ : Type u} {γ ε φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (init : γ → σ) (elems : γ → List α)
    (hL : ∀ x, encIn x = frame (encS (init x)) ++ (elems x).flatMap tok)
    {next : σ × α → σ} {emit : σ × α → ε} {finish : σ → φ} {g : γ → ω}
    {tN sN tE sE : σ × α → ℕ} {tF sF : σ → ℕ}
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next (fun p => encE (emit p)) (init x) (elems x) ++
      encF (finish (streamState (init x) next (elems x) (elems x).length)))
    {roundCost : γ → ℕ → ℕ} {sMax lMax : γ → ℕ}
    (hcost : ∀ x j (hj : j < (elems x).length),
      tN (streamState (init x) next (elems x) j, (elems x)[j]) +
        tE (streamState (init x) next (elems x) j, (elems x)[j]) +
        (encS (streamState (init x) next (elems x) j)).length +
        (encS (streamState (init x) next (elems x) (j + 1))).length +
        (encA (elems x)[j]).length + 1 ≤ roundCost x j)
    (hsMax : ∀ x j (hj : j < (elems x).length),
      sN (streamState (init x) next (elems x) j, (elems x)[j]) +
        sE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ sMax x)
    (hS : ∀ x, ∀ j ≤ (elems x).length,
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tF (streamState (init x) next (elems x) (elems x).length) +
        (encIn x).length + (∑ j ∈ Finset.range (elems x).length, roundCost x j) + lMax x + 1))
      (fun x => c * (sF (streamState (init x) next (elems x) (elems x).length) + sMax x +
        lMax x + 1)) := by
  -- the framed initial state is read from the input prefix, leaving the cursor on the tokens
  have hsum := streamFold_sum_after r tok htok hread (fun x => frame (encS (init x))) elems
    hL (kI := 0) (fun e => appendRead rawFrameReader (e (Fin.last 0)))
    (tI := fun x => 2 * (frame (encS (init x))).length + 4)
    (sI := fun x => (frame (encS (init x))).length + 2) (fun e x => ?_)
    hnext hemit hfinish hg hcost hsMax hS hA
  · obtain ⟨c, h⟩ := hsum
    refine ⟨c * 5, h.mono (fun x => ?_) (fun x => ?_)⟩
    · have hpre : (frame (encS (init x))).length ≤ (encIn x).length := by
        rw [hL x, List.length_append]
        omega
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left c (by omega)
    · have h₀ : (encS (init x)).length ≤ lMax x := hS x 0 (Nat.zero_le _)
      simp only [length_frame]
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left c (by omega)
  · have hread_init : rawFrameReader.read rawFrameReader.q₀ ((encIn x).drop 0) =
        (frame (encS (init x)), (frame (encS (init x))).length) := by
      rw [List.drop_zero, hL x]
      exact read_rawFrameReader (encS (init x)) ((elems x).flatMap tok)
    have hraw := transformsTapesAt_appendRead rawFrameReader (e (Fin.last 0)) (encIn x) 1
      (by simp) []
    simp only [Fin.val_one, Nat.sub_self, hread_init, List.length_nil, List.nil_append] at hraw
    refine hraw.imp (fun _ _ ws ⟨hin, hp, hws⟩ => ⟨hin, hp, by simp [hws]⟩) ?_ (by omega) le_rfl
    rintro _ _ ws p' ws' em ⟨_, _, rfl⟩ ⟨hp', hws', hem⟩
    exact ⟨hp', hws', hem⟩

end Turing.MultiTapeTM


