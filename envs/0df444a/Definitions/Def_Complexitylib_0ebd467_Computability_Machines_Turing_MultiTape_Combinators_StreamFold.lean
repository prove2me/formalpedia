-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_StreamFold
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_StreamFold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:09.568267+00:00
-- url     : https://prove2.me/theorems/144db5ed-2eb3-4f30-9559-67c54359134c
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.StreamFold — Streaming folds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.StreamFold` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A streaming fold reads its input once, from left to right, one token at a time. It keeps a state
--   on a work tape; for each token it appends the token's content to the state, computes the next
--   state from the result and emits a word to the output. The input is never copied, so a round costs
--   time and space in the size of the state and the token only.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.frozenRound`: the part of a round that does not use the input.
--   * `Turing.MultiTapeTM.streamTM`: initialization, the loop of rounds, finalization and cleanup.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.transformsTapes_frozenRound`: the specification of `frozenRound`.
--   * `Turing.MultiTapeTM.transformsTapesAt_streamLoop_after`: the loop of rounds, started just past an
--     input prefix; `transformsTapesAt_streamLoop` is its empty-prefix case.
--   * `Turing.MultiTapeTM.computesTidily_streamTM_after`: the tidy assembly of `streamTM` from an
--     initializer that may move the input head past a prefix; `computesTidily_streamTM` is the case of
--     an initializer that leaves the input head at the start.
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_StreamFold`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/StreamFold.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_CopyWord
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ReadInput
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_WhileInput
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Fin_Tuple
import Mathlib.Tactic.FinCases

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.StreamFold` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Streaming folds

A streaming fold reads its input once, from left to right, one token at a time. It keeps a state
on a work tape; for each token it appends the token's content to the state, computes the next
state from the result and emits a word to the output. The input is never copied, so a round costs
time and space in the size of the state and the token only.

## Main definitions

* `Turing.MultiTapeTM.frozenRound`: the part of a round that does not use the input.
* `Turing.MultiTapeTM.streamTM`: initialization, the loop of rounds, finalization and cleanup.

## Main results

* `Turing.MultiTapeTM.transformsTapes_frozenRound`: the specification of `frozenRound`.
* `Turing.MultiTapeTM.transformsTapesAt_streamLoop_after`: the loop of rounds, started just past an
  input prefix; `transformsTapesAt_streamLoop` is its empty-prefix case.
* `Turing.MultiTapeTM.computesTidily_streamTM_after`: the tidy assembly of `streamTM` from an
  initializer that may move the input head past a prefix; `computesTidily_streamTM` is the case of
  an initializer that leaves the input head at the start.
-/

namespace Turing.MultiTapeTM

variable {m K : ℕ} {Symbol S : Type*}

/-! ### Specifications on selected tapes -/

/-- An embedding of `Fin m` into a larger `Fin K` sending `i` to `a`. -/
public theorem exists_embedding_eq (h : m ≤ K) (i : Fin m) (a : Fin K) :
    ∃ e : Fin m ↪ Fin K, e i = a :=
  ⟨(Fin.castLEEmb h).trans (Equiv.swap (Fin.castLE h i) a).toEmbedding, by simp⟩

/-- An embedding of `Fin m` into a larger `Fin K` sending `i` to `a` and `o` to `b`. -/
public theorem exists_embedding_eq₂ (h : m ≤ K) {i o : Fin m} (hio : i ≠ o) {a b : Fin K}
    (hab : a ≠ b) : ∃ e : Fin m ↪ Fin K, e i = a ∧ e o = b := by
  obtain ⟨e, he⟩ := exists_embedding_eq h i a
  refine ⟨e.trans (Equiv.swap (e o) b).toEmbedding, ?_, by simp⟩
  have hoa : e o ≠ a := fun h => hio (e.injective (h.trans he.symm)).symm
  simp [he, Equiv.swap_apply_of_ne_of_ne hoa.symm hab]

/-! ### The part of a round that does not use the input -/

section Frozen

variable {SE SN : Type*} {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN}
  {V N F : Fin K}

/-- The three tapes `V`, `N`, `F` of `copyWord`: target, source and flag. -/
public def threeTapes (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :
    Fin (0 + 1 + 2) ↪ Fin K :=
  ⟨![V, N, F], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

/-- Emit with `E` from the word on tape `V`, write the next state to tape `N` with `Nm`, and move
it to tape `V`, using tape `F` to flag the left end of the word. -/
public noncomputable def frozenRound (E : MultiTapeTM K Bool SE) (Nm : MultiTapeTM K Bool SN)
    (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  E.seq (Nm.seq (((clearWork Bool).extendTapes (tapeEmb V)).seq
    ((copyWord (threeTapes V N F hVN hVF hNF) true).seq
      ((clearWork Bool).extendTapes (tapeEmb N)))))

open Sequential in
/-- `frozenRound` takes the word `w` on tape `V` and every other tape blank to `next` on tape `V`
and every other tape blank, emitting `emit`, if `E` emits `emit` from `w` and `Nm` writes `next`
to tape `N`. -/
public theorem transformsTapes_frozenRound (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    {w emit next : List Bool} {tE sE tN sN : ℕ}
    (hE : TransformsTapes E (fun _ ws => ws = Function.update (fun _ => []) V w)
      (fun _ ws ws' em => ws' = ws ∧ em = emit) tE sE)
    (hN : TransformsTapes Nm (fun _ ws => ws = Function.update (fun _ => []) V w)
      (fun _ ws ws' em => ws' = Function.update ws N next ∧ em = []) tN sN) :
    TransformsTapes (frozenRound E Nm V N F hVN hVF hNF)
      (fun _ ws => ws = Function.update (fun _ => []) V w)
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V next ∧ em = emit)
      (tE + (tN + (3 * (w.length + 1) + ((3 * next.length + 10) + 3 * (next.length + 1)))))
      (sE + (sN + ((w.length + 1 + K) + ((4 * next.length + K + 15) +
        (next.length + 1 + K))))) := by
  set W₀ := Function.update (fun _ => ([] : List Bool)) V w
  set W₁ := Function.update W₀ N next
  set W₂ := Function.update W₁ V []
  set W₃ := Function.update W₂ V next
  have hW₄ : Function.update W₃ N [] = Function.update (fun _ => []) V next := by
    funext l
    simp only [W₃, W₂, W₁, W₀, Function.update_apply]
    split_ifs <;> simp_all
  have h₀ : TransformsTapes E (fun _ ws => ws = W₀) (fun _ _ ws' em => ws' = W₀ ∧ em = emit)
      tE sE := hE.imp (fun _ _ h => h) (fun _ _ _ _ hws ⟨h, he⟩ => ⟨h.trans hws, he⟩) le_rfl le_rfl
  have h₁ : TransformsTapes Nm (fun _ ws => ws = W₀) (fun _ _ ws' em => ws' = W₁ ∧ em = [])
      tN sN := hN.imp (fun _ _ h => h) (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws], he⟩)
      le_rfl le_rfl
  have h₂ : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb V)) (fun _ ws => ws = W₁)
      (fun _ _ ws' em => ws' = W₂ ∧ em = []) (3 * (w.length + 1)) (w.length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb V w).imp (fun _ _ h => by simp [h, W₁, W₀, hVN])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws], he⟩) le_rfl le_rfl
  have h₃ := (transformsTapes_copyWord (threeTapes V N F hVN hVF hNF) true next).imp
    (P' := fun _ ws => ws = W₂) (Q' := fun _ _ ws' em => ws' = W₃ ∧ em = [])
    (fun _ _ h => by
      subst h
      change W₂ N = next ∧ W₂ V = [] ∧ W₂ F = []
      simp [W₂, W₁, W₀, hVN.symm, hVF.symm, hNF.symm])
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws]; rfl, he⟩) le_rfl le_rfl
  have h₄ : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb N)) (fun _ ws => ws = W₃)
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V next ∧ em = [])
      (3 * (next.length + 1)) (next.length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb N next).imp
      (fun _ _ h => by simp [h, W₃, W₂, W₁, hVN.symm])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, hW₄], he⟩) le_rfl le_rfl
  refine (h₀.seq_eq (h₁.seq_eq (h₂.seq_eq (h₃.seq_eq h₄)))).imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨h, he⟩ => ⟨h, by simp [he]⟩) le_rfl le_rfl

end Frozen

/-! ### Rounds and the whole machine -/

section Stream

variable {Q SI SE SN SF : Type*} {r : InputReader Bool Q} {I : MultiTapeTM K Bool SI}
  {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN} {Fm : MultiTapeTM K Bool SF}
  {V N F : Fin K}

/-- One round: append the content of the next token to the state on tape `V`, then run
`frozenRound` with the input head frozen. -/
public noncomputable def streamRound (r : InputReader Bool Q) (E : MultiTapeTM K Bool SE)
    (Nm : MultiTapeTM K Bool SN) (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  (appendRead r V).seq (frozenRound E Nm V N F hVN hVF hNF).freezeInput

/-- The streaming fold: write the initial state to tape `V` with `I`, run rounds while there is
input left, emit from the final state with `Fm`, clear tape `V` and rewind the input. -/
public noncomputable def streamTM (r : InputReader Bool Q) (I : MultiTapeTM K Bool SI)
    (E : MultiTapeTM K Bool SE) (Nm : MultiTapeTM K Bool SN) (Fm : MultiTapeTM K Bool SF)
    (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  I.seq ((whileInput (streamRound r E Nm V N F hVN hVF hNF)).seq
    ((Fm.seq ((clearWork Bool).extendTapes (tapeEmb V))).freezeInput.seq (rewindInputOn K Bool)))

/-- One round at the input position `p₀` of `x`, on the state `v`: if `E` emits `emit` from the
state with the token's content appended and `Nm` computes `next` from it, the round leaves `next`
on tape `V`, emits `emit` and moves the input head over the token. -/
public theorem transformsTapesAt_streamRound (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (x : List Bool) (p₀ : Fin (x.length + 2)) (hp₀ : p₀.val ≠ 0) (v : List Bool)
    {emit next : List Bool} {tE sE tN sN : ℕ}
    (hE : TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V
        (v ++ (r.read r.q₀ (x.drop (p₀.val - 1))).1))
      (fun _ ws ws' em => ws' = ws ∧ em = emit) tE sE)
    (hN : TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V
        (v ++ (r.read r.q₀ (x.drop (p₀.val - 1))).1))
      (fun _ ws ws' em => ws' = Function.update ws N next ∧ em = []) tN sN) :
    let rd := r.read r.q₀ (x.drop (p₀.val - 1))
    TransformsTapesAt (streamRound r E Nm V N F hVN hVF hNF)
      (fun input p ws => input = x ∧ p.val = p₀.val ∧ ws = Function.update (fun _ => []) V v)
      (fun _ _ _ p' ws' em => p'.val = p₀.val + rd.2 ∧
        ws' = Function.update (fun _ => []) V next ∧ em = emit)
      (v.length + 1 + ((rd.2 + 1) + ((v ++ rd.1).length + 2)) +
        (tE + (tN + (3 * ((v ++ rd.1).length + 1) + ((3 * next.length + 10) +
          3 * (next.length + 1))))))
      ((v ++ rd.1).length + 2 + (K - 1) +
        (sE + (sN + (((v ++ rd.1).length + 1 + K) + ((4 * next.length + K + 15) +
          (next.length + 1 + K)))))) := by
  intro rd
  have hread := (transformsTapesAt_appendRead r V x p₀ hp₀ v).imp
    (P' := fun input p ws => input = x ∧ p.val = p₀.val ∧ ws = Function.update (fun _ => []) V v)
    (fun _ _ ws ⟨hx, hp, hws⟩ => ⟨hx, hp, by simp [hws]⟩) (fun _ _ _ _ _ _ _ h => h) le_rfl le_rfl
  refine (transformsTapesAt_seq hread
    (transformsTapes_frozenRound hVN hVF hNF hE hN).freezeInput ?_).imp
    (fun _ _ _ h => h) ?_ le_rfl le_rfl
  · rintro _ _ ws _ _ _ ⟨-, -, hws⟩ ⟨-, hws', -⟩
    rw [hws', hws, Function.update_idem]
  · rintro _ _ _ _ _ _ _ ⟨_, _, _, _, ⟨hp, -, rfl⟩, ⟨rfl, hws, rfl⟩, rfl⟩
    exact ⟨hp, hws, rfl⟩

/-- The input position after the first `j` tokens. -/
public lemma streamPos_lt (toks : List (List Bool)) (j : ℕ) :
    1 + ((toks.take j).flatten).length < toks.flatten.length + 2 := by
  have := (List.take_sublist j toks).flatten.length_le
  omega

public lemma drop_flatten_take (toks : List (List Bool)) {j : ℕ} (hj : j < toks.length) :
    toks.flatten.drop ((toks.take j).flatten).length =
      toks[j] ++ (toks.drop (j + 1)).flatten := by
  calc toks.flatten.drop ((toks.take j).flatten).length
      = ((toks.take j).flatten ++ (toks.drop j).flatten).drop ((toks.take j).flatten).length := by
        rw [← List.flatten_append, List.take_append_drop]
    _ = (toks.drop j).flatten := List.drop_left
    _ = toks[j] ++ (toks.drop (j + 1)).flatten := by
        rw [List.drop_eq_getElem_cons hj, List.flatten_cons]

public lemma length_flatten_take_succ (toks : List (List Bool)) {j : ℕ} (hj : j < toks.length) :
    ((toks.take (j + 1)).flatten).length = ((toks.take j).flatten).length + toks[j].length := by
  rw [List.take_succ_eq_append_getElem hj, List.flatten_append, List.length_append]
  simp

/-- The time of round `j` of the streaming loop. -/
@[expose] public def streamRoundTime (toks : List (List Bool)) (cont vs : ℕ → List Bool)
    (tE tN : ℕ → ℕ) (j : ℕ) : ℕ :=
  (vs j).length + 1 + ((toks[j]?.getD []).length + 1 + ((vs j ++ cont j).length + 2)) +
    (tE j + (tN j + (3 * ((vs j ++ cont j).length + 1) + ((3 * (vs (j + 1)).length + 10) +
      3 * ((vs (j + 1)).length + 1)))))

-- upstream: candidate
/-- **The streaming loop after an input prefix.** The input is a prefix `pre` followed by the
concatenation of the non-empty tokens `toks`, from each of which the reader `r` reads the content
`cont j`. If for every token `j` the machine `E` emits `es j` and `Nm` computes the next state
`vs (j + 1)` from the state `vs j` followed by `cont j`, then the loop of rounds, started on the
state `vs 0` just past the prefix, leaves the final state on tape `V`, emits the words `es j` and
stops at the end of the input. The prefix is neither read nor copied. -/
public theorem transformsTapesAt_streamLoop_after (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (pre : List Bool) (toks : List (List Bool)) (htoks : ∀ t ∈ toks, t ≠ [])
    (cont vs es : ℕ → List Bool) {sR : ℕ} {tE sE tN sN : ℕ → ℕ}
    (hread : ∀ j (hj : j < toks.length),
      r.read r.q₀ (toks.flatten.drop ((toks.take j).flatten).length) = (cont j, toks[j].length))
    (hE : ∀ j < toks.length, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = ws ∧ em = es j) (tE j) (sE j))
    (hN : ∀ j < toks.length, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = Function.update ws N (vs (j + 1)) ∧ em = []) (tN j) (sN j))
    (hsR : ∀ j < toks.length, (vs j ++ cont j).length + 2 + (K - 1) +
        (sE j + (sN j + (((vs j ++ cont j).length + 1 + K) + ((4 * (vs (j + 1)).length + K + 15) +
          ((vs (j + 1)).length + 1 + K))))) ≤ sR) :
    TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = pre ++ toks.flatten ∧ p.val = 1 + pre.length ∧
        ws = Function.update (fun _ => []) V (vs 0))
      (fun input _ _ p' ws' em => input = pre ++ toks.flatten ∧
        p'.val = 1 + (pre ++ toks.flatten).length ∧
        ws' = Function.update (fun _ => []) V (vs toks.length) ∧
        em = ((List.range toks.length).map es).flatten)
      (∑ j ∈ Finset.range toks.length, (streamRoundTime toks cont vs tE tN j + 1) + 1)
      (2 * K * sR + K) := by
  set x := pre ++ toks.flatten with hx
  let L (j : ℕ) : ℕ := pre.length + ((toks.take j).flatten).length
  have hpos (j : ℕ) : 1 + L j < x.length + 2 := by
    have := streamPos_lt toks j
    simp only [x, L, List.length_append]
    omega
  let P (n : ℕ) (input : List Bool) (p : Fin (input.length + 2)) (ws : Fin K → List Bool)
      (em : List Bool) : Prop :=
    input = x ∧ p.val = 1 + L n ∧ ws = Function.update (fun _ => []) V (vs n) ∧
      em = ((List.range n).map es).flatten
  have hround : ∀ n < toks.length, ∀ acc, TransformsTapesAt (streamRound r E Nm V N F hVN hVF hNF)
      (fun input p ws => P n input p ws acc)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (acc ++ e))
      (streamRoundTime toks cont vs tE tN n) sR := by
    intro n hn acc
    let p₀ : Fin (x.length + 2) := ⟨1 + L n, hpos n⟩
    have hrd : r.read r.q₀ (x.drop (p₀.val - 1)) = (cont n, toks[n].length) := by
      have hdrop : x.drop (p₀.val - 1) = toks.flatten.drop ((toks.take n).flatten).length := by
        simp only [p₀, L, hx, Nat.add_sub_cancel_left]
        rw [← List.drop_drop, List.drop_left]
      rw [hdrop]
      exact hread n hn
    have h := transformsTapesAt_streamRound (r := r) hVN hVF hNF x p₀ (by simp [p₀]) (vs n)
      (hE := by rw [hrd]; exact hE n hn) (hN := by rw [hrd]; exact hN n hn)
    simp only [hrd] at h
    refine h.imp (fun _ _ _ ⟨hin, hp, hws, _⟩ => ⟨hin, hp, hws⟩) ?_ ?_ ?_
    · rintro _ _ _ p' ws' em ⟨rfl, -, -, rfl⟩ ⟨hp', hws', rfl⟩
      refine ⟨rfl, ?_, hws', by simp [List.range_succ]⟩
      rw [hp']
      change (1 + (pre.length + ((toks.take n).flatten).length)) + toks[n].length =
        1 + (pre.length + ((toks.take (n + 1)).flatten).length)
      rw [length_flatten_take_succ toks hn]
      omega
    · simp [streamRoundTime, List.getElem?_eq_getElem hn]
    · exact hsR n hn
  have hmore : ∀ n < toks.length, ∀ input p ws em, P n input p ws em →
      inputSymbolAt input p ≠ none := by
    rintro n hn input p ws em ⟨rfl, hp, -, -⟩
    have hlt : L n < x.length := by
      have h₁ := length_flatten_take_succ toks hn
      have h₂ := hpos (n + 1)
      have : 0 < toks[n].length := List.length_pos_iff.mpr (htoks _ (List.getElem_mem hn))
      simp only [x, L, List.length_append] at h₂ ⊢
      omega
    simp only [inputSymbolAt, hp]
    split_ifs
    · omega
    · rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt]
      simp
  have hL : L toks.length = x.length := by
    simp only [L, x, List.take_length, List.length_append]
  refine (transformsTapesAt_whileInput hround hmore
    (R := fun input p ws em => P toks.length input p ws em)
    (fun input p ws em h => ⟨by
      obtain ⟨rfl, hp, -, -⟩ := h
      simp [inputSymbolAt, hp, hL], h⟩)).imp
    (fun _ _ _ ⟨hin, hp, hws⟩ => ⟨hin, by simp [hp, L], hws, rfl⟩)
    (fun _ _ _ _ _ _ _ ⟨hin, hp, hws, he⟩ => ⟨hin, hp.trans (by rw [hL]), hws, he⟩) le_rfl le_rfl

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: derived from `transformsTapesAt_streamLoop_after` with the empty prefix, so the
-- loop induction is proved once.
/-- **The streaming loop.** The input `x` is the concatenation of the non-empty tokens `toks`, from
each of which the reader `r` reads the content `cont j`. If for every token `j` the machine `E`
emits `es j` and `Nm` computes the next state `vs (j + 1)` from the state `vs j` followed by
`cont j`, then the loop of rounds, started on the state `vs 0` at the start of the input, leaves
the final state on tape `V`, emits the words `es j` and stops at the end of the input. -/
public theorem transformsTapesAt_streamLoop (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (toks : List (List Bool)) (htoks : ∀ t ∈ toks, t ≠ []) (cont vs es : ℕ → List Bool)
    {sR : ℕ} {tE sE tN sN : ℕ → ℕ}
    (hread : ∀ j (hj : j < toks.length),
      r.read r.q₀ (toks.flatten.drop ((toks.take j).flatten).length) = (cont j, toks[j].length))
    (hE : ∀ j < toks.length, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = ws ∧ em = es j) (tE j) (sE j))
    (hN : ∀ j < toks.length, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = Function.update ws N (vs (j + 1)) ∧ em = []) (tN j) (sN j))
    (hsR : ∀ j < toks.length, (vs j ++ cont j).length + 2 + (K - 1) +
        (sE j + (sN j + (((vs j ++ cont j).length + 1 + K) + ((4 * (vs (j + 1)).length + K + 15) +
          ((vs (j + 1)).length + 1 + K))))) ≤ sR) :
    TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = toks.flatten ∧ p.val = 1 ∧
        ws = Function.update (fun _ => []) V (vs 0))
      (fun input _ _ p' ws' em => input = toks.flatten ∧ p'.val = 1 + toks.flatten.length ∧
        ws' = Function.update (fun _ => []) V (vs toks.length) ∧
        em = ((List.range toks.length).map es).flatten)
      (∑ j ∈ Finset.range toks.length, (streamRoundTime toks cont vs tE tN j + 1) + 1)
      (2 * K * sR + K) :=
  transformsTapesAt_streamLoop_after hVN hVF hNF [] toks htoks cont vs es hread hE hN hsR

-- upstream: candidate
open Sequential in
/-- Initialize with a phase `I` that may move the input head past a prefix `pre`, run a streaming
phase from there, emit from its final state and clean up. The phase specifications own the token
reader, round callbacks and their resource accounting. -/
public theorem computesTidily_streamTM_after (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (x pre v₀ v₁ em ef : List Bool) {tI sI tLoop sLoop tF sF : ℕ}
    (hI : TransformsTapesAt I (fun inp p ws => inp = x ∧ p.val = 1 ∧ ws = fun _ => [])
      (fun _ _ _ p' ws' e => p'.val = 1 + pre.length ∧
        ws' = Function.update (fun _ => []) V v₀ ∧ e = []) tI sI)
    (hloop : TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = x ∧ p.val = 1 + pre.length ∧
        ws = Function.update (fun _ => []) V v₀)
      (fun input _ _ p' ws' e => input = x ∧ p'.val = 1 + x.length ∧
        ws' = Function.update (fun _ => []) V v₁ ∧ e = em) tLoop sLoop)
    (hF : TransformsTapes Fm (fun _ ws => ws = Function.update (fun _ => []) V v₁)
      (fun _ ws ws' e => ws' = ws ∧ e = ef) tF sF) :
    (streamTM r I E Nm Fm V N F hVN hVF hNF).ComputesTidilyInTimeAndSpace x (em ++ ef)
      (tI + tLoop + ((tF + 3 * (v₁.length + 1)) + (x.length + 2)))
      (sI + (sLoop + ((sF + (v₁.length + 1 + K)) + K))) := by
  have hI' := hI.imp
    (Q' := fun input _ _ p' ws' e => input = x ∧ p'.val = 1 + pre.length ∧
      ws' = Function.update (fun _ => []) V v₀ ∧ e = [])
    (fun _ _ _ h => h) (fun _ _ _ _ _ _ ⟨hin, _, _⟩ h => ⟨hin, h⟩) le_rfl le_rfl
  have hF' := hF.imp
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) V v₁ ∧ e = ef)
    (fun _ _ h => h)
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨h.trans hws, he⟩) le_rfl le_rfl
  have hclear : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb V))
      (fun _ ws => ws = Function.update (fun _ => []) V v₁)
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
      (3 * (v₁.length + 1)) (v₁.length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb V v₁).imp (fun _ _ h => by simp [h])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws]; simp, he⟩) le_rfl le_rfl
  have hfin := (hF'.seq_eq hclear).freezeInput_eq x (1 + x.length)
  have hrw := (transformsTapesAt_rewindInput (k := K) x).imp
    (P' := fun input p ws => input = x ∧ p.val = 1 + x.length ∧ ws = (fun _ => []))
    (Q' := fun input _ _ p' ws' e => input = x ∧ p'.val = 1 ∧ ws' = (fun _ => []) ∧ e = [])
    (fun _ _ _ h => h.1)
    (by rintro _ _ _ _ _ _ ⟨hin, _, rfl⟩ ⟨rfl, hws, he⟩
        exact ⟨hin, rfl, hws, he⟩) le_rfl le_rfl
  have hall := hI'.seq_eq (hloop.seq_eq (hfin.seq_eq hrw))
  refine (hall.transformsTapes (fun _ _ _ _ _ _ h => Fin.ext h.2.1)).imp
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, rfl, hws⟩)
    (fun _ _ _ _ _ ⟨_, _, hws, he⟩ => ⟨hws, by simpa using he⟩) (by omega) (by omega)

/-- Initialize, run a streaming phase, emit from its final state and clean up. The phase
specification owns the token reader, round callbacks and their resource accounting. This is
`computesTidily_streamTM_after` with an initializer that leaves the input head at the start. -/
public theorem computesTidily_streamTM (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (x v₀ v₁ em ef : List Bool) {tI sI tLoop sLoop tF sF : ℕ}
    (hI : TransformsTapes I (fun inp ws => inp = x ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) V v₀ ∧ e = []) tI sI)
    (hloop : TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = x ∧ p.val = 1 ∧ ws = Function.update (fun _ => []) V v₀)
      (fun input _ _ p' ws' e => input = x ∧ p'.val = 1 + x.length ∧
        ws' = Function.update (fun _ => []) V v₁ ∧ e = em) tLoop sLoop)
    (hF : TransformsTapes Fm (fun _ ws => ws = Function.update (fun _ => []) V v₁)
      (fun _ ws ws' e => ws' = ws ∧ e = ef) tF sF) :
    (streamTM r I E Nm Fm V N F hVN hVF hNF).ComputesTidilyInTimeAndSpace x (em ++ ef)
      (tI + tLoop + ((tF + 3 * (v₁.length + 1)) + (x.length + 2)))
      (sI + (sLoop + ((sF + (v₁.length + 1 + K)) + K))) :=
  computesTidily_streamTM_after hVN hVF hNF x [] v₀ v₁ em ef
    (hI.transformsTapesAt_eq.imp (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ _ ⟨_, hp, hws, he⟩ => ⟨hp, hws, he⟩) le_rfl le_rfl) hloop hF

end Stream

end Turing.MultiTapeTM


