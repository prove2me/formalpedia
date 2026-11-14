-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Correct
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Correct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:57.335378+00:00
-- url     : https://prove2.me/theorems/9c8df855-7f76-47a9-a2ef-162d28743220
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct — The simulation is correct
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A configuration of the simulation, together with the output so far, is a configuration of a
--   machine over `ℕ` (`Turing.MultiTapeTM.Universal.SCfg.toCfg`), the zippers holding the symbols of
--   the work tapes. If the description holds the transition of the machine for the current key, a step
--   of the simulation is a step of the machine, and emits the same symbol
--   (`Turing.MultiTapeTM.Universal.toCfg_step`).
--
--   A machine with finitely many states and symbols, renamed into `ℕ` by `Turing.MultiTapeTM.map`, has a
--   description listing its transitions (`Turing.MultiTapeTM.Universal.desc`). Since runs commute with
--   renaming, simulating the description yields the renamed output of the machine.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.desc`: the description of a machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.simulate_desc`: the simulation agrees with the machine.
--
--   **Contents.** The module is published as a whole: 21 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Correct`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Correct.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Map
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Lookup

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The simulation is correct

A configuration of the simulation, together with the output so far, is a configuration of a
machine over `ℕ` (`Turing.MultiTapeTM.Universal.SCfg.toCfg`), the zippers holding the symbols of
the work tapes. If the description holds the transition of the machine for the current key, a step
of the simulation is a step of the machine, and emits the same symbol
(`Turing.MultiTapeTM.Universal.toCfg_step`).

A machine with finitely many states and symbols, renamed into `ℕ` by `Turing.MultiTapeTM.map`, has a
description listing its transitions (`Turing.MultiTapeTM.Universal.desc`). Since runs commute with
renaming, simulating the description yields the renamed output of the machine.

## Main definitions

* `Turing.MultiTapeTM.Universal.desc`: the description of a machine.

## Main results

* `Turing.MultiTapeTM.Universal.simulate_desc`: the simulation agrees with the machine.
-/

namespace Turing.MultiTapeTM.Universal

variable {k : ℕ}

/-- The key of the arguments of a transition. -/
@[expose] public def key (q : ℕ) (inp : Option ℕ) (work : Fin k → Option ℕ) : Key :=
  ⟨q, inp, List.ofFn work⟩

/-- An action, with the work tapes in a list. -/
@[expose] public def Act.ofAction (a : Action k ℕ ℕ) : Act :=
  ⟨a.inputTape, List.ofFn a.workTapes, a.output, a.state⟩

/-- The description `d` holds the transition of `tm` for the key `(q, inp, work)`. -/
public def Desc.Holds (d : Desc) (tm : MultiTapeTM k ℕ ℕ) (q : ℕ) (inp : Option ℕ)
    (work : Fin k → Option ℕ) : Prop :=
  (d.table.find? (·.1 = key q inp work)).map Prod.snd = some (.ofAction (tm.tr q inp work))

/-! ### Configurations of the simulation as configurations -/

namespace Tape

/-- The symbol at position `z`. -/
@[expose] public def cellAt (t : Tape) (z : ℤ) : Option ℕ :=
  if t.head ≤ z then t.right.getD (z - t.head).toNat none
  else t.left.getD (t.head - z - 1).toNat none

lemma read_eq (t : Tape) : t.read = t.cellAt t.head := by
  simp only [read, cellAt, le_refl, ↓reduceIte, sub_self, Int.toNat_zero]
  cases t.right <;> rfl

lemma cellAt_write (t : Tape) (o : Option ℕ) (z : ℤ) :
    (t.write o).cellAt z = if z = t.head then o else t.cellAt z := by
  unfold cellAt write
  split_ifs with h₁ h₂ <;> simp only at *
  · subst h₂; simp
  · obtain ⟨n, hn⟩ : ∃ n, (z - t.head).toNat = n + 1 := ⟨(z - t.head).toNat - 1, by omega⟩
    rw [hn, List.getD_cons_succ]
    rcases t.right with _ | ⟨a, r⟩ <;> simp
  · omega

lemma cellAt_move (t : Tape) (m : SignType) (z : ℤ) : (t.move m).cellAt z = t.cellAt z := by
  unfold cellAt move
  rcases m with _ | _ | _ <;> simp only <;> split_ifs <;> try omega
  · obtain ⟨n, hn⟩ : ∃ n, (z - (t.head - 1)).toNat = n + 1 := ⟨(z - t.head).toNat, by omega⟩
    rw [hn, List.getD_cons_succ, show n = (z - t.head).toNat by omega]
  · rw [show (z - (t.head - 1)).toNat = 0 by omega, List.getD_cons_zero,
      show (t.head - z - 1).toNat = 0 by omega]
    rcases t.left with _ | ⟨a, l⟩ <;> simp
  · obtain ⟨n, hn⟩ : ∃ n, (t.head - z - 1).toNat = n + 1 :=
      ⟨(t.head - z - 1).toNat - 1, by omega⟩
    rw [show (t.head - 1 - z - 1).toNat = n by omega, hn]
    rcases t.left with _ | ⟨a, l⟩ <;> simp
  · rw [show (z - t.head).toNat = (z - (t.head + 1)).toNat + 1 by omega]
    rcases t.right with _ | ⟨a, r⟩ <;> simp
  · rw [show (t.head + 1 - z - 1).toNat = 0 by omega, show (z - t.head).toNat = 0 by omega]
    simp only [read, List.getD_cons_zero]
    cases t.right <;> rfl
  · rw [show (t.head + 1 - z - 1).toNat = (t.head - z - 1).toNat + 1 by omega]
    simp

lemma head_move (t : Tape) (m : SignType) : (t.move m).head = t.head + m := by
  rcases m with _ | _ | _ <;> simp [move, SignType.cast, sub_eq_add_neg]

end Tape

variable {x : List ℕ}

/-- The empty work tape, for missing work tapes. -/
@[expose] public def Tape.blank : Tape := ⟨0, [], []⟩

/-- The configuration of a machine with `k` work tapes on the input `x` that `s` represents, with
the output `out`: the work tapes hold the symbols of the zippers. Missing work tapes are blank and
an input head beyond the input is clamped; on well-shaped configurations neither happens. -/
@[expose] public def SCfg.toCfg (k : ℕ) (x : List ℕ) (s : SCfg) (out : List ℕ) :
    Cfg k ℕ ℕ x where
  state := s.state
  inputPos := ⟨min s.inputPos (x.length + 1), by omega⟩
  workTapes i := (s.workTapes.getD i .blank).cellAt
  workTapePos i := (s.workTapes.getD i .blank).head
  output := out

/-- `s` has `k` work tapes and its input head on the input `x` or its boundaries. -/
public structure SCfg.WellShaped (k : ℕ) (x : List ℕ) (s : SCfg) : Prop where
  length_workTapes : s.workTapes.length = k
  inputPos_le : s.inputPos ≤ x.length + 1

lemma moveInput_val (p : Fin (x.length + 2)) (m : SignType) :
    moveInput p.val (inputSymbol x p.val) m = (moveInputPos p m).val := by
  have := val_moveInputPos_eq p m
  have hs := isSome_inputSymbol x p.val
  rcases m with _ | _ | _ <;> simp only [moveInput, SignType.cast] at *
  · omega
  · omega
  · by_cases h : (inputSymbol x p.val).isSome
    · simp only [h, or_true, ↓reduceIte]
      have := hs.mp h
      omega
    · have := mt hs.mpr h
      split_ifs with hc
      · rcases hc with hc | hc
        · omega
        · exact absurd hc h
      · omega

lemma applyTapes_ofFn (ts : Fin k → Tape) (as : Fin k → Option (Option ℕ) × SignType) :
    applyTapes (List.ofFn ts) (List.ofFn as) = List.ofFn fun i => (ts i).apply (as i) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.ofFn_succ, applyTapes, ih]

lemma inputSymbol_val (c : Cfg k ℕ ℕ x) : inputSymbol x c.inputPos.val = c.inputSymbol := by
  unfold inputSymbol Cfg.inputSymbol
  have := c.inputPos.isLt
  split_ifs <;> grind [List.head?_drop, Fin.ext_iff]

/-- **A step of the simulation is a step of the machine**, emitting the same symbol, if the
description holds the transition for the current key. -/
public theorem toCfg_step {tm : MultiTapeTM k ℕ ℕ} {d : Desc} {s : SCfg} {out : List ℕ}
    (hs : s.WellShaped k x)
    (hd : ∀ q, (s.toCfg k x out).state = some q →
      d.Holds tm q (s.toCfg k x out).inputSymbol (s.toCfg k x out).workTapeSymbols) :
    (step d x s).1.toCfg k x (out ++ (step d x s).2.toList) = tm.step (s.toCfg k x out) ∧
      (step d x s).1.WellShaped k x := by
  obtain ⟨st, ip, ws⟩ := s
  obtain ⟨hk, hp⟩ := hs
  dsimp only at hk hp
  obtain ⟨ts, rfl⟩ : ∃ ts : Fin k → Tape, ws = List.ofFn ts :=
    ⟨fun i => ws[i], List.ext_getElem (by simp [hk]) fun _ _ _ => by simp⟩
  cases st with
  | none => exact ⟨by simpa [step] using
      (step_of_halt (cfg := SCfg.toCfg k x ⟨none, ip, List.ofFn ts⟩ out) rfl).symm, hk, hp⟩
  | some q =>
    set c := SCfg.toCfg k x ⟨some q, ip, List.ofFn ts⟩ out
    have hip : (c.inputPos : ℕ) = ip := by simp only [c, SCfg.toCfg]; omega
    have hkey : SCfg.key ⟨some q, ip, List.ofFn ts⟩ x q =
        key q c.inputSymbol c.workTapeSymbols := by
      simp only [SCfg.key, key, ← hip, inputSymbol_val, List.map_ofFn]
      congr 2
      funext i
      simp [Tape.read_eq, c, SCfg.toCfg, Cfg.workTapeSymbols]
    obtain ⟨⟨_, _⟩, he, rfl⟩ := Option.map_eq_some_iff.mp (hd q rfl)
    rw [step_of_state (show c.state = some q from rfl)]
    simp only [step, hkey, he]
    set a := tm.tr q c.inputSymbol c.workTapeSymbols
    refine ⟨Cfg.ext rfl (Fin.ext ?_) (funext fun i => funext fun z => ?_) (funext fun i => ?_) ?_,
      by simp [Act.apply, Act.ofAction, applyTapes_ofFn], moveInput_le hp _⟩
    · have := (moveInputPos c.inputPos a.inputTape).isLt
      simp only [SCfg.toCfg, Act.apply, Act.ofAction, Action.apply_inputPos, ← hip, moveInput_val]
      omega
    · simp only [SCfg.toCfg, Act.apply, Act.ofAction, applyTapes_ofFn, List.getD_ofFn, Tape.apply,
        Tape.cellAt_move, Action.apply_workTapes]
      cases (a.workTapes i).1 <;>
        simp [Tape.cellAt_write, Function.update_apply, c, SCfg.toCfg]
    · simp [SCfg.toCfg, Act.apply, Act.ofAction, applyTapes_ofFn, Tape.apply, Tape.head_move, c]
      cases (a.workTapes i).1 <;> simp [Tape.write]
    · simp [SCfg.toCfg, Act.ofAction, c]

/-- The initial configuration of the simulation is the initial configuration. -/
public theorem toCfg_init {d : Desc} (hk : d.tapes = k) :
    (init d).toCfg k x [] = Cfg.init d.q₀ x ∧ (init d).WellShaped k x := by
  subst hk
  refine ⟨Cfg.ext rfl (Fin.ext ?_) (funext fun i => funext fun z => ?_) (funext fun i => ?_) rfl,
    by simp [init], by simp [init]⟩ <;>
    simp [SCfg.toCfg, init, List.getD_eq_getElem?_getD, Tape.cellAt, Tape.blank]

/-! ### Descriptions of machines -/

variable {Symbol State : Type} [Fintype State] [Fintype Symbol]
  (eS : State ↪ ℕ) (eY : Symbol ↪ ℕ)

/-- The description of a machine with finitely many states and symbols, renamed into `ℕ` by `eS`
and `eY`: a transition for every state and every choice of read symbols. -/
@[expose] public noncomputable def desc (tm : MultiTapeTM k Symbol State) : Desc :=
  ⟨k, eS tm.q₀, (Finset.univ : Finset (State × Option Symbol × (Fin k → Option Symbol))).toList.map
    fun e => (key (eS e.1) (e.2.1.map eY) (Option.map eY ∘ e.2.2),
      .ofAction ((tm.tr e.1 e.2.1 e.2.2).map eS eY))⟩

omit [Fintype State] [Fintype Symbol] in
lemma key_injective : Function.Injective fun e : State × Option Symbol × (Fin k → Option Symbol) =>
    key (eS e.1) (e.2.1.map eY) (Option.map eY ∘ e.2.2) := by
  rintro ⟨q, i, w⟩ ⟨q', i', w'⟩ h
  simp only [key, Key.mk.injEq] at h
  rw [eS.injective h.1, Option.map_injective eY.injective h.2.1,
    (Option.map_injective eY.injective).comp_left (List.ofFn_injective h.2.2)]

/-- The description of `tm` holds the transitions of the renamed machine on renamed keys. -/
lemma holds_desc (tm : MultiTapeTM k Symbol State) (q : State) (inp : Option Symbol)
    (work : Fin k → Option Symbol) :
    (desc eS eY tm).Holds (tm.map eS eY) (eS q) (inp.map eY) (Option.map eY ∘ work) := by
  have hmem : (key (eS q) (inp.map eY) (Option.map eY ∘ work),
      Act.ofAction ((tm.tr q inp work).map eS eY)) ∈ (desc eS eY tm).table :=
    List.mem_map.mpr ⟨(q, inp, work), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp ((List.find?_isSome
    (p := fun e => decide (e.1 = key (eS q) (inp.map eY) (Option.map eY ∘ work)))).mpr
      ⟨_, hmem, by simp⟩)
  obtain ⟨⟨q', inp', work'⟩, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some he)
  have hk := List.find?_some he
  simp only [decide_eq_true_eq] at hk
  cases key_injective eS eY (a₁ := (q', inp', work')) (a₂ := (q, inp, work)) hk
  simp [Desc.Holds, he, tr_map]

/-- The run of the simulation of the description of `tm`, read as configurations, is the renamed
run of `tm`. -/
public theorem toCfg_iterate (tm : MultiTapeTM k Symbol State) (x : List Symbol) (t : ℕ) :
    (tm.runFrom (tm.initCfg x) t).map eS eY =
        ((stepOut (desc eS eY tm) (x.map eY))^[t] (init (desc eS eY tm), [])).1.toCfg k
          (x.map eY) ((stepOut (desc eS eY tm) (x.map eY))^[t] (init (desc eS eY tm), [])).2 ∧
      ((stepOut (desc eS eY tm) (x.map eY))^[t] (init (desc eS eY tm), [])).1.WellShaped k
        (x.map eY) := by
  induction t with
  | zero =>
    simp only [runFrom, Function.iterate_zero_apply, MultiTapeNTM.initCfg]
    have h := toCfg_init (k := k) (d := desc eS eY tm) (x := x.map eY) rfl
    exact ⟨by rw [h.1, Cfg.map_init]; rfl, h.2⟩
  | succ t ih =>
    rw [runFrom_succ, ← step_map, Function.iterate_succ_apply', ih.1]
    refine (toCfg_step ih.2 fun q hq => ?_).imp_left Eq.symm
    rw [← ih.1] at hq ⊢
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [Cfg.inputSymbol_map]
    exact holds_desc eS eY tm q _ (tm.runFrom (tm.initCfg x) t).workTapeSymbols

/-- **The simulation is correct**: simulating the description of `tm` on the renamed input for
`t` steps yields the renamed output of `tm` after `t` steps, and whether `tm` has halted. -/
public theorem simulate_desc (tm : MultiTapeTM k Symbol State) (x : List Symbol) (t : ℕ) :
    simulate (desc eS eY tm) (x.map eY) t =
      ((tm.runFrom (tm.initCfg x) t).output.map eY,
        (tm.runFrom (tm.initCfg x) t).state.isNone) := by
  have hs := congrArg Cfg.state (toCfg_iterate eS eY tm x t).1
  have ho := congrArg Cfg.output (toCfg_iterate eS eY tm x t).1
  simp only [Cfg.map_state, Cfg.map_output, SCfg.toCfg] at hs ho
  simp only [simulate, ← hs, ← ho, Option.isNone_map]

end Turing.MultiTapeTM.Universal


