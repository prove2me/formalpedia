-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Map
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Map
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:28.049347+00:00
-- url     : https://prove2.me/theorems/133021e9-0aec-4af7-85af-ec06d5b8274a
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Map — Renaming states and symbols
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Map` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Injections `eS` of states and `eY` of symbols rename actions (`Turing.Action.map`) and
--   configurations (`Turing.Cfg.map`). The renamed machine `Turing.MultiTapeTM.map eS eY tm` acts as
--   `tm` on renamed states and symbols and halts elsewhere, so its runs from renamed configurations are
--   the renamed runs of `tm`.
--
--   ### Main definitions
--
--   * `Turing.Action.map`, `Turing.Cfg.map`: renamed actions and configurations.
--   * `Turing.MultiTapeTM.map`: the renamed machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.runFrom_map_map`: the run of the renamed machine is the renamed run.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Map`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Map.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Map` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Renaming states and symbols

Injections `eS` of states and `eY` of symbols rename actions (`Turing.Action.map`) and
configurations (`Turing.Cfg.map`). The renamed machine `Turing.MultiTapeTM.map eS eY tm` acts as
`tm` on renamed states and symbols and halts elsewhere, so its runs from renamed configurations are
the renamed runs of `tm`.

## Main definitions

* `Turing.Action.map`, `Turing.Cfg.map`: renamed actions and configurations.
* `Turing.MultiTapeTM.map`: the renamed machine.

## Main results

* `Turing.MultiTapeTM.runFrom_map_map`: the run of the renamed machine is the renamed run.
-/

namespace Turing

variable {k : ℕ} {Symbol State Symbol' State' : Type*} {input : List Symbol}
  (eS : State ↪ State') (eY : Symbol ↪ Symbol')

/-- An action with renamed states and symbols. -/
@[expose, simps] public def Action.map (a : Action k Symbol State) : Action k Symbol' State' where
  inputTape := a.inputTape
  workTapes i := ((a.workTapes i).1.map (Option.map eY), (a.workTapes i).2)
  output := a.output.map eY
  state := a.state.map eS

/-- A configuration with renamed states and symbols. -/
@[expose, simps] public def Cfg.map (c : Cfg k Symbol State input) :
    Cfg k Symbol' State' (input.map eY) where
  state := c.state.map eS
  inputPos := c.inputPos.cast (by simp)
  workTapes i z := (c.workTapes i z).map eY
  workTapePos := c.workTapePos
  output := c.output.map eY

namespace Cfg

variable (c : Cfg k Symbol State input)

@[simp]
public lemma inputSymbol_map : (c.map eS eY).inputSymbol = c.inputSymbol.map eY := by
  unfold inputSymbol
  by_cases h₀ : c.inputPos.val = 0 <;> by_cases h₁ : c.inputPos.val = input.length + 1 <;>
    simp [Cfg.map, Fin.ext_iff, h₀, h₁]

@[simp]
public lemma workTapeSymbols_map (i : Fin k) :
    (c.map eS eY).workTapeSymbols i = (c.workTapeSymbols i).map eY :=
  rfl

public lemma map_init (q₀ : State) :
    (init q₀ input : Cfg k Symbol State input).map eS eY = init (eS q₀) (input.map eY) := by
  ext <;> simp [Cfg.map]

end Cfg

@[simp]
public lemma Action.apply_map (a : Action k Symbol State) (c : Cfg k Symbol State input) :
    (a.map eS eY).apply (c.map eS eY) = (a.apply c).map eS eY := by
  refine Cfg.ext rfl (Fin.ext ?_) (funext fun i => funext fun z => ?_) rfl ?_
  · have h₁ := val_moveInputPos_eq (c.map eS eY).inputPos a.inputTape
    have h₂ := val_moveInputPos_eq c.inputPos a.inputTape
    simp only [Cfg.map_inputPos, Fin.val_cast, List.length_map] at h₁
    simp only [Action.apply_inputPos, Action.map_inputTape, Cfg.map_inputPos, Fin.val_cast]
    omega
  · simp only [Action.apply_workTapes, Action.map_workTapes, Cfg.map_workTapes]
    cases (a.workTapes i).1 <;> simp [Function.update_apply, apply_ite (Option.map eY)]
  · rcases a with ⟨_, _, _ | _, _⟩ <;> simp

namespace MultiTapeTM

/-- The halting action, which leaves every tape alone. -/
@[expose] public def haltAction : Action k Symbol State :=
  ⟨0, fun _ => (none, 0), none, none⟩

/-- `tm` with renamed states and symbols: on renamed states and symbols it acts as `tm`, elsewhere
it halts. -/
@[expose] public noncomputable def map (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol' State' :=
  ofTr (eS tm.q₀) fun q i w =>
    match Function.partialInv eS q, Function.partialInv (Option.map eY) i,
      Function.partialInv (fun w : Fin k → Option Symbol => Option.map eY ∘ w) w with
    | some q, some i, some w => (tm.tr q i w).map eS eY
    | _, _, _ => haltAction

variable (tm : MultiTapeTM k Symbol State)

@[simp]
public lemma q₀_map : (tm.map eS eY).q₀ = eS tm.q₀ := rfl

@[simp]
public lemma tr_map (q : State) (i : Option Symbol) (w : Fin k → Option Symbol) :
    (tm.map eS eY).tr (eS q) (i.map eY) (Option.map eY ∘ w) = (tm.tr q i w).map eS eY := by
  simp [map, Function.partialInv_left eS.injective,
    Function.partialInv_left (Option.map_injective eY.injective),
    Function.partialInv_left ((Option.map_injective eY.injective).comp_left (α := Fin k))]

/-- A step of the renamed machine is the renamed step. -/
public theorem step_map (c : Cfg k Symbol State input) :
    (tm.map eS eY).step (c.map eS eY) = (tm.step c).map eS eY := by
  cases hq : c.state with
  | none => rw [step_of_halt hq, step_of_halt (by simp [hq])]
  | some q =>
    rw [step_of_state hq, step_of_state (q := eS q) (by simp [hq]), Cfg.inputSymbol_map,
      show (c.map eS eY).workTapeSymbols = Option.map eY ∘ c.workTapeSymbols from rfl, tr_map,
      Action.apply_map]

-- vendored: `runFrom_map` in crei:crei/tidy-universal, a name that cslib #1116 gives to the run
-- of a step homomorphism
/-- **The run of the renamed machine** is the renamed run. -/
public theorem runFrom_map_map (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.map eS eY).runFrom (c.map eS eY) t = (tm.runFrom c t).map eS eY :=
  (Function.Semiconj.iterate_right (f := Cfg.map eS eY) (fun c => (step_map eS eY tm c).symm) t
    c).symm

end MultiTapeTM

end Turing


