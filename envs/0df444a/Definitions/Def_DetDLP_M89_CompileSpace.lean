-- Prove2me | Definitions.Def_DetDLP_M89_CompileSpace
-- name    : DetDLP_M89_CompileSpace
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T17:12:24.170259+00:00
-- url     : https://prove2.me/theorems/2efd43f0-3de4-4b38-9aab-e62e2f2fe6dd
-- title:
--   Prefix space preservation for compiled bit programs
-- statement:
--   Prefix space preservation for compiled bit programs. This module supports bounded execution of finite Boolean-stack programs on the primitive multitape machine.
-- source:
--   OpenAI math, lean/OAI/Algorithms/SubexponentialSAT; local verified port, as credited in the module header.

/-
# All-prefix visited-space preservation for the finite bit compiler

Adapted from OpenAI `math` (Apache License 2.0), selectively retrieved
2026-11-23: SqrtLogSpace/VisitedTape, GuardedCompiler, and CompileSpace.
The existing platform LocatedCfg/locatedStep/visitedSpace are shared rather
than duplicated. Original proof bodies and module comments are retained;
imports are replaced by the locally verified compiler core.
-/
import Definitions.Def_DetDLP_M89_BitCompiler
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem headDisplacement_bounds (action : Turing.TM0.Stmt (Option Bool)) :
    -1 ≤ headDisplacement action ∧ headDisplacement action ≤ 1 := by
  cases action with
  | move direction => cases direction <;> decide
  | write symbol =>
      change (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
      decide

@[simp] theorem LocatedCfg.monitor_config {machine : PrimitiveMachine}
    (c : LocatedCfg machine) (config : machine.Cfg) :
    (c.monitor config).config = config := by
  cases hs : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hs]
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hs, ht]
      | inr result =>
          obtain ⟨next, action⟩ := result
          simp [LocatedCfg.monitor, hs, ht]

theorem locatedStep_erase (machine : PrimitiveMachine) (c : LocatedCfg machine) :
    (locatedStep machine c).map LocatedCfg.config = machine.step c.config := by
  simp only [locatedStep, Option.map_map]
  cases machine.step c.config <;> simp

theorem locatedStep_config {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (h : locatedStep machine c = some d) : machine.step c.config = some d.config := by
  rw [← locatedStep_erase machine c, h]
  rfl

theorem locatedStep_position_action {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {q next : Fin machine.stateCount}
    {action : Turing.TM0.Stmt (Option Bool)}
    (hs : locatedStep machine c = some d) (hq : c.config.state = .inr q)
    (ha : machine.transition q (c.config.tapes (machine.scan q)).head = .inr (next, action)) :
    d.position = Function.update c.position (machine.scan q)
      (c.position (machine.scan q) + headDisplacement action) := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  simp [LocatedCfg.monitor, hq, ha]

theorem locatedStep_position_halt {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {q : Fin machine.stateCount} {answer : Bool}
    (hs : locatedStep machine c = some d) (hq : c.config.state = .inr q)
    (ha : machine.transition q (c.config.tapes (machine.scan q)).head = .inl answer) :
    d.position = c.position := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  simp [LocatedCfg.monitor, hq, ha]

theorem locatedStep_position_bounds {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (i : Fin machine.tapeCount) :
    c.position i - 1 ≤ d.position i ∧ d.position i ≤ c.position i + 1 := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hs : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hs]
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hs, ht]
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hs, ht, Function.update_self]
            have h := headDisplacement_bounds action
            omega
          · simp [LocatedCfg.monitor, hs, ht, Function.update_of_ne hi]

theorem locatedTrace_position_bounds {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) (i : Fin machine.tapeCount) :
    c.position i - (steps : ℤ) ≤ d.position i ∧
      d.position i ≤ c.position i + (steps : ℤ) := by
  induction tr with
  | refl => simp
  | cons hs _ ih =>
      have h := locatedStep_position_bounds hs i
      omega

theorem locatedTrace_erase {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (h : Computation.Trace (locatedStep machine) steps c d) :
    Computation.Trace machine.step steps c.config d.config := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih => exact .cons (locatedStep_config hs) ih

theorem locatedTrace_lift {machine : PrimitiveMachine} {c : LocatedCfg machine}
    {config : machine.Cfg} {steps : ℕ}
    (h : Computation.Trace machine.step steps c.config config) :
    ∃ d : LocatedCfg machine,
      Computation.Trace (locatedStep machine) steps c d ∧ d.config = config := by
  generalize hc : c.config = start at h
  induction h generalizing c with
  | refl => exact ⟨c, .refl c, hc⟩
  | @cons steps start next final hs _ ih =>
      have hstep : locatedStep machine c = some (c.monitor next) := by
        simp [locatedStep, hc, hs]
      obtain ⟨d, hd, hcfg⟩ := ih (c := c.monitor next) (c.monitor_config next)
      exact ⟨d, .cons hstep hd, hcfg⟩

theorem locatedStep_encloses {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d)
    (h : ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i) :
    ∀ i, d.lower i ≤ d.position i ∧ d.position i ≤ d.upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  intro i
  cases hstate : c.config.state with
  | inl answer => simpa [LocatedCfg.monitor, hstate] using h i
  | inr q =>
      cases htransition : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simpa [LocatedCfg.monitor, hstate, htransition] using h i
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hstate, htransition, Function.update_self]
          · simpa [LocatedCfg.monitor, hstate, htransition, Function.update_of_ne hi] using h i

theorem locatedStep_expands {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (i : Fin machine.tapeCount) :
    d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hstate : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hstate]
  | inr q =>
      cases htransition : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hstate, htransition]
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hstate, htransition, Function.update_self]
          · simp [LocatedCfg.monitor, hstate, htransition, Function.update_of_ne hi]

theorem locatedStep_envelope {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ i, lower i ≤ d.position i ∧ d.position i ≤ upper i) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  intro i
  have hc' := hc i
  have hp' := hp i
  cases hs : c.config.state with
  | inl answer => simpa [LocatedCfg.monitor, hs] using hc'
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simpa [LocatedCfg.monitor, hs, ht] using hc'
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hs, ht, Function.update_self] at hp' ⊢
            exact ⟨⟨hc'.1, hp'.1⟩, hc'.2, hp'.2⟩
          · simpa [LocatedCfg.monitor, hs, ht, Function.update_of_ne hi] using hc'

theorem locatedTrace_encloses {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (h : ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i) :
    ∀ i, d.lower i ≤ d.position i ∧ d.position i ≤ d.upper i := by
  induction tr with
  | refl => exact h
  | cons hs _ ih => exact ih (locatedStep_encloses hs h)

theorem locatedTrace_init_encloses {machine : PrimitiveMachine} {input : List Bool}
    {d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps (locatedInit machine input) d) :
    ∀ i, d.lower i ≤ d.position i ∧ d.position i ≤ d.upper i := by
  apply locatedTrace_encloses tr
  intro i
  simp only [locatedInit, Int.ofNat_eq_natCast]
  split_ifs <;> omega

theorem locatedTrace_expands {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (i : Fin machine.tapeCount) :
    d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i := by
  induction tr with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | cons hs _ ih =>
      have h := locatedStep_expands hs i
      exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩

theorem visitedSpace_mono {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (h : ∀ i, d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i) :
    visitedSpace c ≤ visitedSpace d := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hi := h i
  omega

theorem locatedTrace_visitedSpace_mono {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) :
    visitedSpace c ≤ visitedSpace d :=
  visitedSpace_mono (locatedTrace_expands tr)

theorem trace_prefix_exists {α : Type*} {step : α → Option α}
    {a b : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps a b) (hle : prefixSteps ≤ steps) :
    ∃ intermediate, Computation.Trace step prefixSteps a intermediate := by
  induction tr generalizing prefixSteps with
  | refl a =>
      have hp : prefixSteps = 0 := by omega
      subst prefixSteps
      exact ⟨a, .refl a⟩
  | @cons steps a next final hs ht ih =>
      cases prefixSteps with
      | zero => exact ⟨a, .refl a⟩
      | succ prefixSteps =>
          obtain ⟨intermediate, hp⟩ := ih (prefixSteps := prefixSteps) (by omega)
          exact ⟨intermediate, .cons hs hp⟩

theorem trace_same_length_unique {α : Type*} {step : α → Option α}
    {a b c : α} {steps : ℕ}
    (hb : Computation.Trace step steps a b)
    (hc : Computation.Trace step steps a c) : b = c :=
  Option.some.inj (hb.iterate.symm.trans hc.iterate)

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht

theorem locatedTrace_prefix_space {machine : PrimitiveMachine}
    {c d intermediate : LocatedCfg machine} {steps prefixSteps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d)
    (hp : Computation.Trace (locatedStep machine) prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) : visitedSpace intermediate ≤ visitedSpace d :=
  locatedTrace_visitedSpace_mono (trace_suffix tr hp hle)

theorem locatedTrace_envelope {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace (locatedStep machine) prefixSteps c intermediate →
      ∀ i, lower i ≤ intermediate.position i ∧ intermediate.position i ≤ upper i) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  induction tr with
  | refl => exact hc
  | @cons steps c next final hs ht ih =>
      apply ih
      · exact locatedStep_envelope hs lower upper hc
          (hp 1 next (by omega) (.cons hs (.refl next)))
      · intro prefixSteps intermediate hle htr
        exact hp (prefixSteps + 1) intermediate (by omega) (.cons hs htr)

theorem locatedTrace_envelope_of_margin {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps budget : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) (ht : steps ≤ budget)
    (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ i, lower i + (budget : ℤ) ≤ c.position i ∧
      c.position i ≤ upper i - (budget : ℤ)) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  apply locatedTrace_envelope tr lower upper hc
  intro prefixSteps intermediate hle htr i
  have hmove := locatedTrace_position_bounds htr i
  have hstart := hp i
  omega

theorem visitedSpace_le_of_envelope {machine : PrimitiveMachine}
    (c : LocatedCfg machine) (lower upper : Fin machine.tapeCount → ℤ)
    (h : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i) :
    visitedSpace c ≤ ∑ i, (upper i - lower i + 1).toNat := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hi := h i
  omega

/-- Useful for polynomial-time preprocessing fragments only: substituting the
full exponential counting time here would not give polynomial space. -/
theorem locatedTrace_space_le_of_length {machine : PrimitiveMachine} {input : List Bool}
    {d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps (locatedInit machine input) d) :
    visitedSpace d ≤ machine.tapeCount * (input.length + 2 * steps + 1) := by
  have hinitial : ∀ i,
      -(steps : ℤ) ≤ (locatedInit machine input).lower i ∧
      (locatedInit machine input).upper i ≤ (input.length : ℤ) + steps := by
    intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  have hpositions : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace (locatedStep machine) prefixSteps
        (locatedInit machine input) intermediate →
      ∀ i, -(steps : ℤ) ≤ intermediate.position i ∧
        intermediate.position i ≤ (input.length : ℤ) + steps := by
    intro prefixSteps intermediate hle htr i
    have h := locatedTrace_position_bounds htr i
    simp only [locatedInit] at h
    omega
  have h := locatedTrace_envelope tr (fun _ => -(steps : ℤ))
    (fun _ => (input.length : ℤ) + steps) hinitial hpositions
  apply (visitedSpace_le_of_envelope d _ _ h).trans
  have hwidth : ((input.length : ℤ) + steps - -(steps : ℤ) + 1).toNat =
      input.length + 2 * steps + 1 := by omega
  simp only [hwidth, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_rfl


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.StackCompiler OAI.Algorithms.SubexponentialSAT.StackEncoding OAI.Algorithms.SubexponentialSAT.StackMachine
open scoped BigOperators

theorem reindex_located_action {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t)
    (c : LocatedCfg (reindex e p)) (q q' : Q) (action : Action)
    (tapes : Fin t → BitTape)
    (hc : c.config = reindexCfg e p ⟨.inr q, tapes⟩)
    (ha : p.transition q (tapes (p.scan q)).head = .inr (q', action)) :
    ∃ d : LocatedCfg (reindex e p),
      locatedStep (reindex e p) c = some d ∧
      d.config = reindexCfg e p
        ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩ ∧
      d.position = Function.update c.position (p.scan q)
        (c.position (p.scan q) + headDisplacement action) := by
  have hs : (reindex e p).step c.config = some (reindexCfg e p
      ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩) := by
    rw [hc, reindex_step, controlStep_action p q q' action tapes ha]
    rfl
  let d := c.monitor (reindexCfg e p
    ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩)
  have hstep : locatedStep (reindex e p) c = some d := by
    rw [locatedStep, hs]
    rfl
  refine ⟨d, hstep, c.monitor_config _, ?_⟩
  have htransition : (reindex e p).transition (e q)
      (c.config.tapes ((reindex e p).scan (e q))).head = .inr (e q', action) := by
    simp only [hc, reindexCfg, reindex, Equiv.symm_apply_apply, ha]
  have hposition := locatedStep_position_action hstep
    (show c.config.state = .inr (e q) by rw [hc]; rfl) htransition
  simpa only [reindex, Equiv.symm_apply_apply] using hposition

theorem reindex_located_halt {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t)
    (c : LocatedCfg (reindex e p)) (q : Q) (answer : Bool)
    (tapes : Fin t → BitTape)
    (hc : c.config = reindexCfg e p ⟨.inr q, tapes⟩)
    (ha : p.transition q (tapes (p.scan q)).head = .inl answer) :
    ∃ d : LocatedCfg (reindex e p),
      locatedStep (reindex e p) c = some d ∧
      d.config = reindexCfg e p ⟨.inl answer, tapes⟩ ∧ d.position = c.position := by
  have hs : (reindex e p).step c.config =
      some (reindexCfg e p ⟨.inl answer, tapes⟩) := by
    rw [hc, reindex_step, controlStep_halt p q answer tapes ha]
    rfl
  let d := c.monitor (reindexCfg e p ⟨.inl answer, tapes⟩)
  have hstep : locatedStep (reindex e p) c = some d := by
    rw [locatedStep, hs]
    rfl
  refine ⟨d, hstep, c.monitor_config _, ?_⟩
  apply locatedStep_position_halt (answer := answer) hstep
    (show c.config.state = .inr (e q) by rw [hc]; rfl)
  simp only [hc, reindexCfg, reindex, Equiv.symm_apply_apply, ha]

theorem reindex_located_fragment {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t) (count : ℕ)
    (state : ℕ → Q) (tapes : ℕ → Fin t → BitTape) (actions : ℕ → Action) (k : Fin t)
    (scan : ∀ i < count, p.scan (state i) = k)
    (next : ∀ i < count,
      p.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)))
    (c : LocatedCfg (reindex e p))
    (hc : c.config = reindexCfg e p ⟨.inr (state 0), tapes 0⟩) :
    ∃ d : LocatedCfg (reindex e p),
      Trace (locatedStep (reindex e p)) count c d ∧
      d.config = reindexCfg e p ⟨.inr (state count), tapes count⟩ ∧
      d.position = Function.update c.position k
        (c.position k + ∑ i ∈ Finset.range count, headDisplacement (actions i)) := by
  have prefixTrace (n : ℕ) (hn : n ≤ count) :
      ∃ d : LocatedCfg (reindex e p),
        Trace (locatedStep (reindex e p)) n c d ∧
        d.config = reindexCfg e p ⟨.inr (state n), tapes n⟩ ∧
        d.position = Function.update c.position k
          (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)) := by
    induction n with
    | zero =>
        refine ⟨c, .refl c, hc, ?_⟩
        simp only [Finset.sum_range_zero, add_zero]
        change (fun i : Fin t => c.position i) =
          Function.update (fun i : Fin t => c.position i) k (c.position k)
        exact (Function.update_eq_self k (fun i : Fin t => c.position i)).symm
    | succ n ih =>
        have hlt : n < count := by omega
        obtain ⟨middle, htrace, hconfig, hposition⟩ := ih (by omega)
        obtain ⟨ha, htapes⟩ := next n hlt
        obtain ⟨d, hstep, hdconfig, hdposition⟩ := reindex_located_action e p middle
          (state n) (state (n + 1)) (actions n) (tapes n) hconfig
          (by simpa only [scan n hlt] using ha)
        refine ⟨d, htrace.trans (.cons hstep (.refl d)), ?_, ?_⟩
        · simpa only [scan n hlt, ← htapes] using hdconfig
        · rw [scan n hlt, hposition] at hdposition
          rw [hdposition]
          change Function.update
              (Function.update (fun i : Fin t => c.position i) k
                (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)))
              k
              (Function.update (fun i : Fin t => c.position i) k
                  (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)) k +
                headDisplacement (actions n)) =
            Function.update (fun i : Fin t => c.position i) k
              (c.position k + ∑ i ∈ Finset.range (n + 1), headDisplacement (actions i))
          funext i
          by_cases hi : i = k
          · subst i
            simp only [Function.update_self, Finset.sum_range_succ]
            rw [add_assoc]
          · simp only [Function.update_of_ne hi]
  exact prefixTrace count le_rfl

theorem mutation_located_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    (k : Fin s) (q : State r l) (op : Mutation Bool)
    (base : Fin s → BitTape) (tape : BitTape)
    (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (actionCfg (stackProgram p) (codes s) k q op base 0 tape)) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) (mutationActions boolCode op).length c d ∧
      d.config = primitiveControlCfg p
        (actionCfg (stackProgram p) (codes s) k q op base
          ⟨(mutationActions boolCode op).length, Nat.lt_succ_self _⟩
          (execute (mutationActions boolCode op) tape)) ∧
      d.position = Function.update c.position k
        (c.position k + ((mutationActions boolCode op).map headDisplacement).sum) := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let state (i : ℕ) : StackCompiler.State (stackProgram p) (codes s) :=
    acting k q op ⟨min i 2, by
      change min i 2 < 3
      omega⟩
  let tapes (i : ℕ) := Function.update base k
    (execute ((mutationActions boolCode op).take i) tape)
  let actions (i : ℕ) := ((mutationActions boolCode op)[i]?).getD (.write none)
  have hscan : ∀ i < (mutationActions boolCode op).length, C.scan (state i) = k := by
    intro i _
    rfl
  have hnext : ∀ i < (mutationActions boolCode op).length,
      C.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)) := by
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi (mutationActions_length boolCode op)
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      cases op <;>
      simp_all [C, state, tapes, actions, controller, acting, codes, boolCode,
        codeOfBoolEquiv, mutationActions, pushBits, popBits, execute, applyAction,
        Function.update_idem]
  obtain ⟨d, htrace, hconfig, hposition⟩ := reindex_located_fragment e C
    (mutationActions boolCode op).length state tapes actions k hscan hnext c
    (by simpa [primitive, primitiveControlCfg, actionCfg, state, tapes, e, C] using hc)
  refine ⟨d, htrace, ?_, ?_⟩
  · cases op <;>
      simpa [primitive, primitiveControlCfg, actionCfg, state, tapes, e, C, codes,
        mutationActions, boolCode, codeOfBoolEquiv, pushBits, popBits] using hconfig
  · cases op <;>
      simpa [primitive, actions, mutationActions, boolCode, codeOfBoolEquiv, pushBits, popBits,
        Finset.sum_range_succ, headDisplacement] using hposition

theorem reader_located_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    (q : State r l) (base : Fin s → BitTape) (tape : BitTape)
    (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (readCfg (stackProgram p) (codes s) q base (0, fun _ => none) tape)) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) 2 c d ∧
      d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => tape.head) tape) ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let k := selected p q
  let state (i : ℕ) : StackCompiler.State (stackProgram p) (codes s) :=
    reading q (⟨min i 2, by change min i 2 < 3; omega⟩,
      if i = 0 then fun _ => none else fun _ => tape.head)
  let tapes (i : ℕ) := Function.update base k (if i = 1 then tape.move .right else tape)
  let actions (i : ℕ) : Action := if i = 0 then .move .right else .move .left
  have hscan : ∀ i < 2, C.scan (state i) = k := by
    intro i _
    rfl
  have hnext : ∀ i < 2,
      C.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)) := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simp [C, state, tapes, actions, k, controller, reading, stackProgram,
        codes, boolCode, codeOfBoolEquiv, applyAction,
        Function.update_idem]
      congr 4
      congr 2
      funext x
      fin_cases x
      change Function.update (fun _ : Fin 1 => none) 0 tape.head 0 = tape.head
      exact Function.update_self 0 tape.head (fun _ : Fin 1 => none)
    · simp [C, state, tapes, actions, k, controller, reading, stackProgram,
        codes, boolCode, codeOfBoolEquiv, applyAction,
        Function.update_idem]
  obtain ⟨d, htrace, hconfig, hposition⟩ := reindex_located_fragment e C
    2 state tapes actions k hscan hnext c
    (by
      change c.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base (0, fun _ => none) tape)
      exact hc)
  refine ⟨d, htrace, ?_, ?_⟩
  · change d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => tape.head) tape)
    exact hconfig
  · rw [hposition]
    have hsum : ∑ i ∈ Finset.range 2, headDisplacement (actions i) = 0 := by
      norm_num [Finset.sum_range_succ, actions, headDisplacement]
    rw [hsum, add_zero]
    change Function.update (fun i : Fin s => c.position i) k (c.position k) =
      (fun i : Fin s => c.position i)
    exact Function.update_eq_self k (fun i : Fin s => c.position i)

theorem read_entry_located {r s l : ℕ} (p : BitProgram.Program r s l)
    (q : State r l) (base : Fin s → BitTape) (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p ⟨.inr (ready q), base⟩) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) 3 c d ∧
      d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => (base (selected p q)).head)
          (base (selected p q))) ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  obtain ⟨middle, hstep, hconfig, hposition⟩ := reindex_located_action e C c
    (ready q) (reading q (0, fun _ => none))
    (.write (base (selected p q)).head) base hc rfl
  have hscan : C.scan (ready q) = selected p q := rfl
  have hmiddle : middle.config = primitiveControlCfg p
      (readCfg (stackProgram p) (codes s) q base (0, fun _ => none)
        (base (selected p q))) := by
    rw [hscan] at hconfig
    simp only [applyAction, Turing.Tape.write_self, Function.update_eq_self] at hconfig
    simpa [primitive, primitiveControlCfg, readCfg, stackProgram, C, e,
      Function.update_eq_self] using hconfig
  obtain ⟨d, htrace, hdconfig, hdposition⟩ := reader_located_trace p q base
    (base (selected p q)) middle hmiddle
  refine ⟨d, .cons hstep htrace, hdconfig, ?_⟩
  rw [hdposition, hposition]
  simp only [headDisplacement, add_zero]
  change Function.update (fun i : Fin s => c.position i) (C.scan (ready q))
      (c.position (C.scan (ready q))) = (fun i : Fin s => c.position i)
  exact Function.update_eq_self (C.scan (ready q)) (fun i : Fin s => c.position i)

theorem decoder_head (s : ℕ) (k : Fin s) (top : Option Bool) :
    decoder s k (registerBits (fun _ : Fin 1 => top)) = top := by
  cases top <;> rfl

theorem dataTape_head (bits : List Bool) : (dataTape bits).head = bits.head? := by
  cases bits <;> rfl

theorem action_return_located {r s l : ℕ} (p : BitProgram.Program r s l)
    (k : Fin s) (q : State r l) (op : Mutation Bool)
    (base : Fin s → BitTape) (tape : BitTape) (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (actionCfg (stackProgram p) (codes s) k q op base
        ⟨(mutationActions boolCode op).length, Nat.lt_succ_self _⟩ tape)) :
    ∃ d : LocatedCfg (primitive p),
      locatedStep (primitive p) c = some d ∧
      d.config = primitiveControlCfg p ⟨.inr (ready q), Function.update base k tape⟩ ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let phase : Fin 3 := ⟨(mutationActions boolCode op).length,
    Nat.lt_succ_of_le (mutationActions_length boolCode op)⟩
  obtain ⟨d, hstep, hconfig, hposition⟩ := reindex_located_action e C c
    (acting k q op phase) (ready q) (.write tape.head) (Function.update base k tape) hc
    (by simp [C, controller, acting, phase, codes])
  refine ⟨d, hstep, ?_, ?_⟩
  · simpa [primitive, primitiveControlCfg, C, e, controller, acting, applyAction,
      Function.update_idem] using hconfig
  · rw [hposition]
    simp only [headDisplacement, add_zero]
    change Function.update (fun i : Fin s => c.position i) (C.scan (acting k q op phase))
        (c.position (C.scan (acting k q op phase))) = (fun i : Fin s => c.position i)
    exact Function.update_eq_self (C.scan (acting k q op phase))
      (fun i : Fin s => c.position i)

theorem stack_located_step {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : StackCfg (State r l) (fun _ : Fin s => Bool)}
    (hs : stackStep (stackProgram p) a = some b)
    {c : LocatedCfg (primitive p)}
    (hc : c.config = compiledCfg (stackProgram p) (codes s) (decoder s) a) :
    ∃ time ≤ 7, ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) time c d ∧
      d.config = compiledCfg (stackProgram p) (codes s) (decoder s) b ∧
      ∀ i : Fin s, d.position i = c.position i + (a.stk i).length - (b.stk i).length := by
  rcases a with ⟨state, S⟩
  cases state with
  | inl answer => simp [stackStep] at hs
  | inr q =>
    let C := controller (stackProgram p) (codes s) (decoder s)
    let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
    let k := selected p q
    let base := fun i => dataTape (S i)
    let readState : StackCompiler.State (stackProgram p) (codes s) :=
      reading q (⟨2, by change 2 < 3; decide⟩, fun _ => (base k).head)
    have hstart : c.config = primitiveControlCfg p ⟨.inr (ready q), base⟩ := by
      simpa only [compiledCfg, encodeCfg, primitiveControlCfg, tapeEncoding_bool,
        Sum.map_inr, base] using hc
    obtain ⟨readEnd, hread, hreadCfg, hreadPos⟩ := read_entry_located p q base c hstart
    have hr : readEnd.config = reindexCfg e C ⟨.inr readState, base⟩ := by
      simpa [primitiveControlCfg, readCfg, readState, stackProgram, k, C, e] using hreadCfg
    cases ht : transition p q (S k).head? with
    | inl answer =>
      dsimp only [k] at ht
      simp only [stackStep, stackProgram, ht, Option.some.injEq] at hs
      subst b
      obtain ⟨d, hlast, hconfig, hposition⟩ := reindex_located_halt e C readEnd
        readState answer base hr (by
          simp [C, controller, readState, reading, codes, boolCode, codeOfBoolEquiv,
            stackProgram, decoder_head, base, dataTape_head, k, ht])
      refine ⟨4, by omega, d, hread.trans (.cons hlast (.refl d)), ?_, ?_⟩
      · simpa only [primitive, compiledCfg, encodeCfg, primitiveControlCfg, tapeEncoding_bool,
          Sum.map_inl, id_eq, base, e, C] using hconfig
      · intro i
        rw [hposition, hreadPos]
        change c.position i = c.position i + (S i).length - (S i).length
        omega
    | inr output =>
      rcases output with ⟨q', op⟩
      dsimp only [k] at ht
      simp only [stackStep, stackProgram, ht, Option.some.injEq] at hs
      subst b
      obtain ⟨actionStart, hdispatch, hdispatchCfg, hdispatchPos⟩ :=
        reindex_located_action e C readEnd readState (acting k q' op 0)
          (.write (base k).head) base hr (by
            simp [C, controller, readState, reading, codes, boolCode, codeOfBoolEquiv,
              stackProgram, decoder_head, base, dataTape_head, k, ht]
            rfl)
      have hactionStart : actionStart.config = primitiveControlCfg p
          (actionCfg (stackProgram p) (codes s) k q' op base 0 (base k)) := by
        simpa [primitiveControlCfg, actionCfg, readState, C, e, controller, reading,
          stackProgram, k, applyAction, Function.update_eq_self] using hdispatchCfg
      have hdispatchPosition : actionStart.position = readEnd.position := by
        rw [hdispatchPos]
        simp only [headDisplacement, add_zero]
        change Function.update (fun i : Fin s => readEnd.position i) (C.scan readState)
            (readEnd.position (C.scan readState)) = (fun i : Fin s => readEnd.position i)
        exact Function.update_eq_self (C.scan readState) (fun i : Fin s => readEnd.position i)
      obtain ⟨actionEnd, haction, hactionCfg, hactionPos⟩ :=
        mutation_located_trace p k q' op base (base k) actionStart hactionStart
      obtain ⟨d, hreturn, hreturnCfg, hreturnPos⟩ := action_return_located p k q' op
        base (execute (mutationActions boolCode op) (base k)) actionEnd hactionCfg
      have htape : execute (mutationActions boolCode op) (base k) =
          dataTape (op.apply (S k)) := by
        simpa only [base, encodeDataStack_boolCode] using mutationActions_correct boolCode op (S k)
      refine ⟨3 + (1 + ((mutationActions boolCode op).length + 1)), ?_, d,
        hread.trans ((Trace.cons hdispatch (Trace.refl actionStart)).trans
          (haction.trans (.cons hreturn (.refl d)))), ?_, ?_⟩
      · have hlength := mutationActions_length boolCode op
        change (mutationActions boolCode op).length ≤ 2 at hlength
        omega
      · rw [htape] at hreturnCfg
        change d.config = primitiveControlCfg p
          ⟨.inr (ready q'), fun i => dataTape (encodeDataStack boolCode
            ((Function.update S k (op.apply (S k))) i))⟩
        simp_rw [encodeDataStack_boolCode]
        have htapes : (fun i => dataTape ((Function.update S k (op.apply (S k))) i)) =
            Function.update base k (dataTape (op.apply (S k))) :=
          Function.comp_update dataTape S k (op.apply (S k))
        rw [htapes]
        exact hreturnCfg
      · intro i
        rw [hreturnPos, hactionPos, hdispatchPosition, hreadPos]
        rw [transition_mutation_displacement p q q' op (S k) ht
          headDisplacement rfl rfl (fun _ => rfl)]
        change Function.update c.position k
          (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) i =
            c.position i + (S i).length - ((Function.update S k (op.apply (S k))) i).length
        by_cases hi : i = k
        · subst i
          change Function.update (fun j : Fin s => c.position j) k
              (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) k =
            c.position k + (S k).length -
              (Function.update S k (op.apply (S k)) k).length
          simp only [Function.update_self]
          omega
        · change Function.update (fun j : Fin s => c.position j) k
              (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) i =
            c.position i + (S i).length -
              (Function.update S k (op.apply (S k)) i).length
          simp only [Function.update_of_ne hi]
          omega

theorem primitive_located_step {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} (hs : BitProgram.step p a = some b)
    {c : LocatedCfg (primitive p)} (hc : c.config = primitiveCfg p a) :
    ∃ time ≤ 7, ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) time c d ∧ d.config = primitiveCfg p b ∧
      ∀ i : Fin s, d.position i = c.position i + (a.stacks i).length - (b.stacks i).length := by
  apply stack_located_step p (a := stackCfg p a) (b := stackCfg p b) _ hc
  rw [stack_step, hs]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler


/-! Transfer a genuine bound on every source stack configuration through the
guarded primitive compiler. The bound is independent of the number of source
instructions. Concrete counting programs must prove the source invariant. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

open GuardedCompiler
open scoped BigOperators

private theorem compile_trace_envelope {r s l : ℕ} (p : BitProgram.Program r s l)
    (anchor : Fin s → ℤ) (bound inputLength : ℕ)
    (hanchor : ∀ i, 0 ≤ anchor i ∧ anchor i ≤ (inputLength : ℤ))
    {a b : BitProgram.Cfg r s l} {sourceSteps : ℕ}
    (tr : BitProgram.Trace p sourceSteps a b) {c : LocatedCfg (primitive p)}
    (hcfg : c.config = primitiveCfg p a)
    (hposition : ∀ i, c.position i = anchor i - ((a.stacks i).length : ℤ))
    (henvelope : ∀ i, -(bound : ℤ) - 7 ≤ c.lower i ∧
      c.upper i ≤ (inputLength : ℤ) + 7)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time c d ∧
      d.config = primitiveCfg p b ∧
      (∀ i, d.position i = anchor i - ((b.stacks i).length : ℤ)) ∧
      ∀ i, -(bound : ℤ) - 7 ≤ d.lower i ∧
        d.upper i ≤ (inputLength : ℤ) + 7 := by
  induction tr generalizing c with
  | refl => exact ⟨0, by omega, c, .refl c, hcfg, hposition, henvelope⟩
  | @cons sourceSteps a next final hs ht ih =>
      obtain ⟨time₁, htime₁, middle, hrun₁, hcfg₁, hshift⟩ :=
        primitive_located_step p hs hcfg
      have hposition₁ : ∀ i,
          middle.position i = anchor i - ((next.stacks i).length : ℤ) := by
        intro i
        rw [hshift i, hposition i]
        omega
      have henvelope₁ : ∀ i, -(bound : ℤ) - 7 ≤ middle.lower i ∧
          middle.upper i ≤ (inputLength : ℤ) + 7 := by
        apply locatedTrace_envelope_of_margin hrun₁ htime₁
          (fun _ => -(bound : ℤ) - 7) (fun _ => (inputLength : ℤ) + 7) henvelope
        intro i
        have hlength := hstacks 0 a (by omega) (.refl a) i
        have ha := hanchor i
        rw [hposition i]
        omega
      have hstacks₁ : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
          BitProgram.Trace p prefixSteps next intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace
        exact hstacks (prefixSteps + 1) intermediate (by omega) (.cons hs htrace)
      obtain ⟨time₂, htime₂, d, hrun₂, hcfg₂, hposition₂, henvelope₂⟩ :=
        ih hcfg₁ hposition₁ henvelope₁ hstacks₁
      exact ⟨time₁ + time₂, by omega, d, hrun₁.trans hrun₂,
        hcfg₂, hposition₂, henvelope₂⟩

theorem compile_trace_space {r s l : ℕ} (p : BitProgram.Program r s l)
    {input : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config = primitiveCfg p final ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  let anchor : Fin s → ℤ := fun i => if i = p.inputStack then input.length else 0
  have hanchor : ∀ i, 0 ≤ anchor i ∧ anchor i ≤ (input.length : ℤ) := by
    intro i
    dsimp [anchor]
    split_ifs <;> omega
  have hposition : ∀ i : Fin s, (locatedInit (primitive p) input).position i =
      anchor i - (((BitProgram.initial p input).stacks i).length : ℤ) := by
    intro i
    by_cases hi : i = p.inputStack <;> simp [locatedInit, anchor, hi]
  have henvelope : ∀ i, -(bound : ℤ) - 7 ≤ (locatedInit (primitive p) input).lower i ∧
      (locatedInit (primitive p) input).upper i ≤ (input.length : ℤ) + 7 := by
    intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  obtain ⟨time, htime, d, hrun, hcfg, _, hspace⟩ :=
    compile_trace_envelope p anchor bound input.length hanchor tr
      (primitive_initial p input).symm hposition henvelope hstacks
  refine ⟨time, htime, d, hrun, hcfg, ?_⟩
  intro prefixSteps intermediate hle hprefix
  apply (locatedTrace_prefix_space hrun hprefix hle).trans
  apply (visitedSpace_le_of_envelope d _ _ hspace).trans
  have hwidth : ((input.length : ℤ) + 7 - (-(bound : ℤ) - 7) + 1).toNat =
      bound + input.length + 15 := by omega
  simp only [hwidth, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_rfl

/-- Full output-word readback, time, and every-prefix visited space refer to
one and the same primitive execution. The actual source trace and source-stack
invariant must be provided by the concrete counting program. -/
theorem compile_word_space {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config.state = .inl (output.head?.getD false) ∧
      d.config.tapes p.outputStack = Turing.Tape.mk₁ (output.map some) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  obtain ⟨time, htime, d, hrun, hcfg, hspace⟩ := compile_trace_space p tr hstacks
  refine ⟨time, htime, d, hrun, ?_, ?_, hspace⟩
  · rw [hcfg, primitive_halted p final halted, hout]
  · rw [hcfg, primitive_tape, hout]

/-- A full word on an arbitrary fixed tape and a separate Boolean halt are
preserved by the same execution used for both resource bounds. -/
theorem compile_word_answer_space {r s l : ℕ} (p : BitProgram.Program r s l)
    (countStack : Fin s) {input word : List Bool} {answer : Bool}
    {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hword : final.stacks countStack = word)
    (hanswer : final.stacks p.outputStack = [answer])
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config.state = .inl answer ∧
      d.config.tapes countStack = Turing.Tape.mk₁ (word.map some) ∧
      d.config.tapes p.outputStack = Turing.Tape.mk₁ [some answer] ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  obtain ⟨time, htime, d, hrun, hcfg, hspace⟩ := compile_trace_space p tr hstacks
  refine ⟨time, htime, d, hrun, ?_, ?_, ?_, hspace⟩
  · rw [hcfg, primitive_halted p final halted, hanswer]
    rfl
  · rw [hcfg, primitive_tape, hword]
  · rw [hcfg, primitive_tape, hanswer]
    rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace


/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

private theorem base_entry_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l) :
    StructuredProgram.entry c (label ∘ embed) (label exit) =
      label (StructuredProgram.entry c embed exit) := by
  induction c generalizing l L with
  | skip => rfl
  | atom => rfl
  | seq first second ihf ihs =>
      change StructuredProgram.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem base_code_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (site : StructuredProgram.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredProgram.code c embed exit site) =
      StructuredProgram.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | skip => exact site.elim
  | atom op => cases op <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredProgram.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [base_entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredProgram.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (base_entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (base_entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (base_entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem entry_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l) :
    StructuredCalls.entry c (label ∘ embed) (label exit) =
      label (StructuredCalls.entry c embed exit) := by
  induction c generalizing l L with
  | base c => exact base_entry_map c label embed exit
  | call => rfl
  | seq first second ihf ihs =>
      change StructuredCalls.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem code_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (site : StructuredCalls.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredCalls.code c embed exit site) =
      StructuredCalls.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | base c => exact base_code_map c label embed exit site
  | call p =>
      simp only [StructuredCalls.code]
      cases p.code site <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredCalls.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredCalls.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

private def commandLabel {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    Fin (StructuredCalls.size c + 1) → Fin L := fun pc =>
  match (StructuredCalls.labelEquiv c).symm pc with
  | none => exit
  | some site => embed site

@[simp] private theorem commandLabel_site {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (site : StructuredCalls.Site c) :
    commandLabel c embed exit (StructuredCalls.siteAddress c site) = embed site := by
  change (match (StructuredCalls.siteEquiv c).optionCongr.symm
    ((StructuredCalls.siteEquiv c).optionCongr (some site)) with
    | none => exit
    | some site => embed site) = embed site
  rw [Equiv.symm_apply_apply]

@[simp] private theorem commandLabel_exit {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit (StructuredCalls.exitAddress c) = exit := by
  change (match (StructuredCalls.siteEquiv c).optionCongr.symm
    ((StructuredCalls.siteEquiv c).optionCongr none) with
    | none => exit
    | some site => embed site) = exit
  rw [Equiv.symm_apply_apply]

private theorem commandLabel_sites {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit ∘ StructuredCalls.siteAddress c = embed := by
  funext site
  exact commandLabel_site c embed exit site

private theorem commandLabel_entry {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s) :
    commandLabel c embed exit (StructuredCalls.compiled c inputStack outputStack).entry =
      StructuredCalls.entry c embed exit := by
  change commandLabel c embed exit
    (StructuredCalls.entry c (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)) = _
  rw [← entry_map c (commandLabel c embed exit) (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c), commandLabel_sites, commandLabel_exit]

private theorem commandLabel_code {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site)
    (pc : Fin (StructuredCalls.size c + 1)) (hpc : pc ≠ StructuredCalls.exitAddress c) :
    caller.code (commandLabel c embed exit pc) =
      ProgramLinking.relocateInstr id id (commandLabel c embed exit) none
        ((StructuredCalls.compiled c inputStack outputStack).code pc) := by
  obtain ⟨site, rfl⟩ : ∃ site, pc = StructuredCalls.siteAddress c site := by
    cases heq : (StructuredCalls.labelEquiv c).symm pc with
    | none =>
        have hp := congrArg (StructuredCalls.labelEquiv c) heq
        exact (hpc (by simpa [StructuredCalls.exitAddress] using hp)).elim
    | some site =>
        exact ⟨site, by simpa [StructuredCalls.siteAddress] using
          (congrArg (StructuredCalls.labelEquiv c) heq)⟩
  rw [commandLabel_site, StructuredCalls.compiled_site, code_map,
    commandLabel_sites, commandLabel_exit]
  exact hcode site

/-- A bound proved for one compiled structured block transfers to every
installation of that same block in a finite caller table. No bound on the
caller's total runtime is used. -/
theorem command_stack_bound {r s L : ℕ} {c : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval c steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled c inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled c inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry c embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  let routine := StructuredCalls.compiled c inputStack outputStack
  let label := commandLabel c embed exit
  let frame := a.withPC (some (StructuredCalls.entry c embed exit))
  have full := StructuredCalls.compiled_trace heval inputStack outputStack
  obtain ⟨source, hs⟩ := trace_prefix_exists full hle
  have hactive : source.pc ≠ none := by
    intro hnone
    have halted := ProgramLinking.trace_from_halted routine (trace_suffix full hs hle) hnone
    change some (StructuredCalls.exitAddress c) = none at halted
    cases halted
  have htable : ∀ pc, routine.code pc ≠ .halt →
      caller.code (label pc) = ProgramLinking.relocateInstr id id label none (routine.code pc) := by
    intro pc hnot
    apply commandLabel_code c caller embed exit inputStack outputStack hcode pc
    intro heq
    subst pc
    exact hnot (StructuredCalls.compiled_exit c inputStack outputStack)
  have hrelocated := ProgramLinking.relocate_trace_before_halt routine caller id id
    label none frame Function.injective_id Function.injective_id htable hs hactive
  have hinitial : ProgramLinking.embedCfg id id label none frame
      (a.withPC (some routine.entry)) = frame := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, routine, label, frame,
      StructuredProgram.State.withPC, commandLabel_entry]
  rw [hinitial] at hrelocated
  have heq := trace_same_length_unique hp hrelocated
  rw [heq]
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- Sequential command blocks share one uniform space bound. -/
theorem sequence_stack_bound {r s L : ℕ} {first second : StructuredCalls.Cmd r s}
    {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (hf : StructuredCalls.Eval first n a b) (hs : StructuredCalls.Eval second m b c)
    (inputStack outputStack : Fin s)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled first inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled first inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled second inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled second inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.seq first second) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.seq first second) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.seq first second) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  exact trace_prefix_bound_trans
    (StructuredCalls.eval_trace hf caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hf inputStack outputStack hfirst caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hs inputStack outputStack hsecond caller (embed ∘ Sum.inr)
      exit (fun q => hcode (.inr q)))

/-- A loop induction combines its current body and remaining iterations by
maximum space; the number of completed iterations never multiplies the bound. -/
theorem while_true_stack_bound {r s L : ℕ} {body : StructuredCalls.Cmd r s}
    {test : Fin r} {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (htest : a.regs test = true)
    (hb : StructuredCalls.Eval body n a b)
    (hw : StructuredCalls.Eval (.while test body) m b c)
    (inputStack outputStack : Fin s)
    (hbody : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hwhile : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := n + m)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry body (embed ∘ some) (embed none)))) ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hbody 0 _ (Nat.zero_le n) (.refl _)
  · exact trace_prefix_bound_trans
      (StructuredCalls.eval_trace hb caller (embed ∘ some) (embed none)
        (fun q => hcode (some q)))
      (command_stack_bound hb inputStack outputStack hbody caller (embed ∘ some)
        (embed none) (fun q => hcode (some q)))
      (command_stack_bound hw inputStack outputStack hwhile caller embed exit hcode)

theorem while_false_stack_bound {r s L : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) {bound : ℕ} (a : StructuredCalls.State r s)
    (htest : a.regs test = false) (hstart : ∀ i, (a.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := 0)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some exit)) ?_ hstart ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · intro prefixSteps intermediate hle hp
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hp
    exact hstart

theorem conditional_true_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = true) (heval : StructuredCalls.Eval yes steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled yes inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled yes inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry yes (fun q => embed (some (.inl q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q)))

theorem conditional_false_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = false) (heval : StructuredCalls.Eval no steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled no inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled no inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry no (fun q => embed (some (.inr q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q)))

/-- A boundary invariant and a uniform actual-body prefix bound establish the
same space bound through any finite number of loop iterations. -/
theorem loop_stack_bound {r s : ℕ} (body : StructuredCalls.Cmd r s) (test : Fin r)
    (inputStack outputStack : Fin s) (I : StructuredCalls.State r s → Prop) (bound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hpreserve : ∀ n a b, StructuredCalls.Eval body n a b → I a →
      a.regs test = true → I b)
    (hbody : ∀ n a b, StructuredCalls.Eval body n a b → I a → a.regs test = true →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
          (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval (.while test body) steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  induction steps using Nat.strong_induction_on generalizing a b with
  | h steps ih =>
      cases heval with
      | while_false htest =>
          exact while_false_stack_bound body test a htest (hinitial a ha)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)
      | @while_true _ _ n m a middle b htest hb hw =>
          have hmiddle := hpreserve n a middle hb ha htest
          exact while_true_stack_bound htest hb hw inputStack outputStack
            (hbody n a middle hb ha htest) (ih m (by omega) hw hmiddle)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

/-- The local runtime estimate applies to one concrete routine invocation.
Reusing it in an outer loop requires its boundary input bound on every call. -/
theorem local_stack_bound {r s l : ℕ} (p : Program r s l)
    {a : Cfg r s l} {steps initialBound : ℕ}
    (ha : dataBits a ≤ initialBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ initialBound + steps := by
  intro prefixSteps intermediate hle hp i
  have hsum : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have hgrowth := trace_dataBits p hp
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

open GuardedCompiler

/-- Direct interface used by the DLP targets: one actual source trace and
an all-prefix source-stack invariant produce the required bounded primitive
run. In particular the source and target resource claims refer to the same run. -/
theorem compile_runsWithin {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    DetDLP.RunsWithin (primitive p) p.outputStack input output
      ((7 * sourceSteps : ℕ) : ℝ) ((s * (bound + input.length + 15) : ℕ) : ℝ) := by
  obtain ⟨time, htime, d, htrace, hhalt, hword, hspace⟩ :=
    compile_word_space p tr halted hout hstacks
  refine ⟨time, d, htrace, ⟨_, hhalt⟩, hword, ?_, ?_⟩
  · exact_mod_cast htime
  · intro prefixSteps intermediate hle hprefix
    exact_mod_cast hspace prefixSteps intermediate hle hprefix

/-- The direct interface with externally chosen real-valued budgets. -/
theorem compile_runsWithin_of_le {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {final : BitProgram.Cfg r s l}
    {sourceSteps bound : ℕ} {τ σ : ℝ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (ht : ((7 * sourceSteps : ℕ) : ℝ) ≤ τ)
    (hs : ((s * (bound + input.length + 15) : ℕ) : ℝ) ≤ σ) :
    DetDLP.RunsWithin (primitive p) p.outputStack input output τ σ := by
  obtain ⟨time, d, htrace, hhalt, hword, htime, hspace⟩ :=
    compile_runsWithin p tr halted hout hstacks
  exact ⟨time, d, htrace, hhalt, hword, htime.trans ht,
    fun n c hn hc => (hspace n c hn hc).trans hs⟩

/-- Polynomial-time local routines need no separate source-space invariant:
each instruction grows total stack data by at most one bit. This theorem
must NOT be used to infer polynomial space from subexponential running time. -/
theorem compile_runsWithin_from_time {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output) :
    DetDLP.RunsWithin (primitive p) p.outputStack input output
      ((7 * sourceSteps : ℕ) : ℝ)
      ((s * ((input.length + sourceSteps) + input.length + 15) : ℕ) : ℝ) := by
  apply compile_runsWithin p tr halted hout
  apply StructuredSpace.local_stack_bound p
  simp only [BitProgram.initial_dataBits]
  exact le_rfl

/-- Read a whole word from any chosen source stack while the output stack
contains the Boolean halt answer. The arbitrary tape is retained by compilation. -/
theorem compile_word_answer_runsWithin {r s l : ℕ} (p : BitProgram.Program r s l)
    (wordStack : Fin s) {input word : List Bool} {answer : Bool}
    {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hword : final.stacks wordStack = word)
    (hanswer : final.stacks p.outputStack = [answer])
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    DetDLP.RunsWithin (primitive p) wordStack input word
      ((7 * sourceSteps : ℕ) : ℝ) ((s * (bound + input.length + 15) : ℕ) : ℝ) := by
  obtain ⟨time, htime, d, htrace, hhalt, hread, _, hspace⟩ :=
    compile_word_answer_space p wordStack tr halted hword hanswer hstacks
  refine ⟨time, d, htrace, ⟨answer, hhalt⟩, hread, ?_, ?_⟩
  · exact_mod_cast htime
  · intro n c hn hc
    exact_mod_cast hspace n c hn hc

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

namespace DetDLP.BitCompilerCheck

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- A concrete source program: halt immediately without changing the raw input. -/
def echoProgram : BitProgram.Program 0 1 1 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code _ := .halt

theorem echo_trace (input : List Bool) :
    BitProgram.Trace echoProgram 1 (BitProgram.initial echoProgram input)
      (BitProgram.terminal echoProgram input) := by
  exact .cons rfl (.refl _)

/-- End-to-end sanity theorem: a concrete finite instruction table, not an
abstract realizer assumption, is compiled into a genuine bounded primitive run. -/
theorem echo_runsWithin (input : List Bool) :
    RunsWithin (GuardedCompiler.primitive echoProgram) (0 : Fin 1) input input
      7 ((2 * input.length + 16 : ℕ) : ℝ) := by
  simpa [echoProgram, Nat.mul_one, Nat.one_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, two_mul] using
    CompileSpace.compile_runsWithin_from_time echoProgram (echo_trace input) rfl rfl

end DetDLP.BitCompilerCheck

#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_runsWithin
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_runsWithin_of_le
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_runsWithin_from_time
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_runsWithin
#print axioms DetDLP.BitCompilerCheck.echo_runsWithin


