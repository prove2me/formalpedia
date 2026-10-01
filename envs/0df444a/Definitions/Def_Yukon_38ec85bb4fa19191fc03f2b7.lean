-- Prove2me | Definitions.Def_Yukon_38ec85bb4fa19191fc03f2b7
-- name    : Yukon_38ec85bb4fa19191fc03f2b7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:03:07.999033+00:00
-- url     : https://prove2.me/theorems/94b31455-2733-4b2b-a47c-6af5fb5ddb22
-- title:
--   YukonModule.PolyFun.PFunctor.Dynamical.Simulation.part0
-- statement:
--   Source module PolyFun.PFunctor.Dynamical.Simulation.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Dynamical/Simulation.lean
--
--   yukon-proof-operation:2a872666abbc01a16bb77bc48b11498caec104dab5390c2a00bd43c063deccb3
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MmE4NzI2NjZhYmJjMDFhMTZiYjc3YmM0OGIxMTQ5OGNhZWMxMDRkYWI1MzkwYzJhMDBiZDQzYzA2M2RlY2NiMyIsImhhc2giOiI5YmM4MDIyOWZjNmE1OTdlN2FjNTk3NTc3ZTdiMTBlNDcyMjk0ZGY5YWI3N2IxNzE0YWRhMjE4YmQ1ZTQyZjZhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8zOGVjODViYjRmYTE5MTkxZmMwM2YyYjciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Definitions.Def_Yukon_f4aa983659c0ad198a975e5b



public import Mathlib.Data.PFunctor.Univariate.M
public import Init
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Equiv.Prod
meta import Definitions.Def_Yukon_f4aa983659c0ad198a975e5b
set_option backward.isDefEq.respectTransparency.types false
/-!
# Simulations between dynamical systems

A **simulation** of one `p`-dynamical system by another is a relation on their
states that is preserved by a single synchronized step and matches the exposed
positions. Because `M p` is the terminal `p.Obj`-coalgebra, a simulation forces
related states to have equal `behavior` trees — the coinductive
`behavior_eq_of_isSimulation`, proved via the bisimulation principle
`M.corec_eq_corec`. This is the interface-generic core of the step-synchronized
simulation method VCVio's oracle machines use to discharge `Implements`.

The relation is step-synchronized (one `D₁` step matches exactly one `D₂` step).
A stutter-budget variant (several `D₂` steps per `D₁` step) is a later addition,
needed once looping / sequential composition introduces silent steps.

Coalgebra morphisms (`Coalg.Hom`) are the functional instances of this notion:
`isSimulation_graph` shows the graph of a map commuting with the structure maps
is a simulation, so morphisms preserve behaviour (`behavior_coalgHom`). The
lax, existential counterpart between bare systems — matching concrete steps by
a `StepRel` — is `DynSystem.ForwardSimulation` in
`PolyFun/PFunctor/Dynamical/Refinement.lean`. The optional verification layer is
`SafetySpec` / `SafetyRefinement`, which adds initial-state, assumption, and
safety obligations. `ForwardSimulation.ofIsSimulation` embeds a synchronized
simulation at the relation `StepRel.sync`.
-/

@[expose] public section

universe u₁ u₂ uA uB

namespace PFunctor

namespace DynSystem

variable {S₁ : Type u₁} {S₂ : Type u₂} {p : PFunctor.{uA, uB}}

/-- `IsSimulation D₁ D₂ R`: the relation `R` on states is a **simulation** —
related states expose the same position, and the two systems' updates carry
related states to related states (with the `D₁`-direction transported along the
shared exposed position). -/
structure IsSimulation (D₁ : DynSystem S₁ p) (D₂ : DynSystem S₂ p)
    (R : S₁ → S₂ → Prop) : Prop where
  /-- Related states expose the same `p`-position. -/
  expose_eq : ∀ {s₁ s₂}, R s₁ s₂ → D₁.expose s₁ = D₂.expose s₂
  /-- One synchronized step preserves the relation. -/
  update_rel : ∀ {s₁ s₂} (h : R s₁ s₂) (d : p.B (D₁.expose s₁)),
      R (D₁.update s₁ d) (D₂.update s₂ (expose_eq h ▸ d))

/-- **A simulation preserves behaviour.** If `R` is a simulation and `R s₁ s₂`,
the two states have the same behaviour tree; hence they are observationally
equivalent (`ObsEq`). Proved by the terminal-coalgebra bisimulation principle. -/
theorem behavior_eq_of_isSimulation {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p}
    {R : S₁ → S₂ → Prop} (hsim : IsSimulation D₁ D₂ R)
    {s₁ : S₁} {s₂ : S₂} (h : R s₁ s₂) :
    D₁.behavior s₁ = D₂.behavior s₂ := by
  refine M.corec_eq_corec D₁.out D₂.out R s₁ s₂ h (fun x y hxy => ?_)
  have he : D₁.expose x = D₂.expose y := hsim.expose_eq hxy
  refine ⟨D₁.expose x, D₁.update x, fun d => D₂.update y (he ▸ d), rfl, ?_,
    hsim.update_rel hxy⟩
  simp only [DynSystem.out]
  refine Sigma.ext he.symm (Function.hfunext (congrArg p.B he.symm) fun a a' hab => ?_)
  exact heq_of_eq (congrArg (D₂.update y) (eq_of_heq (hab.trans (eqRec_heq he a').symm)))

/-- Simulation-related states are observationally equivalent. -/
theorem obsEq_of_isSimulation {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p}
    {R : S₁ → S₂ → Prop} (hsim : IsSimulation D₁ D₂ R)
    {s₁ : S₁} {s₂ : S₂} (h : R s₁ s₂) : ObsEq D₁ D₂ s₁ s₂ :=
  behavior_eq_of_isSimulation hsim h

/-! ## Coalgebra morphisms as simulations -/

/-- The graph of a map commuting with the coalgebra structure maps is a
simulation: coalgebra morphisms are the functional forward simulations. -/
theorem isSimulation_graph {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p} (f : S₁ → S₂)
    (hf : ∀ st, D₂.out (f st) = p.map f (D₁.out st)) :
    IsSimulation D₁ D₂ (fun st₁ st₂ => f st₁ = st₂) := by
  have hexpose : ∀ st, D₂.expose (f st) = D₁.expose st :=
    fun st => congrArg Sigma.fst (hf st)
  have hupdate : ∀ st, HEq (D₂.update (f st)) (f ∘ D₁.update st) :=
    fun st => congr_arg_heq Sigma.snd (hf st)
  refine ⟨fun {st₁ st₂} h => h ▸ (hexpose st₁).symm, fun {st₁ st₂} h d => ?_⟩
  subst h
  exact (congr_heq (hupdate st₁) (eqRec_heq _ d)).symm

/-- A coalgebra morphism between the state coalgebras of two `p`-systems is a
functional simulation: its graph is a simulation. The coalgebra structures are
the systems' own (`DynSystem.coalg`), supplied locally: with the state set a
parameter, the system no longer determines them by instance synthesis. -/
theorem isSimulation_graph_coalgHom {S₂' : Type u₁}
    {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂' p} :
    letI := D₁.coalg
    letI := D₂.coalg
    ∀ f : Coalg.Hom p.Obj S₁ S₂', IsSimulation D₁ D₂ (fun st₁ st₂ => f st₁ = st₂) := by
  letI := D₁.coalg
  letI := D₂.coalg
  exact fun f => isSimulation_graph f fun st => (congrFun f.comm st).symm

/-- Coalgebra morphisms preserve behaviour trees. -/
theorem behavior_coalgHom {S₂' : Type u₁}
    {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂' p} :
    letI := D₁.coalg
    letI := D₂.coalg
    ∀ f : Coalg.Hom p.Obj S₁ S₂', ∀ st : S₁, D₂.behavior (f st) = D₁.behavior st := by
  letI := D₁.coalg
  letI := D₂.coalg
  exact fun f st =>
    (behavior_eq_of_isSimulation (isSimulation_graph_coalgHom f) rfl).symm

end DynSystem

end PFunctor


