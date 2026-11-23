-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:24.480611+00:00
-- url     : https://prove2.me/theorems/2a4aef4b-0f98-4f5d-81de-6a714027063f
-- title:
--   In NOf Mem
-- statement:
--   Definitions and structural lemmas for In NOf Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
section Mod
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def NV (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V :=
  ⨆ i : Pos n, LinearMap.range (E i.1.1 i.1.2)
def JJ (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {T | ∀ x, T x ∈ NV E}
  add_mem' ha hb x := (NV E).add_mem (ha x) (hb x)
  zero_mem' _ := (NV E).zero_mem
  smul_mem' c _ h x := (NV E).smul_mem c (h x)
def HH (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V := ∑ c : Fin n, ((c : ℕ) : ℂ) • E c c
def adH (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Module.End ℂ V) :=
  LinearMap.mulLeft ℂ (HH E) - LinearMap.mulRight ℂ (HH E)
def PP (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ k : ℕ, adH E T = ((k : ℂ) + 1) • T}
end Mod
inductive Low : FreeAlgebra ℂ (Fin n × Fin n) → Prop
  | one : Low 1
  | mul (u) (p : Fin n × Fin n) : Low u → p.2 ≤ p.1 → Low (u * FreeAlgebra.ι ℂ p)
  | add (u v) : Low u → Low v → Low (u + v)
  | smul (c : ℂ) (u) : Low u → Low (c • u)
def Red (a : FreeAlgebra ℂ (Fin n × Fin n)) : Prop :=
  ∃ u, Low u ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E a - ev E u ∈ JJ E
end GlobalTheory.CompanionTheory.HCdecomp


