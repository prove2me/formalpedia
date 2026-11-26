-- Prove2me | Definitions.Def_Malliavin_Simplex
-- name    : Malliavin_Simplex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:42:12.733322+00:00
-- url     : https://prove2.me/theorems/03580bcc-f381-5dbf-a77a-945d47979ff4
-- title:
--   Simplex
-- statement:
--   Definitions and structural lemmas for Simplex, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean

import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
namespace Malliavin
variable {T : Type*} {E : Type*}
def diagonal (T : Type*) (n : ℕ) : Set (Fin n → T) :=
  {t | ¬ Function.Injective t}
section Order
variable [LinearOrder T]
def simplex (T : Type*) [LinearOrder T] (n : ℕ) : Set (Fin n → T) :=
  {t | StrictMono t}
def sortedBy (T : Type*) [LinearOrder T] (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → T) :=
  (fun t : Fin n → T => t ∘ σ) ⁻¹' simplex T n
end Order
section MeasurableComp
variable [MeasurableSpace T]
end MeasurableComp
section Measurable
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
end Measurable
section Integral
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
end Integral
end Malliavin
end


