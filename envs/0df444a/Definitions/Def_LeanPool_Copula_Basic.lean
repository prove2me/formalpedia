-- Prove2me | Definitions.Def_LeanPool_Copula_Basic
-- name    : LeanPool_Copula_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:28.168005+00:00
-- url     : https://prove2.me/theorems/b05b2d73-58e9-440a-876d-81c62f8dbfce
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory
open scoped unitInterval
namespace ProbabilityTheory
structure Copula (d : ℕ) where
  /-- The probability measure underlying the copula. -/
  measure : ProbabilityMeasure (Fin d → I)
  /-- Every coordinate has the uniform distribution on the unit interval. -/
  marginal_eq (i : Fin d) : measure.toMeasure.map (fun x => x i) = volume
namespace Copula
variable {d : ℕ}
@[expose]
def toMeasure (C : Copula d) : Measure (Fin d → I) := C.measure.toMeasure
instance (C : Copula d) : IsProbabilityMeasure C.toMeasure :=
  inferInstanceAs (IsProbabilityMeasure C.measure.toMeasure)
@[expose]
noncomputable def ofMap {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → Fin d → I) (hX : Measurable X)
    (hmarg : ∀ i, μ.toMeasure.map (fun ω => X ω i) = volume) : Copula d where
  measure := μ.map hX.aemeasurable
  marginal_eq i := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (measurable_pi_apply i) hX]
    exact hmarg i
end Copula
end ProbabilityTheory


