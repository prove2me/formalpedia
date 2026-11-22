-- Prove2me | solution 1 for Auto.integrable_of_le_gdom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:51:30.78978+00:00
-- url     : https://prove2.me/submissions/e171e351-adc9-4938-a690-69d9eb4a63cb

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_integrable_gdom

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ p, |f p| ≤ C * gdom ε p) :
    Integrable f := ((integrable_gdom hε).const_mul C).mono' hf.aestronglyMeasurable
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb p)
end Auto
