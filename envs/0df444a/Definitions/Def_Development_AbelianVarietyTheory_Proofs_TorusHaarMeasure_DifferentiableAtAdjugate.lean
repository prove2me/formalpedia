-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:40.539799+00:00
-- url     : https://prove2.me/theorems/5503db79-e11e-4950-af1c-2fc80653b740
-- title:
--   Differentiable At Adjugate
-- statement:
--   Definitions and structural lemmas for Differentiable At Adjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.UnitriJac
open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
noncomputable section
abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}
def lowMat {r : ℕ} (u : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a c => if h : c < a then u ⟨(a, c), h⟩ else 0
def leftM {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) : Matrix (Low r) (Low r) ℂ :=
  Matrix.of fun p q : Low r => if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0
def adM {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) : Matrix (Low r) (Low r) ℂ :=
  Matrix.of fun p q : Low r => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def crd {r : ℕ} (X : Data E r) (v : V (nd X)) (τ : X.Ψ) : Low r → ℂ :=
  fun p => v ((Fintype.equivFin (Ent X)) ⟨τ, p⟩)
end
end GlobalTheory.UnitriJac


