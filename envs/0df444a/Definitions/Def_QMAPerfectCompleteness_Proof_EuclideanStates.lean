-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
-- name    : QMAPerfectCompleteness_Proof_EuclideanStates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:45:27.490278+00:00
-- url     : https://prove2.me/theorems/803df796-0a4e-4fc6-8ee0-2ca4c938af6e
-- title:
--   Euclidean normalization and pure-state density matrices
-- statement:
--   Defines normalization of a finite complex vector using its Euclidean norm, and the rank-one matrix formed from a vector and its conjugate transpose. These constructions turn a nonzero honest history vector into a normalized pure proof without using the supremum norm of a function space.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/EuclideanStates.lean, lines 34–47.

/- Generated from Solutions.EuclideanStates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic



open Matrix
open scoped ComplexOrder MatrixOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]











/-- Normalize using the Euclidean norm, rather than the sup norm of a function type. -/
noncomputable def normalize (v : ι → ℂ) : ι → ℂ := ((euclidNorm v : ℂ)⁻¹) • v





/-- The rank-one matrix |v⟩⟨v|. -/
def pureDensity (v : ι → ℂ) : Matrix ι ι ℂ := vecMulVec v (star v)















end QMAPerfectCompleteness.Main.VerifierAnalysis


