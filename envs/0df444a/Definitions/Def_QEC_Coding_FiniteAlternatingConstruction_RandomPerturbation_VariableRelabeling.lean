-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:39:47.274199+00:00
-- url     : https://prove2.me/theorems/483b4513-e8c5-4c2b-b8fb-348fa6626757
-- title:
--   Variable Relabeling
-- statement:
--   Definitions and structural lemmas for Variable Relabeling, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26DecodingGraph
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
variable {A : Type*} [Fintype A] [DecidableEq A]
def pulledSupport (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ)
    (u : A ≃ Vertex P) : Event P J r → Finset A := codedSupport u (eventSupport P J r)
def pulledBad (P : TannerSquarePresentation) (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ)
    (u : A ≃ Vertex P) : ∀ e, Set (pulledSupport P J r u e → Space) :=
  codedBad u (eventSupport P J r) (eventBad P J r lambda K)
def pulledOutput (P : TannerSquarePresentation) (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ)
    (u : A ≃ Vertex P) (T : HTable A Space) : A → Space :=
  output (pulledSupport P J r u) (pulledBad P J r lambda K u) T
def pulledVertexLaw (P : TannerSquarePresentation) (R c : ℝ) (u : A ≃ Vertex P) (a : A) :
    Measure Space := vertexLaw P R c (u a)
theorem pulledVertexLaw_probability (P : TannerSquarePresentation) (R c : ℝ) (hc : c<1)
    (u : A ≃ Vertex P) (a : A) : IsProbabilityMeasure (pulledVertexLaw P R c u a) :=
  vertexLaw_probability P R hc (u a)
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling


