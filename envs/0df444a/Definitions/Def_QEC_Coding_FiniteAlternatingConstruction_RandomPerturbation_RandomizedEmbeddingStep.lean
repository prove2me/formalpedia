-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:09:36.737776+00:00
-- url     : https://prove2.me/theorems/15a5769e-9a6d-4b78-879f-18c214b1388d
-- title:
--   Randomized Embedding Step
-- statement:
--   Definitions and structural lemmas for Randomized Embedding Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
noncomputable def perturbationOddScale {L : ℝ} (p : GeometricParameters L) : OddScale :=
  BDL26QuantitativeBounds.leastOddScaleAbove ((2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ)) (by have h := p.rounding; linarith)
noncomputable def perturbationEmbeddingOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) : Vertex P → Space :=
  perturbedMap P J p.lambda (geometricOutput P J p T)
end QEC.Coding.BDL26RandomPerturbation


