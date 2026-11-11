-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:14:21.140486+00:00
-- url     : https://prove2.me/theorems/45c486eb-b76e-4241-b273-ac9cb7f69172
-- title:
--   Seed Embedding
-- statement:
--   Definitions and structural lemmas for Seed Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def seedPoint (S : OddScale) : Vertex (state S 0).presentation → Space := fun _ => 0
end QEC.Coding.BDL26RandomSeedEmbedding


