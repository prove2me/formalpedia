-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T01:56:07.519022+00:00
-- url     : https://prove2.me/theorems/b054480c-87b3-48b8-801e-71a01476c605
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
abbrev StageMaps {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Vertex (state (perturbationOddScale p) n).presentation → Space
abbrev StageTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)
def Experiment {L : ℝ} (p : GeometricParameters L) : ℕ → Type
  | 0 => Unit
  | n+1 => Experiment p n × StageTables p n
instance experimentMeasurableSpace {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → MeasurableSpace (Experiment p n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => (experimentMeasurableSpace p n).prod inferInstance
def experimentPrefix {L : ℝ} (p : GeometricParameters L) (m : ℕ) :
    (n : ℕ) → m ≤ n → Experiment p n → Experiment p m
  | 0, h, z => by
      have hm : m = 0 := by omega
      subst m
      exact z
  | n+1, h, z =>
      if he : m = n+1 then he.symm ▸ z
      else experimentPrefix p m n (by omega) z.1
def tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageTables p i.val :=
  fun z => (experimentPrefix p (i.val+1) n i.isLt z).2
def evaluate {L : ℝ} (p : GeometricParameters L) : (n : ℕ) → Experiment p n → StageMaps p n
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | n+1, z => physicalSuccessorOutput p n (evaluate p n z.1) z.2
def history {L : ℝ} (p : GeometricParameters L) (n : ℕ) (z : Experiment p n)
    (i : Fin (n+1)) : StageMaps p i.val :=
  evaluate p i.val (experimentPrefix p i.val n (by omega) z)
def stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val :=
  fun z => evaluate p i.val (experimentPrefix p i.val n (by omega) z)
def stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val × StageTables p i.val :=
  fun z => (stageInput p n i z, tableAt p n i z)
end QEC.Coding.BDL26FiniteEmbeddingExperiment


