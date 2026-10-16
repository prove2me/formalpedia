-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
-- name    : OAI_InformationTheory_PhotonNumber_PhysicalMinimum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:32:43.279191+00:00
-- url     : https://prove2.me/theorems/5308d070-82fd-4a62-a2a8-e371cb9c6c51
-- title:
--   Canonical weighted-column representation of a state with finite sixth number moment
-- statement:
--   This file defines the canonical weighted-column representation of a bosonic state.
--
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space, $\nu(k) = 1+\sum_jk_j$, and $W_3$ the diagonal operator multiplying the $k$-th coordinate by $\nu(k)^{-3}$. Let $\rho$ be a state (positive bounded, $\sum_k\operatorname{Re}\langle k|\rho|k\rangle = 1$) with finite sixth number moment, $\sum_k(1+|k|)^6\langle k|\rho|k\rangle<\infty$, and let $r_a = \sqrt\rho\,|a\rangle$ be its root columns. The canonical representation is indexed by $a\in\mathbb{N}^n$, with vectors
--   $$
--   x_a = \bigl(\nu(k)^3\,r_a(k)\bigr)_{k\in\mathbb{N}^n}\in\mathcal F_n .
--   $$
--   These are square-summable in $a$, satisfy $W_3x_a = r_a$, hence $\sum_a\|W_3x_a\|^2 = 1$ and $\sum_a|W_3x_a\rangle\langle W_3x_a| = \rho$; that is, they form a weighted-column representation of $\rho$.
--
--   It provides a weighted-column representation for every state with finite sixth moment (not only for Gibbs-form states), so that the generator and slice constructions defined for such representations apply to arbitrary sufficiently regular states.
--
--   **Formalization Note** This is `WeightedColumns.canonical ρ hm` with `hm : FiniteMoment 6 ρ`, built from `weightedRoot 3 ρ hm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace TensorLp
open scoped ENNReal
variable {A B : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {J : Type*}

end BeamLadder

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ}
namespace GibbsData
variable {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData

def WeightedColumns.canonical (ρ : State n) (hm : FiniteMoment 6 ρ) : WeightedColumns ρ where
  Index := NumberIndex n
  vector := weightedRoot 3 ρ hm
  summable := weightedRoot_summable 3 ρ hm
  normalized := by simpa only [inverse_weightedRoot] using rootColumn_norm ρ
  density := by simpa only [inverse_weightedRoot] using rootColumn_operator ρ

namespace WeightedColumns

end WeightedColumns

end

section
open QuantumTrace TensorLp

end

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end

namespace Regularization
open QuantumTrace
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)
end GibbsData
end

namespace Regularization

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} (R : Regularization n)

end

open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

end

end OAI


