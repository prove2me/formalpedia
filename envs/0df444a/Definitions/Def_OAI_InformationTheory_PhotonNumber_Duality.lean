-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
-- name    : OAI_InformationTheory_PhotonNumber_Duality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:43:53.445233+00:00
-- url     : https://prove2.me/theorems/eb578d09-217b-4a82-a94d-62a1f466dd3f
-- title:
--   Scalar comparison diagrams and mean functionals for ensemble mixtures
-- statement:
--   This file defines the scalar version of the diagonal comparison systems attached to a thermal spectral space, and linear functionals given by ensemble means.
--
--   Notation: a thermal spectral space $S$ consists of a Hilbert basis $(b_i)$ of a complex Hilbert space $E$, weights $p_i>0$ with $\sum_ip_i = 1$, and $r>0$; its parameter at $(i,j)$ is $(r,\omega_r(p_i,p_j))$ with $\omega_r(p,q) = (\log p-\log q)/(\log(r+1)-\log r)$, and parameters range over $(0,\infty)\times\mathbb{R}$. A diagonal comparison system consists of source and target parameters, a space of tests and a linear map from tests to target families.
--
--   1. **Scalar targets and diagrams.** A complex-linear functional $q$ on bounded operators is viewed as a linear map into $\mathbb{C}^{\{\ast\}}$. The scalar diagram of $S$ and $q$ is the comparison system whose tests are the coordinates of the centered test operators of $S$ (weighted by $h(r)L(p_i,p_j)$, $L$ the logarithmic mean), whose source parameters are the parameters of $S$, whose single target index carries an extra parameter "none", and whose map applies $q$ to the operator realising a test. A weight $w$ on parameters is extended by $w(\text{none}) = 1$.
--
--   2. **Mean functionals.** For a square-summable family $(v_i)$ the mean $Z\mapsto\sum_i\langle v_i,Zv_i\rangle$ is a complex-linear functional on bounded operators, and for two such families $v,w$ and $t\in\mathbb{R}$ the mixture functional is
--   $$
--   Z\ \mapsto\ \sqrt{t(1-t)}\,\Bigl(\sum_i\langle v_i,Zv_i\rangle - \sum_j\langle w_j,Zw_j\rangle\Bigr).
--   $$
--
--   The scalar diagram turns a single linear functional into a comparison problem of the same diagonal form as the operator-valued ones, so that bounds on functionals such as the mixture functional can be derived from comparison inequalities.
--
--   **Formalization Note** Parameters of the scalar diagram live in `Option Param`, with `none` for the target; `scalarWeight w` sends `none` to $1$. The mean is a `tsum`, and linearity uses its absolute convergence for square-summable families.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Duality.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Duality.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum

namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

namespace WeightedColumns
variable {ρ σ τ : State n}

end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def scalarTarget (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ) :
    (E →L[ℂ] E) →ₗ[ℂ] (Unit → ℂ) where
  toFun Z _ := q Z
  map_add' X Y := by ext; exact map_add q X Y
  map_smul' c X := by ext; exact q.map_smul c X

def scalarDiagram (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ) :
    DiagonalForms.System (Option Param) (S.I × S.I) Unit :=
  CenteredTests.system S.basis S.p S.pos S.sum.summable (h S.r) (h_pos S.rpos)
    (fun ij => some (S.pparam ij)) (some (⟨S.r,S.rpos⟩,0))
    (fun j => by simp [Space.pparam, Space.param, frequency])
    (fun _ => none) (scalarTarget q)

def scalarWeight (w : Param → ℝ) : Option Param → ℝ
  | none => 1
  | some p => w p

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def meanLM (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := mean v
  map_add' Z Y := by
    unfold mean
    simp only [add_apply, inner_add_right]
    exact (mean_hasSum v hv Z).summable.tsum_add (mean_hasSum v hv Y).summable
  map_smul' c Z := by
    simp only [mean, smul_apply, inner_smul_right, tsum_mul_left, smul_eq_mul, RingHom.id_apply]
def mixtureFunctional (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (t : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] ℂ :=
  (Real.sqrt (t*(1-t)) : ℂ) • (meanLM v hv-meanLM w hw)

end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

end

section
variable {I J : Type*} [Fintype I] [Fintype J]

end

open scoped ComplexConjugate

end ThermalDual

end

end OAI


