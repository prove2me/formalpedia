-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum
-- name    : OAI_InformationTheory_PhotonNumber_Minimum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:45:57.7323+00:00
-- url     : https://prove2.me/theorems/fa021c29-bca6-4aff-b99b-08b8802e2eda
-- title:
--   Thermal setups for the regularized two-beam-splitter minimization and fourth-moment drift constants
-- statement:
--   This file fixes the numerical setup of a regularized minimization problem built from two beam splitters and thermal reference states, together with auxiliary energies and constants.
--
--   Notation: $\mathcal F_n = \ell^2(\mathbb{N}^n)$, $|k| = \sum_jk_j$, $\nu(k) = 1+|k|$; $h(r) = \log(r+1)-\log r$; $w_r(v)$ is the thermal weight and $\underline w(r) = \inf_vw_r(v)$, with mixture constant $C(r) = (h(r)\underline w(r))^{-1/2}$; $\tau_r$ is the thermal state with diagonal entries $\prod_j(r+1)^{-1}(r/(r+1))^{k_j}$; $\mathrm{BS}_\eta(\rho,\sigma)$ is the beam-splitter output state.
--
--   1. **Two-port data and energies.** $\lambda(\eta,\theta) = (\theta\eta,\ \theta(1-\eta))$ and the output reference $\theta(\eta a_0+(1-\eta)a_1)+(1-\theta)d$. For a weighted-column representation $(x_i)$ of a state and a mode $j$, the lower energy is $\sum_i\|A_jx_i\|^2$ with $(A_jx)_k = \sqrt{k_j+1}\,\nu(k+e_j)^{-3}x_{k+e_j}$, and the centered lower energy subtracts $|\Omega_{r,j}(1)|^2$, where $\Omega_{r,j}(1) = (r+1)\sum_i\langle A_jx_i,W_3x_i\rangle - r\sum_i\langle W_3x_i,C_jx_i\rangle$ is the weak mean ($W_3$ diagonal with entries $\nu(k)^{-3}$, $C_j$ the matching raising operator). For spectral log data, the defect square is $\sum_j\|D_j\|^2$ (operator norms of the defect functionals at thermal parameter $r>0$) and the mean square is $\sum_j|\mu_j|^2$ (means of the annihilation matrices).
--
--   2. **Drift constants.** The drift polynomial is $(r+1)\,t\,(t^4-(t+1)^4) + r\,(t+n)\,((t+2)^4-(t+1)^4)$. One has $|k|\le\nu(k)$ and $0\le|k|/\nu(k)^4\le1$, so the diagonal operator with entries $|k|/\nu(k)^4$ is bounded by $1$. The fourth drift constant is $4+|4rn+12r-6|+|18rn+24r-4|+|28rn+14r-1|+|15rn|$. For a regularization with parameter $\delta\in[0,1]$, also $1-\delta\in[0,1]$.
--
--   3. **Thermal setups.** A thermal setup consists of $\eta,\theta,\kappa\in(0,1)$ and $\varepsilon,d,r_1,r_2>0$ such that, with $r_0 = \theta(\eta r_1+(1-\eta)r_2)+(1-\theta)d$,
--   $$
--   (1+\varepsilon)\bigl(\theta\eta r_1+\theta(1-\eta)r_2\bigr)\le r_0,\qquad (1+\varepsilon)\bigl(\theta\eta(r_1+1)+\theta(1-\eta)(r_2+1)\bigr)\le r_0+1,\qquad \kappa\le\frac{\varepsilon^2}{4(\varepsilon+2)\,C(r_0)^2}.
--   $$
--   Then $r_0>0$, $w_1 = (1-\kappa)\theta\eta>0$ and $w_2 = (1-\kappa)\theta(1-\eta)>0$. For $\zeta>0$ the associated regularization has first transmissivity $\eta$, attenuation parameter $\delta = 1-\theta$, mixing parameter $\kappa$, reference states $\tau_d$ and $\tau_{r_0}$ (both of finite energy), and constants
--   $$
--   c = \frac1{h(r_0)},\quad a_1 = \frac{(1+\varepsilon)w_1}{h(r_1)},\quad a_2 = \frac{(1+\varepsilon)w_2}{h(r_2)},\quad b_1 = \varepsilon w_1,\quad b_2 = \varepsilon w_2,\quad \zeta .
--   $$
--   The middle state is $\mathrm{BS}_\eta(\rho,\sigma)$ and the raw state is $\mathrm{BS}_\theta(\mathrm{BS}_\eta(\rho,\sigma),\tau_d)$.
--
--   The thermal setup encodes the slack needed to compare the regularized objective with thermal states of mean photon numbers $r_1$, $r_2$ (inputs) and $r_0$ (output); the slack inequalities and the smallness of $\kappa$ are the quantitative assumptions of that comparison.
--
--   **Formalization Note** `ThermalSetup` is a structure with the listed fields and proofs; `reg n ζ hζ` builds the `Regularization n`. `defectSquared` uses the operator norm of the continuous linear functional `G.defect r hr j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

def twoPortLambda (η θ : ℝ) : Fin 2 → ℝ := ![θ*η,θ*(1-η)]

def outputReference (η θ : ℝ) (a : Fin 2 → ℝ) (d : ℝ) : ℝ :=
  θ*(η*a 0+(1-η)*a 1)+(1-θ)*d

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

def lowerEnergy (X : WeightedColumns ρ) (j : Fin n) : ℝ :=
  ∑' i, ‖sandwich 0 3 (by omega) j (X.vector i)‖^2

end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

end

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

def centeredLowerEnergy (X : WeightedColumns ρ) (r : ℝ) (j : Fin n) : ℝ :=
  X.lowerEnergy j-‖X.weakMean r j‖^2

end

open QuantumTrace
variable {n : ℕ}

end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
def driftPolynomial (n : ℕ) (r t : ℝ) : ℝ :=
  (r+1)*t*(t^4-(t+1)^4)+r*(t+n)*((t+2)^4-(t+1)^4)

end

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

theorem number_le_weight (k : NumberIndex n) : (totalNumber k:ℝ)≤numberWeight k := by
  simp only [numberWeight,totalNumber,Nat.cast_sum]; linarith

theorem number_div_weight_bound (k : NumberIndex n) : |(totalNumber k:ℝ)/numberWeight k^4|≤1 := by
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  exact (number_le_weight k).trans (le_self_pow₀ (numberWeight_one_le k) (by norm_num))

def numberSandwich (n : ℕ) : Fock n →L[ℂ] Fock n :=
  diagonal (fun k => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

def fourthDriftConstant (n : ℕ) (r : ℝ) : ℝ :=
  |(-4:ℝ)|+|4*r*n+12*r-6|+|18*r*n+24*r-4|+|28*r*n+14*r-1|+|15*r*n|

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem attenuation_mem : 1-R.δ ∈ Set.Icc 0 1 :=
  ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

structure ThermalSetup where
  η : ℝ
  θ : ℝ
  κ : ℝ
  ε : ℝ
  d : ℝ
  r1 : ℝ
  r2 : ℝ
  hη : η ∈ Set.Ioo 0 1
  hθ : θ ∈ Set.Ioo 0 1
  hκ : κ ∈ Set.Ioo 0 1
  hε : 0<ε
  hd : 0<d
  hr1 : 0<r1
  hr2 : 0<r2
  slack_r : (1+ε)*(θ*η*r1+θ*(1-η)*r2)≤θ*(η*r1+(1-η)*r2)+(1-θ)*d
  slack_s : (1+ε)*(θ*η*(r1+1)+θ*(1-η)*(r2+1))≤θ*(η*r1+(1-η)*r2)+(1-θ)*d+1
  small_κ : κ≤ε^2/(4*(ε+2)*mixtureConstant (θ*(η*r1+(1-η)*r2)+(1-θ)*d)^2)

namespace ThermalSetup
variable (P : ThermalSetup)
def r0 : ℝ := P.θ*(P.η*P.r1+(1-P.η)*P.r2)+(1-P.θ)*P.d
def w1 : ℝ := (1-P.κ)*P.θ*P.η
def w2 : ℝ := (1-P.κ)*P.θ*(1-P.η)
theorem r0_pos : 0<P.r0 := by
  unfold r0
  exact add_pos (mul_pos P.hθ.1 (add_pos (mul_pos P.hη.1 P.hr1)
    (mul_pos (sub_pos.mpr P.hη.2) P.hr2))) (mul_pos (sub_pos.mpr P.hθ.2) P.hd)
theorem w1_pos : 0<P.w1 := mul_pos (mul_pos (sub_pos.mpr P.hκ.2) P.hθ.1) P.hη.1
theorem w2_pos : 0<P.w2 := mul_pos (mul_pos (sub_pos.mpr P.hκ.2) P.hθ.1) (sub_pos.mpr P.hη.2)
theorem η_mem : P.η ∈ Set.Icc 0 1 := ⟨P.hη.1.le,P.hη.2.le⟩
theorem θ_mem : P.θ ∈ Set.Icc 0 1 := ⟨P.hθ.1.le,P.hθ.2.le⟩
theorem κ_mem : P.κ ∈ Set.Icc 0 1 := ⟨P.hκ.1.le,P.hκ.2.le⟩
theorem δ_mem : 1-P.θ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr P.hθ.2.le,sub_le_self _ P.hθ.1.le⟩

def reg (n : ℕ) (ζ : ℝ) (hζ : 0<ζ) : Regularization n where
  η := P.η
  δ := 1-P.θ
  κ := P.κ
  hη := P.η_mem
  hδ := P.δ_mem
  hκ := P.κ_mem
  τD := thermalState n P.d P.hd
  τ0 := thermalState n P.r0 P.r0_pos
  finiteD := thermalState_finiteEnergy n P.d P.hd
  finite0 := thermalState_finiteEnergy n P.r0 P.r0_pos
  c := 1/h P.r0
  a1 := (1+P.ε)*P.w1/h P.r1
  a2 := (1+P.ε)*P.w2/h P.r2
  b1 := P.ε*P.w1
  b2 := P.ε*P.w2
  ζ := ζ
  hc := one_div_pos.mpr (h_pos P.r0_pos)
  ha1 := div_pos (mul_pos (by linarith [P.hε]) P.w1_pos) (h_pos P.hr1)
  ha2 := div_pos (mul_pos (by linarith [P.hε]) P.w2_pos) (h_pos P.hr2)
  hb1 := mul_pos P.hε P.w1_pos
  hb2 := mul_pos P.hε P.w2_pos
  hζ := hζ

def middle {n : ℕ} (ρ σ : State n) : State n := beamOutput P.η P.η_mem ρ σ
def raw {n : ℕ} (ρ σ : State n) : State n :=
  beamOutput P.θ P.θ_mem (P.middle ρ σ) (thermalState n P.d P.hd)
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
def defectSquared (r : ℝ) (hr : 0<r) : ℝ := ∑ j, ‖G.defect r hr j‖^2
def meanSquared : ℝ := ∑ j, ‖G.annihilationMean j‖^2
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup

namespace ThermalDual

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup
end EntropyPhotonNumber

end

end OAI


