-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalLimit
-- name    : OAI_InformationTheory_PhotonNumber_ThermalLimit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:48:09.02701+00:00
-- url     : https://prove2.me/theorems/8c69b711-4ca3-4d4d-a477-e213261998a4
-- title:
--   Thermal relative entropy, balance recurrences and the entropy part of the regularized objective
-- statement:
--   This file names the pieces into which the regularized objective of a thermal setup is split: an entropy part comparing entropies with thermal values, a penalty built from a thermal relative-entropy expression, and a constant offset, together with a detailed-balance recurrence for matrices indexed by photon numbers.
--
--   Notation: $g(t) = (t+1)\log(t+1)-t\log t$ (thermal entropy per mode), $h(r) = \log(r+1)-\log r$, $S(\rho)$ is the von Neumann entropy and $E(\rho) = \sum_k|k|\langle k|\rho|k\rangle$ the energy of an $n$-mode state. A thermal setup provides $\eta,\theta,\kappa\in(0,1)$, $\varepsilon,d,r_1,r_2>0$, $r_0 = \theta(\eta r_1+(1-\eta)r_2)+(1-\theta)d$, $w_1 = (1-\kappa)\theta\eta$, $w_2 = (1-\kappa)\theta(1-\eta)$, and its regularized output $\mathrm{Out}(\rho,\sigma) = (1-\kappa)\,\mathrm{BS}_\theta(\mathrm{BS}_\eta(\rho,\sigma),\tau_d)+\kappa\,\tau_{r_0}$.
--
--   1. **Balance recurrence.** For $p\in\mathbb{N}^J$ ($J$ finite) let $p-e_j$ lower the $j$-th coordinate by one (truncated at $0$). A matrix $M$ indexed by $\mathbb{N}^J\times\mathbb{N}^J$ satisfies the balance condition at $r$ if for all $j$, $p$, $b$ with $p_j>0$
--   $$
--   (r+1)\sqrt{p_j}\;M(p,b) = r\sqrt{b_j}\;M(p-e_j,\,b-e_j).
--   $$
--
--   2. **Thermal relative entropy.** $D_r(\rho) = n\log(r+1)+h(r)\,E(\rho)-S(\rho)$.
--
--   3. **Split of the objective.** For states $\rho,\sigma$:
--   $$
--   \text{entropy part} = \frac{S(\mathrm{Out}(\rho,\sigma))-n\,g(r_0)}{h(r_0)} - w_1\frac{S(\rho)-n\,g(r_1)}{h(r_1)} - w_2\frac{S(\sigma)-n\,g(r_2)}{h(r_2)},
--   $$
--   the penalty is $\varepsilon\bigl(\tfrac{w_1}{h(r_1)}D_{r_1}(\rho)+\tfrac{w_2}{h(r_2)}D_{r_2}(\sigma)\bigr)$, and the offset is
--   $$
--   -\frac{n\,g(r_0)}{h(r_0)}+\frac{w_1n\,g(r_1)}{h(r_1)}+\frac{w_2n\,g(r_2)}{h(r_2)}+\varepsilon\Bigl(\frac{w_1}{h(r_1)}\,n\log(r_1+1)+\frac{w_2}{h(r_2)}\,n\log(r_2+1)\Bigr).
--   $$
--
--   Normalising each entropy by its thermal value $n\,g(r)$ and by $h(r)$ is designed to compare the regularized objective with the thermal entropies $g(r)$ that appear in the entropy photon-number inequality $\eta\,g^{-1}(S(\rho_A)/n)+(1-\eta)\,g^{-1}(S(\rho_B)/n)\le g^{-1}(S(\rho_C)/n)$.
--
--   **Formalization Note** `Balance r M` is a `Prop` on functions $M:(J\to\mathbb{N})\to(J\to\mathbb{N})\to\mathbb{C}$; `lower p j` uses truncated natural subtraction (also applied to $b$). The output uses the regularization `P.reg n 1 _` (moment-penalty constant $\zeta = 1$, which does not affect the output state). `entropy` and `energy` are real `tsum`s ($0$ for divergent series).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalLimit.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalLimit.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric
open EntropyPhotonNumber
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace ThermalRecurrence

section
variable {J : Type*} [Fintype J] [DecidableEq J]

def lower (p : J → ℕ) (j : J) : J → ℕ := Function.update p j (p j-1)

omit [Fintype J] in
@[simp] theorem lower_same (p : J → ℕ) (j : J) : lower p j j = p j-1 := by simp [lower]

def Balance (r : ℝ) (M : (J → ℕ) → (J → ℕ) → ℂ) : Prop :=
  ∀ j p b, 0 < p j →
    ((r+1)*Real.sqrt (p j : ℝ)) • M p b =
      (r*Real.sqrt (b j : ℝ)) • M (lower p j) (lower b j)

end

end ThermalRecurrence

namespace EntropyPhotonNumber
open Filter Topology Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
end ThermalSetup
end

section
open QuantumTrace Annihilation Filter ThermalMetric

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
end ThermalSetup
end

open QuantumTrace ThermalMetric Filter

def thermalRelative {n : ℕ} (r : ℝ) (ρ : State n) : ℝ :=
  n*Real.log (r+1)+h r*energy ρ-entropy ρ

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
def out (ρ σ : State n) : State n := (P.reg n 1 zero_lt_one).output ρ σ

def entropyPart (ρ σ : State n) : ℝ :=
  (entropy (P.out ρ σ)-n*g P.r0)/h P.r0-
    P.w1*(entropy ρ-n*g P.r1)/h P.r1-P.w2*(entropy σ-n*g P.r2)/h P.r2

def penalty (ρ σ : State n) : ℝ :=
  P.ε*(P.w1/h P.r1*thermalRelative P.r1 ρ+P.w2/h P.r2*thermalRelative P.r2 σ)

def offset (n : ℕ) : ℝ :=
  -n*g P.r0/h P.r0+P.w1*n*g P.r1/h P.r1+P.w2*n*g P.r2/h P.r2+
    P.ε*(P.w1/h P.r1*(n*Real.log (P.r1+1))+P.w2/h P.r2*(n*Real.log (P.r2+1)))

end ThermalSetup
end EntropyPhotonNumber

end

end OAI


