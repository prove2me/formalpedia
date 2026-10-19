-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_FreshStates
-- name    : OAI_Probability_EntangledGames_FreshStates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:18:48.97599+00:00
-- url     : https://prove2.me/theorems/a2b58992-0e39-44a3-ac7f-5d8a846eb4bd
-- title:
--   Conditioned states with one coordinate fixed, event densities and basis states
-- statement:
--   This file defines the subnormalized states that describe a repeated strategy conditioned on an event once the questions at one coordinate are set to a prescribed pair, together with the density of the conditioned question distribution and the product basis states.
--
--   **Setting.** Let $X,Y$ be finite question sets, $I$ a finite set of coordinates, $R$ a finite label set and $\mu$ a probability law on $X\times Y$. A question profile is $z=(z_i)_{i\in I}\in\mathcal Z=(X\times Y)^I$, $\mu^{\otimes I}(z)=\prod_{i\in I}\mu(z_i)$ is the product law, and $z^{i\leftarrow q}$ is $z$ with its $i$-th entry replaced by $q\in X\times Y$. A coefficient matrix $C\in\mathbb{C}^{m\times n}$ stands for the bipartite vector $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$, and for $M\in\mathbb{C}^{m\times m}$, $N\in\mathbb{C}^{n\times n}$ we write $\mathrm{Pr}_C(M,N)=\operatorname{Re}\langle\psi_C,(M\otimes N)\psi_C\rangle$. Let $\theta_r$ ($r\in R$) be real functions of profiles and $p\in\mathbb{R}$.
--
--   1. **State at a coordinate.** Given a coordinate $i$, matrix families $U_r(z)\in\mathbb{C}^{u\times m}$ and $V_r(z)\in\mathbb{C}^{v\times n}$ ($u,v$ finite index sets) and $q\in X\times Y$, the state $\Psi_i(q)$ is the block-diagonal matrix indexed by $(u\times(R\times\mathcal Z))\times(v\times(R\times\mathcal Z))$ with one block for each label $(r,z)\in R\times\mathcal Z$:
--   $$\Psi_i(q)=\bigoplus_{(r,z)\in R\times\mathcal Z}\sqrt{\frac{\mu^{\otimes I}(z)\,\theta_r(z)}{p}}\;U_r\big(z^{i\leftarrow q}\big)\,C\,V_r\big(z^{i\leftarrow q}\big)^{\mathsf T}.$$
--   Since $UCV^{\mathsf T}$ is the coefficient matrix of $(U\otimes V)\psi_C$, this is the vector $\sum_{(r,z)}\sqrt{\mu^{\otimes I}(z)\theta_r(z)/p}\;\big((U_r\otimes V_r)(z^{i\leftarrow q})\,\psi_C\big)\otimes e_{(r,z)}\otimes e_{(r,z)}$, in which both parties hold a copy of the classical label $(r,z)$.
--   2. **Event density.** For matrix families $F_r(z)\in\mathbb{C}^{m\times m}$ and $H_r(z)\in\mathbb{C}^{n\times n}$,
--   $$\rho(z)=\frac1p\sum_{r\in R}\theta_r(z)\,\mathrm{Pr}_C\big(F_r(z),H_r(z)\big).$$
--   3. **Basis states.** For $i\in m$ and $j\in n$, $E_{ij}\in\mathbb{C}^{m\times n}$ is the matrix unit (entry $1$ at $(i,j)$ and $0$ elsewhere), the coefficient matrix of the product basis state $e_i\otimes e_j$.
--
--   If $\theta_r(z)\,\mathrm{Pr}_C(F_r(z),H_r(z))$ is the probability that a repeated strategy, on questions $z$, produces the outcome $r$ of a tested event, and $p=\sum_r\mathbb{E}_{z\sim\mu^{\otimes I}}[\theta_r(z)\,\mathrm{Pr}_C(F_r(z),H_r(z))]$ is the total probability of the event, then $\rho$ is the density of the conditioned question distribution with respect to $\mu^{\otimes I}$, and its $\mu^{\otimes I}$-average is $1$. The states $\Psi_i(q)$, with $U_r,V_r$ square-root factors of the players' effects, are the conditioned post-measurement states with the questions at a fresh coordinate $i$ overwritten by $q$; they are the raw material from which single-round strategies are extracted.
--
--   **Formalization Note** The definitions are `MixedExposure.stateAt` (built with `weightedBlock`), `MixedExposure.eventDensity` and `QuantumSampling.basisState`. The block weight passes through `Real.sqrt`, which is $0$ on negative arguments, and division by $p=0$ gives $0$ in Lean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/FreshStates.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/FreshStates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates

namespace OAI

universe u_X u_Y u_I u_E u_R u_m u_n u_u u_v u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [DecidableEq I]
end ThresholdParallelRepetition.FiniteProbability.Law
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [DecidableEq X] [DecidableEq Y]
variable {m : Type u_m} {n : Type u_n} {u : Type u_u} {v : Type u_v} [Fintype m] [Fintype n] [Fintype u] [Fintype v]
def stateAt (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    Matrix (u×(R×Profile I X Y)) (v×(R×Profile I X Y)) ℂ :=
  weightedBlock (fun t : R×Profile I X Y => (pi (fun _ : I => μ)).weight t.2 * θ t.1 t.2 / p)
    (fun t => U t.1 (Function.update t.2 i q)*C*(V t.1 (Function.update t.2 i q))ᵀ)

variable [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def eventDensity (θ : R → Profile I X Y → ℝ) (p : ℝ) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (z : Profile I X Y) : ℝ := (1/p)*∑ r, θ r z*prob C (F r z) (H r z)

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
-- [generator] trimmed: open FiniteProbability Law ScalarEntropy
open FiniteProbability Law
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def basisState (i : m) (j : n) : Matrix m n ℂ := fun a b => if a=i ∧ b=j then 1 else 0
variable {X : Type u_X} {Y : Type u_Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
end ThresholdParallelRepetition.QuantumSampling

end

end OAI


