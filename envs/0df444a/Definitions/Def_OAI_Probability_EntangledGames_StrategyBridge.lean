-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_StrategyBridge
-- name    : OAI_Probability_EntangledGames_StrategyBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:39:16.852797+00:00
-- url     : https://prove2.me/theorems/880d3b6f-26fe-42bd-bd3f-7134d5159544
-- title:
--   Coefficient matrix of an entangled strategy and the repeated-game model it induces
-- statement:
--   An entangled strategy $S$ for question sets $\mathcal X,\mathcal Y$ and finite answer sets $\mathcal A,\mathcal B$ consists of local dimensions $d_A,d_B\ge1$, a unit vector $\psi\in\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ with coordinates $\psi(i,j)$ and $\sum_{i,j}|\psi(i,j)|^2=1$, and positive operator-valued measures (POVMs): for each $x\in\mathcal X$ positive semidefinite $d_A\times d_A$ matrices $P^x_a$ ($a\in\mathcal A$) with $\sum_aP^x_a=I$, and for each $y\in\mathcal Y$ positive semidefinite $d_B\times d_B$ matrices $Q^y_b$ ($b\in\mathcal B$) with $\sum_bQ^y_b=I$. A game $G=(\pi,V_G)$ consists of a probability distribution $\pi$ on $\mathcal X\times\mathcal Y$ and an acceptance predicate $V_G$ on $\mathcal X\times\mathcal Y\times\mathcal A\times\mathcal B$. A $k$-fold repeated strategy is an entangled strategy whose question sets are $\mathcal X^k,\mathcal Y^k$ and whose answer sets are $\mathcal A^k,\mathcal B^k$.
--
--   A repeated model with coordinate set $I$ consists of a probability law $\mu$ on $\mathcal X\times\mathcal Y$, a matrix $C\in\mathbb C^{m\times n}$ with $\|C\|_{\mathrm{HS}}^2=\sum_{i,j}|C_{ij}|^2=1$, for each $\vec x\in\mathcal X^I$ a POVM $\{P_{\vec x}(\vec a)\}_{\vec a\in\mathcal A^I}$ on $\mathbb C^m$, for each $\vec y\in\mathcal Y^I$ a POVM $\{Q_{\vec y}(\vec b)\}_{\vec b\in\mathcal B^I}$ on $\mathbb C^n$, and a predicate $V$ on $\mathcal X\times\mathcal Y\times\mathcal A\times\mathcal B$. In it the question pairs $(x_i,y_i)_{i\in I}$ are drawn independently from $\mu$, the answers $(\vec a,\vec b)$ occur with probability $\operatorname{Re}\langle\mathrm{vec}\,C,(P_{\vec x}(\vec a)\otimes Q_{\vec y}(\vec b))\,\mathrm{vec}\,C\rangle$, where $\mathrm{vec}\,C$ is the vector with entries $C_{ij}$, and coordinate $i$ is won when $V(x_i,y_i,a_i,b_i)$ holds. The file defines:
--
--   1. **Coefficient matrix of a strategy.** $C_S\in\mathbb C^{d_A\times d_B}$ with $(C_S)_{ij}=\psi(i,j)$, so that $\psi=\mathrm{vec}\,C_S$. It has unit Hilbert–Schmidt norm:
--   $$
--   \|C_S\|_{\mathrm{HS}}^2=\sum_{i,j}|\psi(i,j)|^2=1 .
--   $$
--
--   2. **Repeated model of a repeated strategy.** For a $k$-fold repeated strategy $S$ and a game $G=(\pi,V_G)$, $\mathcal M(S,G)$ is the repeated model with coordinate set $I=\{0,\dots,k-1\}$, $m=d_A$, $n=d_B$ and
--   $$
--   \mu=\pi,\qquad C=C_S,\qquad P_{\vec x}(\vec a)=P^{\vec x}_{\vec a},\qquad Q_{\vec y}(\vec b)=Q^{\vec y}_{\vec b},\qquad V=V_G,
--   $$
--   where $P^{\vec x}_{\vec a}$ and $Q^{\vec y}_{\vec b}$ are the measurement operators of $S$ for the question tuples $\vec x,\vec y$ and the answer tuples $\vec a,\vec b$.
--
--   Because $\psi=\mathrm{vec}\,C_S$, the Born probabilities $\operatorname{Re}\langle\psi,(P^{\vec x}_{\vec a}\otimes Q^{\vec y}_{\vec b})\psi\rangle$ of $S$ are exactly the answer probabilities of $\mathcal M(S,G)$. This bridge transfers the analysis of abstract repeated models to the concrete strategies of the threshold parallel repetition theorem: for $k\ge1$ the probability that $S$ wins at least $\lceil (v+\delta)k\rceil$ of the $k$ coordinates equals the probability, under the joint law of $\mathcal M(S,G)$, that the fraction of won coordinates is at least $v+\delta$, where $v$ is the entangled value of $G$.
--
--   **Formalization Note** The declarations are `Strategy.coeff`, `Strategy.coeff_unit` (the identity $\|C_S\|_{\mathrm{HS}}^2=1$, which supplies the normalisation field of the model) and `Strategy.repetitionModel`. Local dimensions are stored as `dimA`, `dimB` with spaces indexed by `Fin (dimA+1)`, `Fin (dimB+1)`; the question and answer sets of a game are `Fin (x+1)`, `Fin (y+1)`, `Fin (a+1)`, `Fin (b+1)`; the law $\mu$ is `G.questionLaw` (the game's distribution packaged as a `Law`); and the POVMs of the model are built from `S.alice`, `S.bob` together with their positivity and completeness proofs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/StrategyBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/StrategyBridge.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments
import Definitions.Def_OAI_Probability_EntangledGames_TestExtraction

namespace OAI

universe u_I u_X u_Y

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law
namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]
def coeff (S : Strategy X Y A B) : Matrix (Fin (S.dimA+1)) (Fin (S.dimB+1)) ℂ := fun i j => S.state (i,j)
lemma coeff_unit (S : Strategy X Y A B) : hsSq S.coeff = 1 := by
  simpa only [hsSq, coeff, Fintype.sum_prod_type] using S.state_unit
def repetitionModel {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b) :
    RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) (Fin k)
      (Fin (S.dimA+1)) (Fin (S.dimB+1)) where
  μ := G.questionLaw
  C := S.coeff
  hC := S.coeff_unit
  P xs := ⟨S.alice xs, S.alice_pos xs, S.alice_total xs⟩
  Q ys := ⟨S.bob ys, S.bob_pos ys, S.bob_total ys⟩
  V := G.accepts
end Strategy

namespace Strategy
variable {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b)
end Strategy
end ThresholdParallelRepetition

end

end OAI


