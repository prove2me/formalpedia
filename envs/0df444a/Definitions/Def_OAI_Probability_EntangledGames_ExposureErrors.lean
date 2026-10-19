-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
-- name    : OAI_Probability_EntangledGames_ExposureErrors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:27:35.069252+00:00
-- url     : https://prove2.me/theorems/5d94c699-7086-4745-bb57-9c62116d881d
-- title:
--   Normalized one-sided hybrid states of an event system
-- statement:
--   This file normalizes the one-sided hybrid states of an event system, producing unit states that depend on the question of only one player.
--
--   **Setting.** An event system $S$ over finite question sets $X,Y$, a finite set of coordinates $I$ and a finite label set $R$ provides a probability law $\mu$ on $X\times Y$, default questions $x_0\in X$, $y_0\in Y$, a list $l=(l_0,\dots,l_{L-1})$ of distinct coordinates, a coefficient matrix $C\in\mathbb{C}^{m\times n}$ of Hilbert–Schmidt norm $1$, weights $\theta_r(z)\in[0,1]$ indexed by labels $r$ and question profiles $z=(z_i)_{i\in I}\in(X\times Y)^I$, an event probability $p>0$, and for $j\in\{0,\dots,L\}$ square-root factors $U_j(r,z)$ and $V_j(r,z)$ of Alice's effect with her questions on $l_j,\dots,l_{L-1}$ resampled and of Bob's effect with his questions on $l_0,\dots,l_{j-1}$ resampled. Write $\mu^{\otimes I}(z)=\prod_i\mu(z_i)$ and $z^{i\leftarrow q}$ for $z$ with entry $i$ replaced by $q$. For $j\in\{0,\dots,L-1\}$ the one-sided states are the block-diagonal matrices, with one block for each label $(r,z)\in R\times(X\times Y)^I$,
--   $$\mathrm{raw}^A_j(x)=\bigoplus_{(r,z)}\sqrt{\frac{\mu^{\otimes I}(z)\,\theta_r(z)}{p}}\;U_{j+1}(r,z_x)\,C\,V_{j+1}(r,z_x)^{\mathsf T},\qquad z_x=z^{l_j\leftarrow(x,y_0)},$$
--   and $\mathrm{raw}^B_j(y)$, defined in the same way with $U_j,V_j$ and $z^{l_j\leftarrow(x_0,y)}$. The two-sided hybrid state $D_j(q)$ is defined in the same way with $U_{j+1},V_j$ and $z^{l_j\leftarrow q}$.
--
--   For a matrix $G$ let $\|G\|_2^2=\sum_{a,b}|G_{ab}|^2$, and let $\operatorname{unitize}(G,E)=G/\|G\|_2$ if $G\neq0$ and $\operatorname{unitize}(0,E)=E$. For a fallback matrix $E$ of the same shape as these states, and $j\in\{0,\dots,L-1\}$:
--
--   1. **Alice's normalized state.** $M_j(E,x)=\operatorname{unitize}\big(\mathrm{raw}^A_j(x),E\big)$ for $x\in X$.
--   2. **Bob's normalized state.** $N_j(E,y)=\operatorname{unitize}\big(\mathrm{raw}^B_j(y),E\big)$ for $y\in Y$.
--
--   These are unit states as soon as $\|E\|_2=1$, and $M_j(E,x)$ depends only on Alice's question while $N_j(E,y)$ depends only on Bob's. In the main argument they replace the two-sided states $D_j(q)$: for $\|E\|_2=1$ one proves
--   $$\sum_{j=0}^{L-1}\mathbb{E}_{(x,y)\sim\mu}\big\|D_j(x,y)-M_j(E,x)\big\|_2^2\le4\log\frac{|R|}{p},$$
--   and the same bound with $N_j(E,y)$ in place of $M_j(E,x)$, so that for a typical step $j$ both players' local states are close to a common state.
--
--   **Formalization Note** The definitions are `EventSystem.M` and `EventSystem.N`, built from `unitize`, `rawA` and `rawB`. `unitize` tests whether $\|G\|_2^2=0$, which happens exactly when $G=0$. The setting assumes $X$, $Y$ and $R$ nonempty, as required by the square-root factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureErrors.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureErrors.lean by skeleton subtraction
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

namespace OAI

universe u_I u_Z u_X u_Y u_R u_m u_n

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {I : Type u_I} {Z : Type u_Z} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
namespace EventSystem
variable (S : EventSystem X Y I R m n)

def M (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ) (x : X) :=
  unitize (S.rawA j x) E
def N (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ) (y : Y) :=
  unitize (S.rawB j y) E
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI


