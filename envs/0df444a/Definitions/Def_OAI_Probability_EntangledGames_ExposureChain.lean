-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
-- name    : OAI_Probability_EntangledGames_ExposureChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:14:42.224418+00:00
-- url     : https://prove2.me/theorems/dcf5af74-a5cb-4889-b9ea-d260d1a76f9d
-- title:
--   Hybrid chains of resampled effects along a list of coordinates
-- statement:
--   This file defines the hybrid families obtained by resampling Alice's or Bob's questions along a list of coordinates of a repeated two-player game, and the normalized weight that an event puts on a question pair at one coordinate.
--
--   **Setting.** Let $X,Y$ be finite question sets, $I$ a finite set of coordinates, $R$ a finite set of labels, $\mu$ a probability law on $X\times Y$ and $x_0\in X$, $y_0\in Y$ default questions. A question profile is $z=(z_i)_{i\in I}$ with $z_i=(x_i,y_i)\in X\times Y$; $z^{i\leftarrow q}$ is $z$ with its $i$-th entry replaced by $q\in X\times Y$, and $\mu^{\otimes I}(z)=\prod_{i\in I}\mu(z_i)$ is the product law. Let $\mu(\cdot\mid y)$ be the law on $X$ proportional to $x\mapsto\mu(x,y)$ (the point mass at $x_0$ if $\sum_x\mu(x,y)=0$), and $\mu(\cdot\mid x)$ the law on $Y$ proportional to $y\mapsto\mu(x,y)$ (the point mass at $y_0$ if $\sum_y\mu(x,y)=0$). For a function $g$ of profiles with values in a real vector space, the left and right resampling operators at coordinate $i$ are
--   $$(\mathcal L_ig)(z)=\sum_{x\in X}\mu(x\mid y_i)\,g\big(z^{i\leftarrow(x,y_i)}\big),\qquad(\mathcal R_ig)(z)=\sum_{y\in Y}\mu(y\mid x_i)\,g\big(z^{i\leftarrow(x_i,y)}\big).$$
--   Fix a list $l=(l_0,\dots,l_{L-1})$ of coordinates and families $F=(F_r)_{r\in R}$, $H=(H_r)_{r\in R}$ of functions of profiles.
--
--   1. **Left chain.** For $j\in\mathbb{N}$ and $r\in R$,
--   $$F^{(j)}_r=\mathcal L_{l_j}\mathcal L_{l_{j+1}}\cdots\mathcal L_{l_{L-1}}F_r,$$
--   so Alice's questions on the coordinates $l_j,\dots,l_{L-1}$ are resampled; $F^{(j)}_r=F_r$ for $j\ge L$.
--   2. **Right chain.** For $j\in\mathbb{N}$ and $r\in R$,
--   $$H^{(j)}_r=\mathcal R_{l_{j-1}}\cdots\mathcal R_{l_1}\mathcal R_{l_0}H_r,$$
--   so Bob's questions on $l_0,\dots,l_{j-1}$ are resampled; $H^{(0)}_r=H_r$, and for $j\ge L$ all coordinates of $l$ are resampled.
--   3. **Chain index set and chain families.** The index set is $\mathcal J_l=\{0,1,\dots,L\}\times R\times(X\times Y)^I$. If the $F_r$ take values in $m\times m$ complex matrices, the left chain family is the map $\mathcal J_l\ni(j,r,z)\mapsto F^{(j)}_r(z)$; if the $H_r$ take values in $n\times n$ complex matrices, the right chain family is $(j,r,z)\mapsto H^{(j)}_r(z)$.
--   4. **Mass at a coordinate.** Let $C\in\mathbb{C}^{m\times n}$ encode the bipartite vector $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$ and write $\mathrm{Pr}_C(M,N)=\operatorname{Re}\langle\psi_C,(M\otimes N)\psi_C\rangle$. Given real weights $\theta_r$ on profiles, a number $p\in\mathbb{R}$, a coordinate $i$, matrix families $F_r$ ($m\times m$) and $H_r$ ($n\times n$), and $q\in X\times Y$,
--   $$\operatorname{mass}_i(q)=\frac1p\sum_{r\in R}\mathbb{E}_{z\sim\mu^{\otimes I}}\Big[\theta_r(z)\,\mathrm{Pr}_C\big(F_r(z^{i\leftarrow q}),H_r(z^{i\leftarrow q})\big)\Big].$$
--   The weight $\theta_r$ is evaluated at the unmodified profile $z$, while the effects see the question pair $q$ at coordinate $i$.
--
--   In the conditioning argument for repeated entangled strategies, $F_r$ and $H_r$ are Alice's and Bob's effects for the outcome $r$ of a tested event, and the two chains interpolate, one coordinate at a time, between the original effects and effects with resampled questions. The index set $\mathcal J_l$ collects every effect occurring in the chains, so that all of them can be factored inside one common space. If the weights $\theta_r$ do not depend on the questions at coordinate $i$ and $p$ is the probability of the event, then $\mu(q)\operatorname{mass}_i(q)$ is the conditional probability, given the event, that the question pair at coordinate $i$ is $q$; thus $\operatorname{mass}_i$ is the density of this conditional distribution with respect to $\mu$.
--
--   **Formalization Note** The definitions are `chainLeft` (folding the left resampling over `l.drop j`), `chainRight` (folding the right resampling over `(l.take j).reverse`), `ExposureIndex` (the type `Fin (l.length+1) × R × Profile I X Y`), `chainLeftFamily`, `chainRightFamily` and `massAt`. The chains are defined for values in any real module. The factor $1/p$ follows Lean's convention $1/0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureChain.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureChain.lean by skeleton subtraction
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

namespace OAI

universe u_I u_X u_Y u_R u_m u_n u_E u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {E : Type u_E} [AddCommMonoid E] [Module ℝ E]
def chainLeft (μ : Law (X×Y)) (x₀ : X) (l : List I) (F : R → Profile I X Y → E)
    (j : ℕ) (r : R) : Profile I X Y → E := μ.lefts x₀ (l.drop j) (F r)
def chainRight (μ : Law (X×Y)) (y₀ : Y) (l : List I) (H : R → Profile I X Y → E)
    (j : ℕ) (r : R) : Profile I X Y → E := μ.rights y₀ (l.take j).reverse (H r)

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

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

abbrev ExposureIndex (l : List I) := Fin (l.length+1) × R × Profile I X Y

def chainLeftFamily (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (F : R → Profile I X Y → Matrix m m ℂ) :
    ExposureIndex (R := R) (X := X) (Y := Y) l → Matrix m m ℂ :=
  fun t => chainLeft μ x₀ l F t.1 t.2.1 t.2.2

def chainRightFamily (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (H : R → Profile I X Y → Matrix n n ℂ) :
    ExposureIndex (R := R) (X := X) (Y := Y) l → Matrix n n ℂ :=
  fun t => chainRight μ y₀ l H t.1 t.2.1 t.2.2

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def massAt (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (q : X×Y) : ℝ :=
  (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
    prob C (F r (Function.update z i q)) (H r (Function.update z i q)))

end ThresholdParallelRepetition.MixedExposure

end

end OAI


