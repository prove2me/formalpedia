-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_ExposureData
-- name    : OAI_Probability_EntangledGames_ExposureData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:22:44.471991+00:00
-- url     : https://prove2.me/theorems/7617bd8d-ebc9-4a56-9993-b69ba6680f36
-- title:
--   Event systems of conditioned repeated strategies and their hybrid states
-- statement:
--   This file packages the data describing an event in a repeated entangled strategy into one structure, and derives from it the square-root factors of resampled effects, the hybrid states, their one-sided versions and the density of the conditioned questions.
--
--   **Notation.** $X,Y$ are finite question sets, $I$ a finite set of coordinates, $R$ a finite set of labels and $m,n$ finite index sets. A profile is $z=(z_i)_{i\in I}$ with $z_i=(x_i,y_i)\in X\times Y$; $z^{i\leftarrow q}$ replaces its $i$-th entry by $q$, and $\mu^{\otimes I}(z)=\prod_i\mu(z_i)$ for a law $\mu$ on $X\times Y$. A function $g$ of profiles *ignores Alice at $i$* if $g$ does not change when $x_i$ is changed, and *ignores Bob at $i$* if it does not change when $y_i$ is changed. For $C\in\mathbb{C}^{m\times n}$ let $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$, $\|C\|_2^2=\sum_{a,b}|C_{ab}|^2$ and $\mathrm{Pr}_C(M,N)=\operatorname{Re}\langle\psi_C,(M\otimes N)\psi_C\rangle$.
--
--   1. **Event system.** An event system consists of: (a) a probability law $\mu$ on $X\times Y$ and default questions $x_0\in X$, $y_0\in Y$; (b) a list $l=(l_0,\dots,l_{L-1})$ of pairwise distinct coordinates; (c) a coefficient matrix $C$ with $\|C\|_2=1$; (d) for every label $r$ and profile $z$, matrices $F_r(z)\in\mathbb{C}^{m\times m}$ and $H_r(z)\in\mathbb{C}^{n\times n}$ with $0\le F_r(z)\le\mathbf 1$ and $0\le H_r(z)\le\mathbf 1$ in the Loewner order, such that every $F_r$ ignores Bob and every $H_r$ ignores Alice at every coordinate; (e) weights $\theta_r(z)\in[0,1]$ such that each $\theta_r$ ignores both Alice and Bob at every coordinate of $l$; (f) the bound $\sum_r\theta_r(z)\,\mathrm{Pr}_C(F_r(z),H_r(z))\le1$ for every profile $z$; (g) a number $p>0$ with
--   $$\sum_{r\in R}\mathbb{E}_{z\sim\mu^{\otimes I}}\big[\theta_r(z)\,\mathrm{Pr}_C\big(F_r(z),H_r(z)\big)\big]=p.$$
--   2. **Resampled effects.** Let $\mu(\cdot\mid y)$ be the conditional law of Alice's question given Bob's question $y$ (the point mass at $x_0$ if $y$ has marginal probability $0$) and $\mu(\cdot\mid x)$ the conditional law of Bob's question given $x$ (with default $y_0$). The resampling operators $(\mathcal L_ig)(z)=\sum_x\mu(x\mid y_i)\,g(z^{i\leftarrow(x,y_i)})$ and $(\mathcal R_ig)(z)=\sum_y\mu(y\mid x_i)\,g(z^{i\leftarrow(x_i,y)})$ define, for $j\in\mathbb{N}$,
--   $$f_j(r,z)=\big(\mathcal L_{l_j}\cdots\mathcal L_{l_{L-1}}F_r\big)(z),\qquad h_j(r,z)=\big(\mathcal R_{l_{j-1}}\cdots\mathcal R_{l_0}H_r\big)(z),$$
--   which are positive semidefinite. They form two families indexed by $\mathcal J=\{0,\dots,L\}\times R\times(X\times Y)^I$, namely $(j,r,z)\mapsto f_j(r,z)$ and $(j,r,z)\mapsto h_j(r,z)$.
--   3. **Square-root factors.** For a family $(A_t)_{t\in\mathcal J}$ of positive semidefinite $m\times m$ matrices let $\Gamma=\int_0^\infty K(s)^*K(s)\,ds$, where $K(s)$ is the block row with blocks $A_t(A_t+s\mathbf 1)^{-1}$; the common factor of a member $A_t$ is the $(\mathcal J\times m)\times m$ matrix of the columns of $\Gamma^{1/2}$ indexed by $\{t\}\times m$. $U_j(r,z)$ is the common factor of $f_j(r,z)$ in the family of the $f$'s, and $V_j(r,z)\in\mathbb{C}^{(\mathcal J\times n)\times n}$ is the common factor of $h_j(r,z)$ in the family of the $h$'s. For $j\le L$,
--   $$U_j(r,z)^*U_j(r,z)=f_j(r,z),\qquad V_j(r,z)^*V_j(r,z)=h_j(r,z).$$
--   4. **Hybrid states.** For $j\in\{0,\dots,L-1\}$ and $q\in X\times Y$, $D_j(q)$ is the block-diagonal matrix with one block for each label $(r,z)\in R\times(X\times Y)^I$,
--   $$D_j(q)=\bigoplus_{(r,z)}\sqrt{\frac{\mu^{\otimes I}(z)\,\theta_r(z)}{p}}\;U_{j+1}(r,z')\,C\,V_j(r,z')^{\mathsf T},\qquad z'=z^{l_j\leftarrow q},$$
--   the coefficient matrix of a vector in which both parties hold a copy of the label $(r,z)$.
--   5. **One-sided states.** $\mathrm{raw}^A_j(x)$ is defined like $D_j$ but with $U_{j+1},V_{j+1}$ and $q=(x,y_0)$; $\mathrm{raw}^B_j(y)$ uses $U_j,V_j$ and $q=(x_0,y)$.
--   6. **Event density.** $\rho(z)=\frac1p\sum_r\theta_r(z)\,\mathrm{Pr}_C(F_r(z),H_r(z))$.
--
--   An event system abstracts a repeated strategy with shared state $\psi_C$ in which an event has been tested: $r$ is its outcome, $\theta_r$ an acceptance weight that does not look at the coordinates of $l$, $p$ the probability of the event, and $l$ lists untested coordinates. Then $\rho$ is the density, with respect to $\mu^{\otimes I}$, of the questions conditioned on the event, and $D_j(q)$ is the subnormalized conditioned state at step $j$ of a hybrid argument, in which Alice's questions on $l_{j+1},\dots,l_{L-1}$ and Bob's questions on $l_0,\dots,l_{j-1}$ have been resampled and the questions at the fresh coordinate $l_j$ are set to $q$. The one-sided states $\mathrm{raw}^A_j(x)$ and $\mathrm{raw}^B_j(y)$ depend only on Alice's, respectively Bob's, question, as a single-round strategy requires.
--
--   **Formalization Note** The structure is `EventSystem` (fields `μ`, `x₀`, `y₀`, `l`, `nodup`, `C`, `hC`, `F`, `H`, the positivity and locality fields, `θ`, `event_le_one`, `p`, `hp`, `mass`). The derived objects are `J`, `f`, `h`, `A`, `B` (abbreviations of the chain constructions), `U`, `V` (built with `commonMap`), `D`, `rawA`, `rawB` and `density`; `f_pos`, `h_pos`, `U_gram` and `V_gram` are the positivity and factorization facts of items 2 and 3. The factors need a nonempty index set, so $X$, $Y$ and $R$ are assumed nonempty for them; block weights pass through `Real.sqrt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureData.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureData.lean by skeleton subtraction
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

namespace OAI

universe u_X u_Y u_I u_R u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

structure EventSystem where
  μ : Law (X×Y)
  x₀ : X
  y₀ : Y
  l : List I
  nodup : l.Nodup
  C : Matrix m n ℂ
  hC : hsSq C = 1
  F : R → Profile I X Y → Matrix m m ℂ
  H : R → Profile I X Y → Matrix n n ℂ
  hF : ∀ r z, (F r z).PosSemidef
  hF1 : ∀ r z, F r z ≤ 1
  hH : ∀ r z, (H r z).PosSemidef
  hH1 : ∀ r z, H r z ≤ 1
  localF : ∀ r i, IgnoresRight (F r) i
  localH : ∀ r i, IgnoresLeft (H r) i
  θ : R → Profile I X Y → ℝ
  hθ : ∀ r z, 0 ≤ θ r z
  hθ1 : ∀ r z, θ r z ≤ 1
  localθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i
  localθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i
  event_le_one : ∀ z, (∑ r, θ r z*prob C (F r z) (H r z)) ≤ 1
  p : ℝ
  hp : 0 < p
  mass : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p

variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
namespace EventSystem
variable (S : EventSystem X Y I R m n)
abbrev J := ExposureIndex (R := R) (X := X) (Y := Y) S.l
abbrev f := chainLeft S.μ S.x₀ S.l S.F
abbrev h := chainRight S.μ S.y₀ S.l S.H
abbrev A := chainLeftFamily S.μ S.x₀ S.l S.F
abbrev B := chainRightFamily S.μ S.y₀ S.l S.H

def U (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×m) m ℂ := commonMap S.A (S.f j r z)
def V (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×n) n ℂ := commonMap S.B (S.h j r z)

omit [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma f_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.f j r z).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (S.hF r) z
omit [DecidableEq X] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma h_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.h j r z).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (S.hH r) z
lemma U_gram {j : ℕ} (hj : j ≤ S.l.length) (r : R) (z : Profile I X Y) :
    (S.U j r z)ᴴ*S.U j r z = S.f j r z :=
  commonMap_gram S.A (fun t => S.f_pos _ _ _) ⟨(⟨j, by omega⟩,r,z),rfl⟩
lemma V_gram {j : ℕ} (hj : j ≤ S.l.length) (r : R) (z : Profile I X Y) :
    (S.V j r z)ᴴ*S.V j r z = S.h j r z :=
  commonMap_gram S.B (fun t => S.h_pos _ _ _) ⟨(⟨j, by omega⟩,r,z),rfl⟩

def D (j : Fin S.l.length) : X×Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V j)
def rawA (j : Fin S.l.length) : X → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun x => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) (x,S.y₀)
def rawB (j : Fin S.l.length) : Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun y => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) (S.x₀,y)

def density : Profile I X Y → ℝ := eventDensity S.θ S.p S.C S.F S.H
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI


