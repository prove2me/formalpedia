-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_Refinement
-- name    : OAI_Probability_EntangledGames_Refinement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:25:38.811202+00:00
-- url     : https://prove2.me/theorems/5153e0a6-dc54-4935-9e4b-4b27cf1827ee
-- title:
--   Answer refinements of an event system and the single-round measurements they induce
-- statement:
--   This file refines the effects of an event system by the answers at a single coordinate and turns the refinement into measurements for one round of the game, using a transport of POVMs along a linear map.
--
--   **Setting.** Matrices are complex, $M^*$ is the conjugate transpose and $\mathbf 1$ the identity. A POVM on $\mathbb{C}^m$ with outcomes in a finite set $A$ is a family $(E_a)_{a\in A}$ of positive semidefinite matrices with $\sum_aE_a=\mathbf 1$. An event system $S$ over finite question sets $X,Y$, a finite set of coordinates $I$ and a finite label set $R$ provides: a probability law $\mu$ on $X\times Y$; default questions $x_0,y_0$; a list $l=(l_0,\dots,l_{L-1})$ of distinct coordinates; a coefficient matrix $C\in\mathbb{C}^{m\times n}$ of Hilbert–Schmidt norm $1$, standing for $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$; effects $0\le F_r(z)\le\mathbf 1$ for Alice and $0\le H_r(z)\le\mathbf 1$ for Bob, indexed by labels $r\in R$ and question profiles $z=(x_i,y_i)_{i\in I}$, where $F_r$ depends only on Alice's questions and $H_r$ only on Bob's; weights $\theta_r(z)\in[0,1]$; and the event probability $p>0$. Write $\mu^{\otimes I}$ for the product law of profiles, $z^{i\leftarrow q}$ for $z$ with entry $i$ replaced by $q$, $\mathrm{Pr}_C(M,N)=\operatorname{Re}\langle\psi_C,(M\otimes N)\psi_C\rangle$, and $\mathcal L_i$, $\mathcal R_i$ for the operators that average a function of $z$ over a fresh $x_i$ drawn from the conditional law $\mu(\cdot\mid y_i)$, respectively over a fresh $y_i$ drawn from $\mu(\cdot\mid x_i)$. The system also provides $f_j(r,z)=(\mathcal L_{l_j}\cdots\mathcal L_{l_{L-1}}F_r)(z)$, $h_j(r,z)=(\mathcal R_{l_{j-1}}\cdots\mathcal R_{l_0}H_r)(z)$ and square-root factors $U_j(r,z)\in\mathbb{C}^{(\mathcal J\times m)\times m}$, $V_j(r,z)\in\mathbb{C}^{(\mathcal J\times n)\times n}$, where $\mathcal J=\{0,\dots,L\}\times R\times(X\times Y)^I$, with $U_j^*U_j=f_j$ and $V_j^*V_j=h_j$ for $j\le L$.
--
--   1. **Transported POVM.** Let $F\in\mathbb{C}^{m\times n}$, let $(G_a)_{a\in A}$ be positive semidefinite $n\times n$ matrices with $\sum_aG_a=F^*F$, and let $a_0\in A$. With $T=F^*F$, $T^{+}$ its pseudo-inverse (the nonzero eigenvalues are inverted and the eigenvalue $0$ is kept) and $\Pi=FT^{+}F^*$ the orthogonal projection onto the range of $F$, the transported POVM on $\mathbb{C}^m$ has effects
--   $$E_a=FT^{+}\,G_a\,T^{+}F^*+[a=a_0]\,(\mathbf 1-\Pi)\qquad(a\in A).$$
--   It is a POVM, and $F^*E_aF=G_a$ for every $a$.
--   2. **Refinement.** For finite answer sets $A,B$, a refinement of $S$ assigns to each coordinate $i$, label $r$ and profile $z$ positive semidefinite matrices $F^i_r(z;a)\in\mathbb{C}^{m\times m}$ ($a\in A$) and $H^i_r(z;b)\in\mathbb{C}^{n\times n}$ ($b\in B$) with
--   $$\sum_{a\in A}F^i_r(z;a)=F_r(z),\qquad\sum_{b\in B}H^i_r(z;b)=H_r(z),$$
--   such that each $F^i_r(\cdot\,;a)$ depends only on Alice's questions and each $H^i_r(\cdot\,;b)$ only on Bob's.
--   3. **Resampled refinements.** For $j\in\{0,\dots,L-1\}$ let $\tilde F_{j,r}(z;a)=\big(\mathcal L_{l_{j+1}}\cdots\mathcal L_{l_{L-1}}F^{l_j}_r(\cdot\,;a)\big)(z)$ and $\tilde H_{j,r}(z;b)=\big(\mathcal R_{l_{j-1}}\cdots\mathcal R_{l_0}H^{l_j}_r(\cdot\,;b)\big)(z)$. They are positive semidefinite, $\sum_a\tilde F_{j,r}(z;a)=f_{j+1}(r,z)$ and $\sum_b\tilde H_{j,r}(z;b)=h_j(r,z)$.
--   4. **Local POVMs.** Given default answers $a_0\in A$ and $b_0\in B$, $\mathcal P_{j,r,z}$ is the POVM on $\mathbb{C}^{\mathcal J\times m}$ transported from $(\tilde F_{j,r}(z;a))_{a\in A}$ along $U_{j+1}(r,z)$ with default $a_0$, and $\mathcal Q_{j,r,z}$ is the POVM on $\mathbb{C}^{\mathcal J\times n}$ transported from $(\tilde H_{j,r}(z;b))_{b\in B}$ along $V_j(r,z)$ with default $b_0$. The hypotheses of item 1 hold by item 3 and the factorizations $U_{j+1}^*U_{j+1}=f_{j+1}$ and $V_j^*V_j=h_j$.
--   5. **Single-round measurements.** For Alice's question $x\in X$, $P_j(x)$ is the block-diagonal POVM with one block for each label $(r,z)\in R\times(X\times Y)^I$, the block $(r,z)$ being $\mathcal P_{j,r,z^{l_j\leftarrow(x,y_0)}}$; for Bob's question $y\in Y$, $Q_j(y)$ has the blocks $\mathcal Q_{j,r,z^{l_j\leftarrow(x_0,y)}}$.
--   6. **Score.** For a coordinate $i$ and a predicate $V$ on $X\times Y\times A\times B$,
--   $$\operatorname{score}(i,V)=\frac1p\sum_{r\in R}\mathbb{E}_{z\sim\mu^{\otimes I}}\Big[\theta_r(z)\sum_{a\in A}\sum_{b\in B}[V(x_i,y_i,a,b)]\;\mathrm{Pr}_C\big(F^i_r(z;a),H^i_r(z;b)\big)\Big],$$
--   where $[V(\dots)]$ is $1$ if the predicate holds and $0$ otherwise.
--
--   When the refinement splits the event outcome $r$ further according to the answers at coordinate $i$, $\operatorname{score}(i,V)$ is the probability of winning coordinate $i$ conditioned on the event. The measurements $P_j(x)$ and $Q_j(y)$ depend only on the player's own question. Paired with the hybrid states $D_j(q)$ of the event system they reproduce this conditional winning probability: in the main argument, the $\mu$-average over $q=(x,y)$ of the payoff $\sum_{a,b}[V(x,y,a,b)]\,\mathrm{Pr}_{D_j(q)}\big(P_j(x)_a,Q_j(y)_b\big)$ equals $\operatorname{score}(l_j,V)$. This is how a conditioned repeated strategy yields a strategy for a single round.
--
--   **Formalization Note** The definitions are `POVM.transport` (with effects `transportedEffect`), the structure `Refinement` (fields `left`, `right` and their positivity, total and locality conditions), `leftFine`, `rightFine`, `leftPOVM`, `rightPOVM`, `P`, `Q` and `score`; `leftFine_pos`, `rightFine_pos`, `leftFine_total` and `rightFine_total` are the facts of item 3, and `coherentDecEq` is a decidable-equality instance. The pseudo-inverse is the continuous functional calculus of $t\mapsto t^{-1}$ with Lean's convention $0^{-1}=0$. The square-root factors, and hence the local and single-round measurements, are formed for nonempty $X$, $Y$ and $R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Refinement.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Refinement.lean by skeleton subtraction
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

namespace OAI

universe u_m u_n u_A u_X u_Y u_I u_R u_B

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling.POVM
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]
def transport (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ*F) (a₀ : A) : POVM m A where
  effect := transportedEffect F G a₀
  pos := transportedEffect_pos F G hG a₀
  total := transportedEffect_sum F G hGT a₀
end QuantumSampling.POVM
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

structure Refinement (S : EventSystem X Y I R m n) (A : Type u_A) (B : Type u_B) [Fintype A] [Fintype B] where
  left : I → R → Profile I X Y → A → Matrix m m ℂ
  right : I → R → Profile I X Y → B → Matrix n n ℂ
  left_pos : ∀ i r z a, (left i r z a).PosSemidef
  right_pos : ∀ i r z b, (right i r z b).PosSemidef
  left_total : ∀ i r z, ∑ a, left i r z a = S.F r z
  right_total : ∀ i r z, ∑ b, right i r z b = S.H r z
  left_local : ∀ i r a j, IgnoresRight (fun z => left i r z a) j
  right_local : ∀ i r b j, IgnoresLeft (fun z => right i r z b) j
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)
def leftFine (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) : Matrix m m ℂ :=
  S.μ.lefts S.x₀ (S.l.drop (j+1)) (fun z => T.left S.l[j.val] r z a) z
def rightFine (j : Fin S.l.length) (r : R) (z : Profile I X Y) (b : B) : Matrix n n ℂ :=
  S.μ.rights S.y₀ (S.l.take j).reverse (fun z => T.right S.l[j.val] r z b) z
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_pos (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) : (T.leftFine j r z a).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (fun z => T.left_pos _ r z a) z
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_pos (j : Fin S.l.length) (r : R) (z : Profile I X Y) (b : B) : (T.rightFine j r z b).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (fun z => T.right_pos _ r z b) z
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_total (j : Fin S.l.length) (r : R) (z : Profile I X Y) :
    ∑ a, T.leftFine j r z a = S.f (j+1) r z := by
  simp only [leftFine]
  rw [← lefts_sum]
  simp only [T.left_total]
  rfl
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_total (j : Fin S.l.length) (r : R) (z : Profile I X Y) :
    ∑ b, T.rightFine j r z b = S.h j r z := by
  simp only [rightFine]
  rw [← rights_sum]
  simp only [T.right_total]
  rfl
def leftPOVM (a₀ : A) (j : Fin S.l.length) (r : R) (z : Profile I X Y) : POVM (S.J×m) A :=
  POVM.transport (S.U (j+1) r z) (T.leftFine j r z) (T.leftFine_pos j r z)
    ((T.leftFine_total j r z).trans (S.U_gram (by omega) r z).symm) a₀
def rightPOVM (b₀ : B) (j : Fin S.l.length) (r : R) (z : Profile I X Y) : POVM (S.J×n) B :=
  POVM.transport (S.V j r z) (T.rightFine j r z) (T.rightFine_pos j r z)
    ((T.rightFine_total j r z).trans (S.V_gram (by omega) r z).symm) b₀

instance coherentDecEq (l : List I) : DecidableEq (((ExposureIndex (R := R) (X := X) (Y := Y) l)×m)×(R×Profile I X Y)) :=
  @instDecidableEqProd _ _ (inferInstance : DecidableEq ((ExposureIndex (R := R) (X := X) (Y := Y) l)×m))
    (inferInstance : DecidableEq (R×Profile I X Y))

def P (a₀ : A) (j : Fin S.l.length) (x : X) : POVM ((S.J×m)×(R×Profile I X Y)) A := by
  classical
  exact POVM.blocks (fun t : R×Profile I X Y => T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] (x,S.y₀)))
def Q (b₀ : B) (j : Fin S.l.length) (y : Y) : POVM ((S.J×n)×(R×Profile I X Y)) B := by
  classical
  exact POVM.blocks (fun t : R×Profile I X Y => T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] (S.x₀,y)))

end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
end QuantumSampling
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)

def score (i : I) (V : X → Y → A → B → Bool) : ℝ :=
  (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
    ∑ a, ∑ b, if V (z i).1 (z i).2 a b then prob S.C (T.left i r z a) (T.right i r z b) else 0)

end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

end OAI


