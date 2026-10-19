-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
-- name    : OAI_Probability_EntangledGames_RepeatedModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:33:58.419119+00:00
-- url     : https://prove2.me/theorems/d03188f2-8ed3-4eac-8e64-b836780e20fe
-- title:
--   Model of a parallel-repeated entangled strategy and its winning events on sets of rounds
-- statement:
--   This file sets up the probabilistic model of an entangled strategy for several parallel rounds of a two-player game, the events that every round of a set $c$ is won, and the translation of such an event into an event system and a refinement on which the conditioning argument operates.
--
--   **Notation.** $X,Y$ are finite question sets, $A,B$ finite answer sets, $I$ a finite set of rounds (coordinates) and $m,n$ finite index sets. A probability law on a finite set is a nonnegative weight function of total mass $1$, and $\mathbb{E}$ denotes the corresponding average. A POVM on $\mathbb{C}^m$ with outcomes in a finite set $\Omega$ is a family $(E_\omega)_{\omega\in\Omega}$ of positive semidefinite matrices with $\sum_\omega E_\omega=\mathbf 1$; its coarse-graining along a map $g\colon\Omega\to\Omega'$ is the POVM with effects $\sum_{\omega:\,g(\omega)=\omega'}E_\omega$. For $C\in\mathbb{C}^{m\times n}$ let $\psi_C=\sum_{i,j}C_{ij}\,e_i\otimes e_j$, $\|C\|_2^2=\sum_{i,j}|C_{ij}|^2$ and $\mathrm{Pr}_C(S,T)=\operatorname{Re}\langle\psi_C,(S\otimes T)\psi_C\rangle$ for $S\in\mathbb{C}^{m\times m}$, $T\in\mathbb{C}^{n\times n}$. A question profile is $z=(z_i)_{i\in I}$ with $z_i=(x_i,y_i)\in X\times Y$, and $\mathbf x(z)=(x_i)_{i\in I}$, $\mathbf y(z)=(y_i)_{i\in I}$ are Alice's and Bob's question tuples.
--
--   1. **Repeated model.** A repeated model $M$ consists of a probability law $\mu$ on $X\times Y$ (the question distribution of one round), a coefficient matrix $C$ with $\|C\|_2=1$, for every $\mathbf x\in X^I$ a POVM $P^{\mathbf x}$ on $\mathbb{C}^m$ with outcomes $\mathbf a\in A^I$, for every $\mathbf y\in Y^I$ a POVM $Q^{\mathbf y}$ on $\mathbb{C}^n$ with outcomes $\mathbf b\in B^I$, and an acceptance predicate $V$ on $X\times Y\times A\times B$.
--   2. **Joint law.** Given questions $z$, the answers follow the outcome law $(\mathbf a,\mathbf b)\mapsto\mathrm{Pr}_C(P^{\mathbf x(z)}_{\mathbf a},Q^{\mathbf y(z)}_{\mathbf b})$, and the joint law of questions and answers on $(X\times Y)^I\times A^I\times B^I$ is
--   $$\mathbb{P}_M(z,\mathbf a,\mathbf b)=\Big(\prod_{i\in I}\mu(z_i)\Big)\,\mathrm{Pr}_C\big(P^{\mathbf x(z)}_{\mathbf a},Q^{\mathbf y(z)}_{\mathbf b}\big).$$
--   3. **Winning events.** Round $i$ is won at $(z,\mathbf a,\mathbf b)$ if $V(x_i,y_i,a_i,b_i)$ holds. For a finite set $c\subseteq I$, $\mathbf 1_c(z,\mathbf a,\mathbf b)$ is $1$ if every round of $c$ is won and $0$ otherwise, and $\operatorname{mass}(c)=\mathbb{E}_{\mathbb{P}_M}[\mathbf 1_c]$ is the probability that all rounds of $c$ are won.
--   4. **Records, masks and coarse measurements.** A record on $c$ is a pair $r=(r_A,r_B)$ of maps $r_A\colon c\to A$ and $r_B\colon c\to B$. The mask $\operatorname{mask}_c(r,z)$ is $1$ if $V(x_i,y_i,r_A(i),r_B(i))$ holds for all $i\in c$, and $0$ otherwise. The coarse measurements $P^{\mathbf x(z)}|_c$ and $Q^{\mathbf y(z)}|_c$ are the coarse-grainings of $P^{\mathbf x(z)}$ and $Q^{\mathbf y(z)}$ along the restriction of answer tuples to $c$.
--   5. **Event system of $c$.** If $\operatorname{mass}(c)>0$, the exposure of $c$ is the event system with question law $\mu$, arbitrary default questions $x_0\in X$ and $y_0\in Y$, the list $l$ of the rounds in $I\setminus c$ (each once, in a fixed order), the state $C$, the records on $c$ as labels, the effects $F_r(z)=(P^{\mathbf x(z)}|_c)_{r_A}$ and $H_r(z)=(Q^{\mathbf y(z)}|_c)_{r_B}$, the weights $\theta_r(z)=\operatorname{mask}_c(r,z)$ and the event probability $p=\operatorname{mass}(c)$.
--   6. **Refinement.** For a round $i$, the fine measurements are the coarse-grainings of $P^{\mathbf x(z)}$ along $\mathbf a\mapsto(\mathbf a|_c,a_i)$ and of $Q^{\mathbf y(z)}$ along $\mathbf b\mapsto(\mathbf b|_c,b_i)$. The refinement of the event system of $c$ assigns to $(i,r,z)$ and answers $a\in A$, $b\in B$ the fine effects with outcomes $(r_A,a)$ and $(r_B,b)$.
--
--   An event system, as used in item 5, is a list of conditions on such data: effects between $0$ and $\mathbf 1$; Alice's effects $F_r(z)$ depend only on $\mathbf x(z)$ and Bob's effects $H_r(z)$ only on $\mathbf y(z)$; the weights lie in $[0,1]$ and do not depend on the rounds in $l$; $\sum_r\theta_r(z)\,\mathrm{Pr}_C(F_r(z),H_r(z))\le1$ for every $z$; and, with $\mu^{\otimes I}(z)=\prod_{i\in I}\mu(z_i)$, the mass identity
--   $$\sum_{r}\mathbb{E}_{z\sim\mu^{\otimes I}}\big[\theta_r(z)\,\mathrm{Pr}_C\big(F_r(z),H_r(z)\big)\big]=p.$$
--   A refinement, as in item 6, requires fine effects that are positive semidefinite, sum over the answer at $i$ to the coarse effects, and depend only on the respective player's questions. The auxiliary lemmas of the file verify these conditions; in particular $\sum_r\operatorname{mask}_c(r,z)\,\mathrm{Pr}_C(F_r(z),H_r(z))$ is the probability, given the questions $z$, that all rounds of $c$ are won, and the mass identity holds with $p=\operatorname{mass}(c)$.
--
--   When $\mu$ is the question distribution of a game and $V$ its acceptance predicate, a repeated model is an entangled strategy for $|I|$ parallel rounds of that game. Conditioning on winning a set $c$ of rounds is the basic step of the threshold argument; the event system and refinement of $c$ carry the conditioned strategy to the rounds outside $c$, where a strategy for a single round is extracted.
--
--   **Formalization Note** The structure is `RepeatedModel` (fields `μ`, `C`, `hC`, `P`, `Q`, `V`, with `V` Boolean-valued). The derived objects are `answers`, `joint`, `winsAt`, `indicator`, `mass`, `Records`, `restrictA`, `restrictB`, `mask`, `coarseA`, `coarseB`, `exposure`, `fineA`, `fineB` and `refinement`; the remaining lemmas (`joint_avg`, `mask_restrict`, `coarse_event`, `mass_coarse`, the bounds and the locality lemmas, and two lemmas on updating one player's question in a profile) are the verifications mentioned above. `exposure` takes the hypothesis $0<\operatorname{mass}(c)$, lists $I\setminus c$ with `Finset.toList`, and picks the default questions with `Classical.arbitrary`, which needs $X$ and $Y$ nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/RepeatedModel.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/RepeatedModel.lean by skeleton subtraction
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

namespace OAI

universe u_X u_Y u_A u_B u_I u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

structure RepeatedModel (X : Type u_X) (Y : Type u_Y) (A : Type u_A) (B : Type u_B) (I : Type u_I) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  μ : Law (X×Y)
  C : Matrix m n ℂ
  hC : hsSq C = 1
  P : (I → X) → POVM m (I → A)
  Q : (I → Y) → POVM n (I → B)
  V : X → Y → A → B → Bool

namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : RepeatedModel X Y A B I m n)
abbrev Result := Profile I X Y × ((I→A)×(I→B))
def answers (z : Profile I X Y) : Law ((I→A)×(I→B)) :=
  outcomeLaw M.C M.hC (M.P (fun i => (z i).1)) (M.Q (fun i => (z i).2))
def joint : Law (Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) where
  weight t := (pi (fun _ : I => M.μ)).weight t.1 * (M.answers t.1).weight t.2
  nonneg t := mul_nonneg ((pi _).nonneg t.1) ((M.answers t.1).nonneg t.2)
  total := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (M.answers _).total, mul_one, (pi _).total]
lemma joint_avg (f : Result (X := X) (Y := Y) (A := A) (B := B) (I := I) → ℝ) :
    M.joint.avg f = (pi (fun _ : I => M.μ)).avg (fun z => (M.answers z).avg (fun w => f (z,w))) := by
  simp only [avg, joint, smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
def winsAt (t : Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) (i : I) : Bool :=
  M.V (t.1 i).1 (t.1 i).2 (t.2.1 i) (t.2.2 i)
def indicator (c : Finset I) (t : Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) : ℝ :=
  if ∀ i ∈ c, M.winsAt t i then 1 else 0
def mass (c : Finset I) : ℝ := M.joint.avg (M.indicator c)
lemma indicator_le_one (c : Finset I) (t) : M.indicator c t ≤ 1 := by
  unfold indicator; split_ifs <;> norm_num
abbrev Records (c : Finset I) := (c → A)×(c → B)
def restrictA (c : Finset I) (a : I→A) : c → A := fun i => a i
def restrictB (c : Finset I) (b : I→B) : c → B := fun i => b i
def mask (c : Finset I) (r : Records (A := A) (B := B) c) (z : Profile I X Y) : ℝ :=
  if ∀ i : c, M.V (z i).1 (z i).2 (r.1 i) (r.2 i) then 1 else 0
def coarseA (c : Finset I) (z : Profile I X Y) : POVM m (c → A) :=
  (M.P (fun i => (z i).1)).coarsen (restrictA c)
def coarseB (c : Finset I) (z : Profile I X Y) : POVM n (c → B) :=
  (M.Q (fun i => (z i).2)).coarsen (restrictB c)
lemma mask_restrict (c : Finset I) (z : Profile I X Y) (a : I→A) (b : I→B) :
    M.mask c (restrictA c a,restrictB c b) z = M.indicator c (z,a,b) := by
  simp only [mask, indicator, winsAt, restrictA, restrictB]
  congr 1
  exact propext Subtype.forall
lemma coarse_event (c : Finset I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z * prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2)) =
      (M.answers z).avg (fun w => M.indicator c (z,w)) := by
  rw [Fintype.sum_prod_type, coarseA, coarseB, coarsen_prob_sum]
  simp only [mask_restrict, answers, outcomeLaw_avg, mul_comm]
lemma mask_nonneg (c : Finset I) (r) (z) : 0 ≤ M.mask c r z := by
  unfold mask; split_ifs <;> norm_num
lemma mask_le_one (c : Finset I) (r) (z) : M.mask c r z ≤ 1 := by
  unfold mask; split_ifs <;> norm_num
lemma coarse_event_le_one (c : Finset I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z * prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2)) ≤ 1 := by
  rw [M.coarse_event]
  exact (M.answers z).avg_le_const (fun w => M.indicator_le_one c (z,w))
lemma mass_coarse (c : Finset I) :
    (∑ r : Records (A := A) (B := B) c, (pi (fun _ : I => M.μ)).avg (fun z => M.mask c r z *
      prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2))) = M.mass c := by
  rw [← avg_sum]
  simp only [M.coarse_event]
  exact (M.joint_avg _).symm
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace FiniteProbability.Law
variable {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [DecidableEq I]
lemma firsts_updateRight (z : Profile I X Y) (i : I) (y : Y) :
    (fun j => (updateRight z i y j).1) = fun j => (z j).1 := by
  funext j
  by_cases h : j=i
  · subst j; simp [updateRight]
  · simp [updateRight, Function.update_of_ne h]
lemma seconds_updateLeft (z : Profile I X Y) (i : I) (x : X) :
    (fun j => (updateLeft z i x j).2) = fun j => (z j).2 := by
  funext j
  by_cases h : j=i
  · subst j; simp [updateLeft]
  · simp [updateLeft, Function.update_of_ne h]
end FiniteProbability.Law
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma coarseA_local (c : Finset I) (r : c→A) (i : I) : IgnoresRight (fun z => (M.coarseA c z).effect r) i := by
  intro z y
  simp only [coarseA, firsts_updateRight]
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma coarseB_local (c : Finset I) (r : c→B) (i : I) : IgnoresLeft (fun z => (M.coarseB c z).effect r) i := by
  intro z x
  simp only [coarseB, seconds_updateLeft]
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_congr (c : Finset I) (r : Records (A := A) (B := B) c) {z z' : Profile I X Y}
    (hz : ∀ i ∈ c, z i = z' i) : M.mask c r z = M.mask c r z' := by
  simp only [mask]
  congr 1
  apply propext
  exact forall_congr' (fun i => by rw [hz i i.property])
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_local_left (c : Finset I) (r : Records (A := A) (B := B) c) (i : I) (hi : i ∉ c) : IgnoresLeft (M.mask c r) i := by
  intro z x
  apply M.mask_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_local_right (c : Finset I) (r : Records (A := A) (B := B) c) (i : I) (hi : i ∉ c) : IgnoresRight (M.mask c r) i := by
  intro z y
  apply M.mask_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

def exposure (c : Finset I) (hp : 0 < M.mass c) : EventSystem X Y I (Records (A := A) (B := B) c) m n where
  μ := M.μ
  x₀ := Classical.arbitrary X
  y₀ := Classical.arbitrary Y
  l := cᶜ.toList
  nodup := cᶜ.nodup_toList
  C := M.C
  hC := M.hC
  F r z := (M.coarseA c z).effect r.1
  H r z := (M.coarseB c z).effect r.2
  hF r z := (M.coarseA c z).pos r.1
  hF1 r z := (M.coarseA c z).le_one r.1
  hH r z := (M.coarseB c z).pos r.2
  hH1 r z := (M.coarseB c z).le_one r.2
  localF r i := M.coarseA_local c r.1 i
  localH r i := M.coarseB_local c r.2 i
  θ := M.mask c
  hθ := M.mask_nonneg c
  hθ1 := M.mask_le_one c
  localθL r i hi := M.mask_local_left c r i (by simpa only [Finset.mem_toList, Finset.mem_compl] using hi)
  localθR r i hi := M.mask_local_right c r i (by simpa only [Finset.mem_toList, Finset.mem_compl] using hi)
  event_le_one := M.coarse_event_le_one c
  p := M.mass c
  hp := hp
  mass := M.mass_coarse c

def fineA (c : Finset I) (i : I) (z : Profile I X Y) : POVM m ((c→A)×A) :=
  (M.P (fun j => (z j).1)).coarsen (fun a => (restrictA c a,a i))
def fineB (c : Finset I) (i : I) (z : Profile I X Y) : POVM n ((c→B)×B) :=
  (M.Q (fun j => (z j).2)).coarsen (fun b => (restrictB c b,b i))

def refinement (c : Finset I) (hp : 0 < M.mass c) : Refinement (M.exposure c hp) A B where
  left i r z a := (M.fineA c i z).effect (r.1,a)
  right i r z b := (M.fineB c i z).effect (r.2,b)
  left_pos i r z a := (M.fineA c i z).pos (r.1,a)
  right_pos i r z b := (M.fineB c i z).pos (r.2,b)
  left_total i r z := POVM.coarsen_slice _ (restrictA c) (fun a => a i) r.1
  right_total i r z := POVM.coarsen_slice _ (restrictB c) (fun b => b i) r.2
  left_local i r a j := by intro z y; simp only [fineA, firsts_updateRight]
  right_local i r b j := by intro z x; simp only [fineB, seconds_updateLeft]
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI


