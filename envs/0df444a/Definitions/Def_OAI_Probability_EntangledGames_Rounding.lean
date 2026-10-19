-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_Rounding
-- name    : OAI_Probability_EntangledGames_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:30:39.377986+00:00
-- url     : https://prove2.me/theorems/4933e2d1-e5a4-46cb-865d-51c7c1257fd3
-- title:
--   Question law of a game, uniform law, and the outcome law of a bipartite measurement
-- statement:
--   This file provides three probability laws used to analyse quantum strategies with finite probability tools, together with bookkeeping identities for coarse-grained measurements.
--
--   **Notation.** A probability law on a finite set $\Omega$ is a function $\rho\colon\Omega\to[0,\infty)$ with $\sum_\omega\rho(\omega)=1$. Matrices are complex and $\mathbf 1$ is the identity. A POVM on $\mathbb{C}^m$ with outcomes in a finite set $A$ is a family $(P_a)_{a\in A}$ of positive semidefinite matrices with $\sum_aP_a=\mathbf 1$; its coarse-graining along a map $f\colon A\to R$ is the POVM $P^f$ with $P^f_r=\sum_{a:\,f(a)=r}P_a$. A coefficient matrix $C\in\mathbb{C}^{m\times n}$ stands for $\psi_C=\sum_{i,j}C_{ij}\,e_i\otimes e_j$, $\|C\|_2^2=\sum_{i,j}|C_{ij}|^2$, and $\mathrm{Pr}_C(M,N)=\operatorname{Re}\langle\psi_C,(M\otimes N)\psi_C\rangle$.
--
--   1. **Question law of a game.** A game $G$ with question sets $\{0,\dots,x\}$ and $\{0,\dots,y\}$ (for natural numbers $x,y$) and finite answer sets is given by a nonnegative function $\pi$ on question pairs with total mass $1$ and an acceptance predicate. Its question law is $\pi$ regarded as a probability law on $\{0,\dots,x\}\times\{0,\dots,y\}$.
--   2. **Uniform law.** For a finite nonempty set $R$, $\operatorname{unif}_R(r)=1/|R|$ for every $r\in R$.
--   3. **Outcome law.** For $C$ with $\|C\|_2=1$, a POVM $P$ on $\mathbb{C}^m$ with outcomes in $A$ and a POVM $Q$ on $\mathbb{C}^n$ with outcomes in $B$, the outcome law is the probability law on $A\times B$ given by
--   $$\operatorname{out}_{C,P,Q}(a,b)=\mathrm{Pr}_C(P_a,Q_b),$$
--   the Born-rule distribution of the outcomes when Alice measures $P$ and Bob measures $Q$ on $\psi_C$.
--
--   The file also proves: $\sum_{a,b}\mathrm{Pr}_C(P_a,Q_b)=\|C\|_2^2$, so the outcome law has total mass $1$; the average of a function $\varphi$ under the outcome law is $\sum_{a,b}\mathrm{Pr}_C(P_a,Q_b)\,\varphi(a,b)$; for coarse-grainings along $f\colon A\to R$ and $g\colon B\to T$ and any real weights $w$ on $R\times T$,
--   $$\sum_{r\in R}\sum_{t\in T}w(r,t)\,\mathrm{Pr}_C\big(P^f_r,Q^g_t\big)=\sum_{a\in A}\sum_{b\in B}w\big(f(a),g(b)\big)\,\mathrm{Pr}_C(P_a,Q_b);$$
--   and coarse-graining along $a\mapsto(f(a),h(a))$ followed by summation over the second component gives the coarse-graining along $f$.
--
--   The outcome law turns a quantum strategy on fixed questions into an ordinary distribution of answers, so that winning probabilities of repeated strategies can be studied with finite probability theory; the uniform law is used to pick a random coordinate, and the question law connects a game to this framework. The coarse-graining identities convert statements about the answers on a subset of rounds into statements about the full measurement.
--
--   **Formalization Note** The definitions are `Game.questionLaw`, `FiniteProbability.Law.uniform` and `QuantumSampling.outcomeLaw`; the identities are `prob_POVM_total`, `outcomeLaw_avg`, `coarsen_prob_sum` and `POVM.coarsen_slice`. In the game, questions and answers are indexed by `Fin (x+1)`, `Fin (y+1)`, `Fin (a+1)` and `Fin (b+1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Rounding.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Rounding.lean by skeleton subtraction
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

namespace OAI

universe u_R u_m u_n u_A u_B u_T u_U

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

def Game.questionLaw {x y a b : ℕ} (G : Game x y a b) : Law (Fin (x+1)×Fin (y+1)) :=
  ⟨G.questionProb, G.questionProb_nonneg, G.questionProb_sum⟩

namespace QuantumSampling
end QuantumSampling
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {R : Type u_R} [Fintype R] [Nonempty R]
def uniform : Law R where
  weight _ := 1/(Fintype.card R : ℝ)
  nonneg _ := by positivity
  total := by simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
namespace ThresholdParallelRepetition
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))

include hμ
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law OperatorEntropy
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} {T : Type u_T} {U : Type u_U} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [Fintype B] [Fintype R] [Fintype T] [Fintype U]

lemma coarsen_prob_sum (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (f : A → R) (g : B → T) (w : R → T → ℝ) :
    (∑ r, ∑ t, w r t * prob C ((P.coarsen f).effect r) ((Q.coarsen g).effect t)) =
      ∑ a, ∑ b, w (f a) (g b) * prob C (P.effect a) (Q.effect b) := by
  classical
  have hR (r : R) : (∑ t, w r t * prob C ((P.coarsen f).effect r) ((Q.coarsen g).effect t)) =
      ∑ b, w r (g b)*prob C ((P.coarsen f).effect r) (Q.effect b) :=
    Q.coarsen_sum g (fun t => w r t • probRight C ((P.coarsen f).effect r))
  simp only [hR]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, ∑ a, w (f a) (g b)*prob C (P.effect a) (Q.effect b) := by
      apply Finset.sum_congr rfl; intro b _
      exact P.coarsen_sum f (fun r => w r (g b) • probLeft C (Q.effect b))
    _ = _ := Finset.sum_comm

lemma POVM.coarsen_slice (P : POVM m A) (f : A → R) (g : A → T) (r : R) :
    (∑ t, (P.coarsen (fun a => (f a,g a))).effect (r,t)) = (P.coarsen f).effect r := by
  classical
  simp only [POVM.coarsen, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp only [Prod.mk.injEq]
  by_cases hr : f a = r
  · simp [hr]
  · simp [hr]

lemma prob_POVM_total (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) :
    (∑ a, ∑ b, prob C (P.effect a) (Q.effect b)) = hsSq C := by
  simp only [← prob_sum_right, ← prob_sum_left, P.total, Q.total, prob_one]

def outcomeLaw (C : Matrix m n ℂ) (hC : hsSq C = 1) (P : POVM m A) (Q : POVM n B) : Law (A×B) where
  weight z := prob C (P.effect z.1) (Q.effect z.2)
  nonneg z := prob_nonneg (P.pos z.1) (Q.pos z.2)
  total := by rw [Fintype.sum_prod_type, prob_POVM_total, hC]

lemma outcomeLaw_avg (C : Matrix m n ℂ) (hC : hsSq C = 1) (P : POVM m A) (Q : POVM n B) (f : A×B → ℝ) :
    (outcomeLaw C hC P Q).avg f = ∑ a, ∑ b, prob C (P.effect a) (Q.effect b)*f (a,b) := by
  simp only [avg, outcomeLaw, smul_eq_mul, Fintype.sum_prod_type]
end ThresholdParallelRepetition.QuantumSampling

end

end OAI


