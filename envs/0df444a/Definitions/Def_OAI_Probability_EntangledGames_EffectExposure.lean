-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
-- name    : OAI_Probability_EntangledGames_EffectExposure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:12:22.101708+00:00
-- url     : https://prove2.me/theorems/032ea6b5-70ac-4978-ad53-c0ae8d940826
-- title:
--   Coarse-grained POVMs and common square-root factors of a family of effects
-- statement:
--   This file introduces the coarse-graining of a quantum measurement and a way to factor every member $T$ of a family of positive semidefinite matrices as $T=W_T^*W_T$ with all factors in one common space, together with three positivity facts.
--
--   Throughout, $n$, $A$, $B$ and $J$ are finite index sets, matrices have complex entries, $M^*$ is the conjugate transpose and $\mathbf 1$ the identity matrix. A POVM on $\mathbb{C}^n$ with outcomes in $A$ is a family $P=(P_a)_{a\in A}$ of positive semidefinite $n\times n$ matrices with $\sum_{a\in A}P_a=\mathbf 1$.
--
--   1. **Coarse-graining.** For a POVM $P$ with outcomes in $A$ and a map $f\colon A\to B$, the coarse-grained POVM $P^f$ has outcomes in $B$ and effects
--   $$P^f_b=\sum_{a\in A:\ f(a)=b}P_a\qquad(b\in B).$$
--   It corresponds to measuring $P$ and reporting only $f(a)$. The file shows that $P^f$ is a POVM and that $\sum_{b\in B}g_b(P^f_b)=\sum_{a\in A}g_{f(a)}(P_a)$ for every family $(g_b)_{b\in B}$ of real-linear functionals on $n\times n$ matrices.
--   2. **Effect index.** Let $(A_j)_{j\in J}$ be a family of $n\times n$ matrices indexed by a nonempty set $J$. For a matrix $T$, $\operatorname{idx}(T)\in J$ is an index with $A_{\operatorname{idx}(T)}=T$ (chosen by the axiom of choice) when $T$ belongs to the family, and a fixed arbitrary element of $J$ otherwise.
--   3. **Common square-root factor.** For $s>0$ let $K(s)$ be the $n\times(J\times n)$ block row whose $j$-th block is $A_j(A_j+s\mathbf 1)^{-1}$, and let
--   $$\Gamma=\int_0^\infty K(s)^*K(s)\,ds,$$
--   a positive semidefinite matrix indexed by $J\times n$. For $j\in J$ let $W_j$ be the $(J\times n)\times n$ matrix formed by the columns of $\Gamma^{1/2}$ with index in $\{j\}\times n$, so that $W_j^*W_k$ is the $(j,k)$ block of $\Gamma$; when all $A_j$ are positive semidefinite this block equals $\int_0^\infty\big(A_j(A_j+s\mathbf 1)^{-1}\big)^*A_k(A_k+s\mathbf 1)^{-1}\,ds$. The factor of a matrix $T$ is $W_T=W_{\operatorname{idx}(T)}$. If every $A_j$ is positive semidefinite and $T$ belongs to the family, then
--   $$W_T^*W_T=T.$$
--
--   In addition, the file records three positivity facts: (a) the average $\sum_r\rho(r)M_r$ of positive semidefinite matrices $M_r$ under a probability law $\rho$ is positive semidefinite; (b) every effect of a POVM satisfies $P_a\le\mathbf 1$ in the Loewner order; (c) resampling preserves positivity. For (c), let $\mu$ be a probability law on $X\times Y$ and let $g$ map question profiles $z=(x_i,y_i)_{i\in I}$ to positive semidefinite matrices; if $g$ is averaged over a fresh $x_i$ drawn from the conditional law of $\mu$ given $y_i$ (or over a fresh $y_i$ drawn from the conditional law given $x_i$), successively along any list of coordinates $i$, the result is again positive semidefinite at every profile. Here the conditional law given $y$ is the normalization of $x\mapsto\mu(x,y)$, replaced by the point mass at a default question when $\sum_x\mu(x,y)=0$, and symmetrically for the conditional law given $x$.
--
--   Coarse-graining is the operation that reduces the measurement of all answers of a repeated strategy to the answers on a subset of rounds. The common factors $W_T$ provide square roots of all effects of a family inside the single space $\mathbb{C}^{J\times n}$, so that two effects of the family can be compared through the Hilbert–Schmidt distance of their factors; this is the device used to build intermediate (hybrid) states when a repeated entangled strategy is conditioned on an event.
--
--   **Formalization Note** The definitions are `POVM.coarsen`, `Resolvent.effectIndex` and `Resolvent.commonMap` (equal to `finitePurification A (effectIndex A T)`), with the facts `coarsen_sum`, `effectIndex_eq`, `commonMap_gram`, `avg_posSemidef`, `lefts_posSemidef`, `rights_posSemidef` and `POVM.le_one`. The integral is a Bochner integral over $(0,\infty)$ and the matrix inverse is Mathlib's (zero on singular matrices); for positive semidefinite $A_j$ and $s>0$ the matrices $A_j+s\mathbf 1$ are invertible and the integral converges. A private copy of the lemma `dite_eq_left` is included for compatibility with the Lean version.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/EffectExposure.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/EffectExposure.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_R u_n u_X u_Y u_I u_A u_B u_m u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability

namespace FiniteProbability.Law
variable {R : Type u_R} {n : Type u_n} [Fintype R] [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n] in
lemma avg_posSemidef (p : Law R) (A : R → Matrix n n ℂ) (hA : ∀ r, (A r).PosSemidef) :
    (p.avg A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r _
  exact (hA r).smul (p.nonneg r)
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq I]
omit [DecidableEq Y] [Fintype n] [DecidableEq n] in
lemma lefts_posSemidef (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) (hf : ∀ z, (f z).PosSemidef) :
    ∀ z, (μ.lefts x₀ l f z).PosSemidef := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_posSemidef _ _ (fun _ => ih _)
omit [DecidableEq X] [Fintype n] [DecidableEq n] in
lemma rights_posSemidef (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) (hf : ∀ z, (f z).PosSemidef) :
    ∀ z, (μ.rights y₀ l f z).PosSemidef := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_posSemidef _ _ (fun _ => ih _)
end FiniteProbability.Law

namespace QuantumSampling.POVM
variable {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} [Fintype n] [DecidableEq n] [Fintype A] [Fintype B] [Fintype R]
lemma le_one (P : POVM n A) (a : A) : P.effect a ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun b _ => (P.pos b).nonneg) (Finset.mem_univ a)

def coarsen (P : POVM n A) (f : A → B) : POVM n B := by
  classical
  exact {
    effect b := ∑ a with f a=b, P.effect a
    pos b := Matrix.posSemidef_sum _ (fun a _ => P.pos a)
    total := by simp only [Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a)), P.total] }

lemma coarsen_sum (P : POVM n A) (f : A → B) (g : B → Matrix n n ℂ →ₗ[ℝ] ℝ) :
    (∑ b, g b ((P.coarsen f).effect b)) = ∑ a, g (f a) (P.effect a) := by
  classical
  simp only [coarsen, map_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end QuantumSampling.POVM

namespace OperatorEntropy
variable {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end OperatorEntropy

namespace Resolvent
variable {J : Type u_J} {n : Type u_n} [Fintype J] [Nonempty J] [DecidableEq J] [Fintype n] [DecidableEq n]

def effectIndex (A : J → Matrix n n ℂ) (T : Matrix n n ℂ) : J :=
  if h : T ∈ Set.range A then Classical.choose h else Classical.choice inferInstance

def commonMap (A : J → Matrix n n ℂ) (T : Matrix n n ℂ) : Matrix (J×n) n ℂ :=
  finitePurification A (effectIndex A T)

omit [DecidableEq J] [DecidableEq n] in
lemma effectIndex_eq (A : J → Matrix n n ℂ) {T : Matrix n n ℂ} (hT : T ∈ Set.range A) :
    A (effectIndex A T) = T := by
  simp only [effectIndex, dite_eq_left hT]
  exact Classical.choose_spec hT
lemma commonMap_gram (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef)
    {T : Matrix n n ℂ} (hT : T ∈ Set.range A) :
    (commonMap A T)ᴴ*commonMap A T = T := by
  rw [commonMap, finitePurification_self A hA, effectIndex_eq A hT]

variable {m : Type u_m} {K : Type u_K} [Fintype m] [DecidableEq m] [Fintype K] [DecidableEq K]
end Resolvent

end ThresholdParallelRepetition

end

end OAI


