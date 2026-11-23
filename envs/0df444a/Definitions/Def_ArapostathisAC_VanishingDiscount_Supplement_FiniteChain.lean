-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_FiniteChain
-- name    : ArapostathisAC_VanishingDiscount_Supplement_FiniteChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:01:50.613157+00:00
-- url     : https://prove2.me/theorems/6e7d91ef-f4a4-477c-ad3a-ef4aaf7cee06
-- title:
--   Finite chains: reachability, communicating and closed classes, unichain; the matrices $P(f)$ and cost vectors $c(f)$ of stationary policies on a finite state space
-- statement:
--   For a square matrix $P$ indexed by a finite set, $j$ is **reachable** from $i$ if $P^m(i,j)>0$ for some $m\ge0$; $i$ and $j$ **communicate** if each is reachable from the other; $i$ is **essential** (recurrent) if every state reachable from $i$ leads back to $i$, i.e. its communicating class is closed, and **transient** otherwise. The number of **closed communicating classes** counts the distinct classes of essential states, and $P$ is **unichain** if there is exactly one.
--
--   On a Borel controlled Markov process with finite state space $S$:
--
--   1. for $f\in\Pi_{SD}$, $P(f)(i,j)=P(j\mid i,f(i))$ and $c(f)=(c(i,f(i)))_{i\in S}$;
--   2. for $f\in\Pi_{SR}$, $P(f)(i,j)=\int P(j\mid i,a)\,f(i)(da)$;
--   3. for a randomized decision rule $f:S\to\mathcal P(A)$, $c(f)=\big(\int c(i,a)\,f(i)(da)\big)_{i\in S}\in[0,\infty]^S$, and $\Pi_{SR}$ is identified with the rules $f$ with $f(i)(U(i))=1$, a subset of $\prod_{i\in S}\mathcal P(A)$ with the product of weak topologies.
--
--   **Formalization Note** The Cesàro limit $P^*$ and the matrix inverse come from the published `BlackwellDiscreteDP.NearOne.LimitMatrix`; the theorems that use them also assert that the limit exists and that $I-P+P^*$ is invertible.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 293–294, §4.1 (P(f), c(f), P*(f), communicating classes); p. 298, §4.2 and Theorem 4.5 (Π_SR, c(·) on Π_SR, unichain)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

open ArapostathisAC.CanonicalTriplet

section Chain

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- State `j` is reachable from state `i` in the finite chain `P`: `P^m(i, j) > 0` for some
`m ≥ 0` (with `P⁰ = I`). -/
def Reaches (P : Matrix n n ℝ) (i j : n) : Prop :=
  ∃ m : ℕ, 0 < (P ^ m) i j

/-- States `i` and `j` communicate in `P`: each is reachable from the other. The communicating
classes of `P` are the classes of this equivalence relation. -/
def Communicates (P : Matrix n n ℝ) (i j : n) : Prop :=
  Reaches P i j ∧ Reaches P j i

/-- State `i` is essential (recurrent) in the finite chain `P`: every state reachable from `i`
leads back to `i`, i.e. the communicating class of `i` is closed. A state that is not essential is
transient. -/
def IsEssential (P : Matrix n n ℝ) (i : n) : Prop :=
  ∀ j, Reaches P i j → Reaches P j i

/-- The number of closed communicating (recurrent, ergodic) classes of the finite chain `P`: the
number of distinct classes `{j : i ↔ j}` of essential states `i`. -/
noncomputable def numClosedClasses (P : Matrix n n ℝ) : ℕ := by
  classical
  exact ((Finset.univ.filter (IsEssential P)).image
    (fun i => Finset.univ.filter (Communicates P i))).card

/-- The finite chain `P` is unichain: it has exactly one closed communicating class (plus,
possibly, transient states). -/
def IsUnichain (P : Matrix n n ℝ) : Prop :=
  numClosedClasses P = 1

end Chain

variable {S A : Type*} [Fintype S] [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The transition matrix `P(f)` of `f ∈ Π_SD` on a finite state space (p. 294):
`P(f)(i, j) = P(j | i, f(i))`. -/
noncomputable def sdMatrix (M : BorelCMP S A) (f : StationaryPolicy M) : Matrix S S ℝ :=
  Matrix.of fun i j => (M.P (i, f.1 i) {j}).toReal

/-- The cost vector `c(f) = (c(i, f(i)))_{i ∈ S}` of `f ∈ Π_SD` (p. 294). -/
def sdCost (M : BorelCMP S A) (f : StationaryPolicy M) : S → ℝ :=
  fun i => M.c (i, f.1 i)

/-- The transition matrix of `f ∈ Π_SR` on a finite state space:
`P(f)(i, j) = ∫ P(j | i, a) f(i)(da)`. -/
noncomputable def srMatrix (M : BorelCMP S A) (f : RandStationaryPolicy M) : Matrix S S ℝ :=
  Matrix.of fun i j => ∫ a, (M.P (i, a) {j}).toReal ∂(f.rule i)

/-- The cost vector `c(f) = (∫ c(i, a) f(i)(da))_{i ∈ S}` of a randomized decision rule
`f : S → 𝒫(A)` (§4.2, p. 298), in `[0, ∞]`. -/
noncomputable def srCost (M : BorelCMP S A) (f : S → ProbabilityMeasure A) : S → ℝ≥0∞ :=
  fun i => ∫⁻ a, ENNReal.ofReal (M.c (i, a)) ∂(f i : Measure A)

/-- The randomized decision rules `f : S → 𝒫(A)` with `f(i)(U(i)) = 1`, i.e. `Π_SR` on a finite
state space, as a subset of the product `∏_{i ∈ S} 𝒫(A)` (product of weak topologies). -/
def srRules (M : BorelCMP S A) : Set (S → ProbabilityMeasure A) :=
  {f | ∀ i, (f i : Measure A) (M.U i)ᶜ = 0}

end ArapostathisAC.VanishingDiscount.Supplement


