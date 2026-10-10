-- Prove2me | Definitions.Def_FSS23105365_FiniteState
-- name    : FSS23105365_FiniteState
-- status  : Definition
-- author  : @YY
-- created : 2026-10-09T15:40:36.24419+00:00
-- url     : https://prove2.me/theorems/962b711d-7b06-4c91-9cb4-8fcabe4f77d5
-- title:
--   Finite-state laws, dyadicity and sampling predicates
-- statement:
--   Binary DFAs on finite indexed state sets, their accepted word slices, uniform word laws and word–acceptance pair laws; real-valued finite Markov chains with nonnegative entries and probability normalization, complete trajectory laws, coordinatewise one-hot encodings, terminal-event conditional laws, dyadic probabilities, and projected trajectory laws. Path-dyadicity quantifies over all finite trajectories, including length zero. Exact randomized $\mathrm{AC}^0$ sampling is expressed by existential depth and polynomial-size constants preceding the length quantifier. The logarithmic seed scale is $\log_2(1/\epsilon)$. Conditional laws use division by the accepting probability; relevant targets require this probability to be strictly positive.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Section 2; Appendix E.2–E.4, especially Lemma E.3 and Theorem E.6.

import Definitions.Def_FSS23105365_Circuits
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

structure BinaryDFA (q : ℕ) where
  start : Fin q
  step : Fin q → Bool → Fin q
  accepting : Finset (Fin q)

def BinaryDFA.run {q n : ℕ} (A : BinaryDFA q) (x : Bits n) : Fin q :=
  (List.ofFn x).foldl A.step A.start

def BinaryDFA.accepts {q n : ℕ} (A : BinaryDFA q) (x : Bits n) : Bool :=
  decide (A.run x ∈ A.accepting)

def pairEncode {q n : ℕ} (A : BinaryDFA q) (x : Bits n) : Option (Fin n) → Bool
  | none => A.accepts x
  | some i => x i

def pairLaw {q n : ℕ} (A : BinaryDFA q) (z : Bits n × Bool) : ℝ :=
  if z.2 = A.accepts z.1 then 1 / (2 : ℝ) ^ n else 0

def pairOutcomeEncode {n : ℕ} (z : Bits n × Bool) : Option (Fin n) → Bool
  | none => z.2
  | some i => z.1 i

def acceptedWords {q : ℕ} (A : BinaryDFA q) (n : ℕ) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (fun x => A.accepts x = true)

noncomputable def wordLaw {q n : ℕ} (A : BinaryDFA q) (x : Bits n) : ℝ :=
  if A.accepts x = true then 1 / ((acceptedWords A n).card : ℝ) else 0

structure MarkovChain (q : ℕ) where
  initial : Fin q → ℝ
  transition : Fin q → Fin q → ℝ
  initial_nonneg : ∀ x, 0 ≤ initial x
  transition_nonneg : ∀ x y, 0 ≤ transition x y
  initial_sum : ∑ x, initial x = 1
  row_sum : ∀ x, ∑ y, transition x y = 1

abbrev Path (q n : ℕ) := Fin (n + 1) → Fin q

noncomputable def pathLaw {q n : ℕ} (M : MarkovChain q) (γ : Path q n) : ℝ :=
  M.initial (γ ⟨0, Nat.zero_lt_succ n⟩) *
    ∏ i : Fin n, M.transition
      (γ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (γ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def pathEncode {q n : ℕ} (γ : Path q n) : (Fin (n + 1) × Fin q) → Bool :=
  fun z => decide (γ z.1 = z.2)

def Dyadic (x : ℝ) : Prop := ∃ a k : ℕ, x = (a : ℝ) / (2 : ℝ) ^ k

def PathDyadic {q : ℕ} (M : MarkovChain q) : Prop :=
  ∀ n : ℕ, ∀ γ : Path q n, Dyadic (pathLaw M γ)

def TransitionDyadic {q : ℕ} (M : MarkovChain q) : Prop :=
  (∀ x, Dyadic (M.initial x)) ∧ ∀ x y, Dyadic (M.transition x y)

noncomputable def acceptanceProbability {q : ℕ} (M : MarkovChain q)
    (F : Finset (Fin q)) (n : ℕ) : ℝ :=
  ∑ γ : Path q n, if γ ⟨n, Nat.lt_succ_self n⟩ ∈ F then pathLaw M γ else 0

noncomputable def conditionedPathLaw {q n : ℕ} (M : MarkovChain q)
    (F : Finset (Fin q)) (γ : Path q n) : ℝ :=
  if γ ⟨n, Nat.lt_succ_self n⟩ ∈ F then
    pathLaw M γ / acceptanceProbability M F n else 0

noncomputable def logInv (ε : ℝ) : ℝ := Real.log (1 / ε) / Real.log 2

def ExactPathAC0 {q : ℕ} (M : MarkovChain q) : Prop :=
  ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
    S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
    ExactLaw S pathEncode (pathLaw M)

noncomputable def projectedPathLaw {q r n : ℕ} (M : MarkovChain r)
    (φ : Fin r → Fin q) (γ : Path q n) : ℝ := by
  classical
  exact ∑ η : Path r n, if (fun i => φ (η i)) = γ then pathLaw M η else 0

end FSS23105365


