-- Prove2me | Definitions.Def_GeneralizedSortingFourCycles_Sorting_MachineModel
-- name    : GeneralizedSortingFourCycles_Sorting_MachineModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:07.844397+00:00
-- url     : https://prove2.me/theorems/63e70ce4-a159-4b48-91e4-274713a9150e
-- title:
--   Finite-bit comparison execution and sorting output
-- statement:
--   A public comparison graph $G$ has vertex set $\{0,\ldots,n-1\}$. Its input word consists of a self-delimiting unary size followed by its adjacency matrix. A request contains two self-delimiting unary vertex labels. Only words encoding graph darts are legal. For an edge $(u,v)$, the comparison oracle returns whether $u$ precedes $v$ in the hidden permutation $\pi$.
--
--   The reusable finite Turing-machine model has a fixed transition table and sequential bit tapes. All ordinary transitions and oracle transitions count toward time. Each issued comparison is counted, including repeats. An input supplies the public graph and independent fair random bits; the auxiliary and guess tapes are empty. The expected sorting output consists of the increasing list of vertices followed by a matrix containing every edge direction, with zero entries at nonedges.
--
--   For an event on $T$ fair bits, its probability is its number of satisfying bit vectors divided by $2^T$. The query scale is
--   $$n^{4/3}(\ln n)^{4/3}.$$
--   These definitions provide an operational interface; they assert no algorithm's existence, correctness, or efficiency.
-- source:
--   Soheil Behnezhad, Shane Ferrante, STOC 2027 submission #1354 (October 2026), §1, printed p. 1 (PDF p. 2); §3, printed p. 5 (PDF p. 6); Theorem 1 and Lemma 9, printed pp. 1, 15 (PDF pp. 2, 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1354.pdf

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_GenSort_Promise
import Definitions.Def_GenSort_answers

namespace GeneralizedSortingFourCycles.Sorting

/-- A self-delimiting unary natural. This is an encoding, not a machine instruction. -/
def natWord (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- A comparison request contains precisely two vertex labels. -/
def pairWord (u v : ℕ) : List Bool := natWord u ++ natWord v

/-- Public input: unary size and the row-major adjacency matrix. The hidden order is absent. -/
noncomputable def graphWord {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact natWord n ++ (List.ofFn fun u : Fin n =>
    List.ofFn fun v : Fin n => decide (G.Adj u v)).flatten

/-- The only accepted requests are encodings of allowed directed edges. -/
def AllowedWord {n : ℕ} (G : SimpleGraph (Fin n)) (w : List Bool) : Prop :=
  ∃ d : G.Dart, w = pairWord d.fst.val d.snd.val

/-- An oracle answers only encoded graph darts. Other strings are outside the oracle;
the theorem separately prohibits issuing them, on every run. -/
def comparisonOracle {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) : Set (List Bool) :=
  {w | ∃ d : G.Dart, w = pairWord d.fst.val d.snd.val ∧ GenSort.answers π d = true}

/-- The output contains the increasing list AND the directions of all edges (row-major;
nonedges have a fixed zero entry). Unary labels make the list self-delimiting. -/
noncomputable def sortingWord {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) : List Bool := by
  classical
  exact (List.ofFn fun i : Fin n => natWord (π i).val).flatten ++
    (List.ofFn fun u : Fin n => List.ofFn fun v : Fin n =>
      decide (G.Adj u v ∧ π.symm u < π.symm v)).flatten

/-- Input and randomness tapes only: no auxiliary advice or nondeterministic guess. -/
noncomputable def sortingInputs {n : ℕ} (G : SimpleGraph (Fin n))
    {T : ℕ} (ω : Fin T → Bool) : NKtLB.Inputs :=
  ⟨graphWord G, [], [], List.ofFn ω⟩

/-- Count actual comparison instructions before time T, including repeated comparisons.
An oracle instruction is one transition; preparing its string uses ordinary bit transitions. -/
noncomputable def comparisonCount (M : NKtLB.Machine) (O : Set (List Bool))
    (inp : NKtLB.Inputs) (T : ℕ) : ℕ := by
  classical
  exact ((Finset.range T).filter fun t =>
    (M.run O inp t).state = M.query ∧ (M.run O inp t).state ≠ M.halt).card

/-- Every issued request is an actual allowed comparison. This includes failed runs. -/
def LegalRun {n : ℕ} (M : NKtLB.Machine) (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (inp : NKtLB.Inputs) (T : ℕ) : Prop :=
  ∀ t < T, (M.run (comparisonOracle G π) inp t).state = M.query →
    (M.run (comparisonOracle G π) inp t).state ≠ M.halt →
    AllowedWord G (M.run (comparisonOracle G π) inp t).queryString

/-- Exact probability over T independent fair bits. The finite denominator is positive,
including T=0. Predicates need no measurability assumption on a finite sample space. -/
noncomputable def fairProbability (T : ℕ) (event : (Fin T → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / (2 : ℝ) ^ T

/-- The natural logarithm and both real four-thirds powers from Theorem 1. -/
noncomputable def queryScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (4 / 3 : ℝ) * (Real.log (n : ℝ)) ^ (4 / 3 : ℝ)

end GeneralizedSortingFourCycles.Sorting


