-- Prove2me | Definitions.Def_RevRedSAT_SearchWithin
-- name    : RevRedSAT_SearchWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:56.010207+00:00
-- url     : https://prove2.me/theorems/3b815ede-09c0-40b6-834c-135cc803b3b3
-- title:
--   Search algorithms and Monte Carlo search algorithms within a time bound
-- statement:
--   Let a problem have instances $I$, a finite universe $\{0,\dots,n(I)-1\}$, a set of feasible solutions $\mathrm{valid}(I)$ (subsets of the universe) and admissible input codes $w$ of $I$.
--
--   1. A **correct search output** is either the word $[0]$ ("no"), when no feasible solution exists, or the bit $1$ followed by the code of a duplicate-free list of the elements of a feasible solution, listed in any order. "A decision algorithm determines whether a feasible solution exists. A search algorithm also returns a solution to the original instance" (App. C, p.92).
--   2. A machine $M$ **solves the search problem within $T$** if on every code $w$ of every instance $I$ it halts within $T(I,w)$ steps with a correct search output.
--   3. A machine $M$ is a **Monte Carlo search algorithm within $T$ with success probability $\theta$** if there is a computable rule $\rho$ with $\rho(t)\le t$, fixed with the machine, such that, with $t=T(I,w)$, for every random string $r\in\{0,1\}^{\rho(t)}$ the machine run on $w$ followed by $r$ halts within $t$ steps with an output that is either "no" or a feasible solution (no false positives), and, whenever a feasible solution exists, at least a $\theta$ fraction of the $2^{\rho(t)}$ random strings yield a solution. The number of random bits depends only on the time bound, so the length of the random string carries no information about the instance. "Randomized algorithms have no false positives and return a valid solution on a YES instance with probability at least 2/3" (Table 1, p.8).
--
--   **Formalization Note** Probabilities are counts over the uniformly distributed random strings; the time bound holds on every random string. A deterministic algorithm is the case $\rho=0$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C, p.92 (decision and search algorithms); Table 1 and its notes, p.8 (search, randomized guarantee)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- The code of an element `u` of the universe `{0, …, n − 1}`: its index in self-delimiting binary. -/
def encFin {n : ℕ} (u : Fin n) : List Bool := encNat u.val

/-- The code of a list of elements (a set, when the list has no repetitions). -/
def encSet {n : ℕ} (L : List (Fin n)) : List Bool := encList encFin L

/-- **A correct output of a search algorithm.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C, p.92: "A decision
algorithm determines whether a feasible solution exists. A search algorithm also returns a solution
to the original instance"; Table 1, p.8: "“Search” includes decision and recovery of a verified
original-instance solution".

The output word is `[false]` ("no") and no feasible solution exists, or it is `true` followed by the
code of a duplicate-free list of the elements of a feasible solution, listed in any order. -/
def IsSearchOutput {n : ℕ} (valid : Finset (Fin n) → Prop) (out : List Bool) : Prop :=
  (out = [false] ∧ ¬ ∃ S, valid S) ∨
    ∃ L : List (Fin n), L.Nodup ∧ valid L.toFinset ∧ out = true :: encSet L

/-- **An output without false positives**: `[false]`, or `true` followed by the code of a feasible
solution. On an instance with no feasible solution the only such output is `[false]`. -/
def IsSoundOutput {n : ℕ} (valid : Finset (Fin n) → Prop) (out : List Bool) : Prop :=
  out = [false] ∨ ∃ L : List (Fin n), L.Nodup ∧ valid L.toFinset ∧ out = true :: encSet L

/-- **A deterministic search algorithm within a time bound.** For a problem whose instances `I`
have universe `{0, …, n(I) − 1}`, feasible solutions `valid I`, and codes `IsCode I w`, the machine
`M` solves the search problem within `T`: on every code `w` of every instance `I` it halts within
`T I w` steps with a correct search output (`IsSearchOutput`). Every code of an instance is an
admissible input, so the bound holds for every listing order of the input. -/
def SearchWithin {ι : Type} (M : Turing.TM2ComputableAux Bool Bool) (n : ι → ℕ)
    (IsCode : ι → List Bool → Prop) (valid : (I : ι) → Finset (Fin (n I)) → Prop)
    (T : ι → List Bool → ℕ) : Prop :=
  ∀ I w, IsCode I w → ∃ out, IsSearchOutput (valid I) out ∧ HMBinPacking.OutputsWithin M w out (T I w)

/-- **A Monte Carlo search algorithm within a time bound, with success probability `θ`.**
Table 1, p.8: "Randomized algorithms have no false positives and return a valid solution on a YES
instance with probability at least 2/3"; Theorem 6.12, p.44: "On a yes-instance it returns a hitting
set of size at most k with probability at least 3/4; on a no-instance it always returns no."

There is a computable rule `ρ`, fixed with the machine, giving the number of random bits as a
function of the time bound: on every code `w` of every instance `I`, with `t = T I w`, the machine
reads `ρ(t) ≤ t` random bits; for every random string `r ∈ {0,1}^{ρ(t)}` the machine, run on `w`
followed by `r`, halts within `t` steps with an output without false positives (`IsSoundOutput`);
and if a feasible solution exists, at least a `θ` fraction of the `2^{ρ(t)}` random strings make
it output a solution.

**Formalization Note** Random bits are read from the input after the instance code; the
probability is the uniform measure on `{0,1}^{ρ(t)}`, i.e. a count. The time bound holds on every
random string (worst-case time). A deterministic algorithm is the case `ρ = 0`. The number of
random bits is a computable function of the time bound only (in this mission's bounds, a function
of `k` and `|w|`), so the length of the random string carries no information about the instance
beyond what the machine can read itself; an algorithm using fewer bits ignores the rest. -/
def MonteCarloWithin {ι : Type} (M : Turing.TM2ComputableAux Bool Bool) (n : ι → ℕ)
    (IsCode : ι → List Bool → Prop) (valid : (I : ι) → Finset (Fin (n I)) → Prop)
    (T : ι → List Bool → ℕ) (θ : ℝ) : Prop :=
  ∃ ρ : ℕ → ℕ, Computable ρ ∧ (∀ t, ρ t ≤ t) ∧ ∀ I w, IsCode I w →
    ∃ out : (Fin (ρ (T I w)) → Bool) → List Bool,
      (∀ r, IsSoundOutput (valid I) (out r) ∧
        HMBinPacking.OutputsWithin M (w ++ List.ofFn r) (out r) (T I w)) ∧
      ((∃ S, valid I S) →
        θ * 2 ^ (ρ (T I w)) ≤ ((Finset.univ.filter fun r => out r ≠ [false]).card : ℝ))

end RevRedSAT


