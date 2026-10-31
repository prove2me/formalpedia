-- Prove2me | Definitions.Def_MalleableSched_Model
-- name    : MalleableSched_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:16.199616+00:00
-- url     : https://prove2.me/theorems/27b85195-9e82-494a-8366-80c9ffd79333
-- title:
--   Malleable jobs: processing times $f_j=1/g_j$, fractional subadditivity, assignments, maximum load $L(\mathbf S)$, well-structured assignments
-- statement:
--   A set $J$ of jobs is to be processed on a set $M$ of machines. A **malleable** job may run on any set of machines at once. Job $j$ has a **speed function** $g_j:2^M\to\mathbb R_{\ge0}$; on the machine set $S$ it needs the **processing time**
--   $$
--   f_j(S)=\frac{1}{g_j(S)},\qquad f_j(S)=\infty \text{ when } g_j(S)=0 \ (\text{in particular } f_j(\emptyset)=\infty).
--   $$
--
--   1. A function $g:2^M\to\mathbb R_{\ge0}$ is **fractionally subadditive** (XOS) if $g(T)\le\sum_{S\subseteq T}\alpha(S)\,g(S)$ for every $T\subseteq M$ and every $\alpha:2^M\to[0,1]$ with $\sum_{S\subseteq T:\,i\in S}\alpha(S)\ge1$ for all $i\in T$. Monotonicity is not assumed.
--   2. An **assignment** $\mathbf S=(S_j)_{j\in J}$ gives every job $j$ a non-empty machine set $S_j\subseteq M$.
--   3. Its **maximum load** is
--   $$
--   L(\mathbf S)=\max_{i\in M}\sum_{j\in J:\,i\in S_j} f_j(S_j).
--   $$
--   4. $\mathbf S$ is **well-structured** if every machine $i$ lies in $S_j$ with $|S_j|>1$ for at most one job $j$: every machine shares at most one job with other machines.
--
--   These are the objects of Theorem 1: a well-structured assignment can be scheduled with makespan equal to its maximum load, so Theorem 1 bounds the gap between assigning and scheduling malleable jobs.
--
--   **Formalization Note** Jobs are `Fin n` and machines `Fin m`. Speeds are real numbers; nonnegativity is a hypothesis of each theorem. Processing times and loads live in $[0,\infty]$ (`ℝ≥0∞`), where $1/0=\infty$; the maximum over machines is a supremum (it is $0$ when there are no machines). In the definition of fractional subadditivity, $\alpha$ is a real function on all subsets with values in $[0,1]$.
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, §1.1 p.2 (assignment, L(S)), §1.2 pp.3–4 (gⱼ = 1/fⱼ, fractional subadditivity), §2 p.7 (well-structured)

import Mathlib

open scoped ENNReal

namespace MalleableSched

/-- **Processing time `f_j(S) = 1 / g_j(S)` of a malleable job.**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs under
Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, §1.1, p.2 and §1.2, p.3:
"we define gj(S) := 1/fj(S) for every j ∈ J and S ⊆ M (as jobs have to be allocated to non-empty
machine set, we assume w.l.o.g. that fj(∅) = ∞ and gj(∅) = 0 for all j ∈ J)".

Job `j` processed on the machine set `S` takes time `1 / g j S`, where `g j S ≥ 0` is its joint
processing speed on `S`.

**Formalization Note.** Jobs are `Fin n` and machines `Fin m` (any finite sets, 0-based).
Speeds are real numbers `g j S` (nonnegativity is a separate hypothesis wherever it is used).
The time is computed in `ℝ≥0∞` as `(ENNReal.ofReal (g j S))⁻¹`, so speed `0` gives time `∞`
(the paper's `fⱼ(∅) = ∞`), never the real-number convention `0⁻¹ = 0`. -/
noncomputable def procTime {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ) (j : Fin n)
    (S : Finset (Fin m)) : ℝ≥0∞ :=
  (ENNReal.ofReal (g j S))⁻¹

/-- **Fractionally subadditive (XOS) set function.**
arXiv:2111.06225v2, §1.2, p.4: "A function g : 2^M → R≥0 is fractionally subadditive (also known
as XOS in the literature), if g(T) ≤ Σ_{S⊆T} α(S)g(S) for all T ⊆ M and for all α : 2^M → [0, 1]
that fulfill Σ_{S⊆T : i∈S} α(S) ≥ 1 for all i ∈ T."

**Formalization Note.** The ground set `M` is `Fin m`; subsets are `Finset (Fin m)`; `α` is any
real function on subsets with values in `[0, 1]` (its values on sets not contained in `T` do not
enter). Nonnegativity of `h` is not part of this definition; it is a separate hypothesis
(`0 ≤ g j S`) of every statement that uses speeds. Monotonicity is not assumed (p.4). -/
def FractionallySubadditive {m : ℕ} (h : Finset (Fin m) → ℝ) : Prop :=
  ∀ (T : Finset (Fin m)) (α : Finset (Fin m) → ℝ),
    (∀ S, 0 ≤ α S ∧ α S ≤ 1) →
    (∀ i ∈ T, 1 ≤ ∑ S ∈ T.powerset.filter (fun S => i ∈ S), α S) →
    h T ≤ ∑ S ∈ T.powerset, α S * h S

/-- **Assignment.** arXiv:2111.06225v2, §1.1, p.2: "A schedule consists of an assignment
S = (Sj)j∈J that specifies a non-empty set of machines Sj ⊆ M for each job j ∈ J".

**Formalization Note.** An assignment is a map `S : Fin n → Finset (Fin m)` with every `S j`
non-empty. -/
def IsAssignment {n m : ℕ} (S : Fin n → Finset (Fin m)) : Prop :=
  ∀ j, (S j).Nonempty

/-- **Maximum load `L(S)` of an assignment.** arXiv:2111.06225v2, §1.1, p.2: "the maximum load
L(S) := max_{i∈M} Σ_{j∈J : i∈Sj} fj(Sj) over all machines."

**Formalization Note.** The load of machine `i` is the sum of the processing times `f_j(S_j)` of
the jobs `j` with `i ∈ S_j`; `L(S)` is its maximum over machines, written `⨆ i` in `ℝ≥0∞` (a
finite maximum; it is `0` when there are no machines). Loads can be `∞` (a job on a set of speed
`0`). -/
noncomputable def maxLoad {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ)
    (S : Fin n → Finset (Fin m)) : ℝ≥0∞ :=
  ⨆ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), procTime g j (S j)

/-- **Well-structured assignment.** arXiv:2111.06225v2, §2, p.7: "We say an assignment S is
well-structured if for every i ∈ M there is at most one j ∈ J with i ∈ Sj and |Sj| > 1, i.e.,
every machine shares at most one job with other machines."

**Formalization Note.** "At most one `j`" is stated as: any two jobs `j, j'` that both contain
`i` in a machine set of size `> 1` are equal. Jobs on a single machine are unrestricted. -/
def WellStructured {n m : ℕ} (S : Fin n → Finset (Fin m)) : Prop :=
  ∀ (i : Fin m) (j j' : Fin n), i ∈ S j → 1 < (S j).card → i ∈ S j' → 1 < (S j').card → j = j'

end MalleableSched


