-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_Thm525For
-- name    : QuantumKtSoI_Supplement_Thm525For
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:33:49.397987+00:00
-- url     : https://prove2.me/theorems/19acfe25-a93b-488d-b52b-882bb918f048
-- title:
--   The statement of Theorem 5.25 for a conditional measure $\mu$
-- statement:
--   For a real-valued conditional measure $\mu$, reals $0<\alpha<\beta<1$, an integer $c_A\ge1$ and $\eta>0$, the **excluded separator** is a machine $A$ with an integer $n_A$ such that for every pair of strings $x,w$ with $|x|\ge n_A$: $A$ halts on $\langle x,w\rangle$ within
--   $$2^{\eta|x|}(|x|+|w|+2)^{c_A}$$
--   steps, accepts with probability at least $2/3$ if $\mu(x|w)\ge\beta|x|$, and rejects with probability at least $2/3$ if $\mu(x|w)\le\alpha|x|$. Theorem 5.25 for $\mu$ says: for all $0<\alpha<\beta<1$ and $c_A\ge1$ there is $\eta>0$ for which no such separator exists.
--
--   Theorems D.40 and F.3 assert this for measures other than $\mathrm{qKt}$.
--
--   **Formalization Note** Accepting is outputting the string $1$ and rejecting is outputting any other string; since $A$ has halted on every branch by the deadline, rejecting with probability at least $2/3$ is accepting with probability at most $1/3$. The real deadline is a floor.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 5.25, p.75

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- The separator excluded by **Theorem 5.25** (p.75 of Myrisiotis, STOC 2027 submission, held
version sha256 6616571c…), for a conditional measure `µ` (`µ x w` is `µ(x | w)`): there is no machine
`A` with an integer `n_A` such that for every pair of strings `x, w` with `|x| ≥ n_A`, `A` halts on
`⟨x, w⟩` within `2^{η|x|}(|x|+|w|+2)^{c_A}` steps on every branch, accepts (outputs the string `1`)
with probability at least `2/3` if `µ(x|w) ≥ β|x|`, and rejects (outputs any other string) with
probability at least `2/3` if `µ(x|w) ≤ α|x|`.

**Formalization Note** The real deadline is read as `⌊·⌋` (p.22). Since `A` halts on every branch by
the deadline, its output probabilities there sum to one (Lemma 3.3(ii)), so rejecting with
probability at least `2/3` is accepting with probability at most `1/3`. -/
def NoSep (μ : List Bool → List Bool → ℝ) (α β : ℝ) (cA : ℕ) (η : ℝ) : Prop :=
  ¬∃ A : CodedMachine, A.Valid ∧ ∃ nA : ℕ, ∀ x w : List Bool, nA ≤ x.length →
    A.toMachine.HaltsWithin (pair x w)
        ⌊(2 : ℝ) ^ (η * x.length) * ((x.length : ℝ) + w.length + 2) ^ cA⌋₊ ∧
      (β * x.length ≤ μ x w → (2 / 3 : ℝ) ≤ A.toMachine.outputProb (pair x w)
        ⌊(2 : ℝ) ^ (η * x.length) * ((x.length : ℝ) + w.length + 2) ^ cA⌋₊ [true]) ∧
      (μ x w ≤ α * x.length → A.toMachine.outputProb (pair x w)
        ⌊(2 : ℝ) ^ (η * x.length) * ((x.length : ℝ) + w.length + 2) ^ cA⌋₊ [true] ≤ 1 / 3)

/-- **Theorem 5.25** for `µ` (p.75): for all reals `0 < α < β < 1` and every integer `c_A ≥ 1` there
is `η > 0` with `NoSep µ α β c_A η`. -/
def Thm525For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ α β : ℝ, 0 < α → α < β → β < 1 → ∀ cA : ℕ, 1 ≤ cA → ∃ η : ℝ, 0 < η ∧ NoSep μ α β cA η

end QuantumKtSoI.Supplement


